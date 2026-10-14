"""Replay each structural M31 assertion's exact native mask and Eq gates.

This is an assignment-specific check of the exported unpadded graph. The
assertion operands and first-use mask constants are reconstructed from the
accepted source IDs, rather than copied from compiler-provided gate records.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PINNED_SOURCES = {
    "src/frontends/s31/language/relation_compiler.zig":
        "2d69107c2039a57d41cb5486a4a891788190b124df8438c72b5f436119bd2591",
    "deps/stwo-zig/src/frontends/circuit/builder/simd.zig":
        "4a0f480064056a7c7a87110666fce4d93a3d147d72dd7e6be8de184b75d78220",
    "deps/stwo-zig/src/frontends/circuit/builder/context.zig":
        "efe7f2bd64402ebd3983d025fbaf6301ae2004e6739bf04f753db3d0191142ef",
}
SPAN_FIELDS = {"index", "var_start", "var_end", "qm31_start", "qm31_end",
               "eq_start", "eq_end"}


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError("native assertion: " + reason)


def check_assertions(graph: dict, raw: dict[str, bytes], inputs: list[dict],
                     nodes: list[dict]) -> dict[str, int]:
    """Bind the source assertion IDs to exact native wires and mask gates."""
    for path, wanted in PINNED_SOURCES.items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == wanted,
                "builder source changed; review assertion replay: " + path)
    assertions = json.loads(raw["certificate"])["ssa"]["assertions"]
    spans = graph["assertion_spans"]
    require(len(assertions) == len(spans), "assertion span count differs")
    source = inputs + nodes
    constants = dict(zip(graph["constant_keys"],
                         (var["idx"] for var in graph["constant_vars"]), strict=True))
    gate_by_out = {op: {gate["out"]: (index, gate)
                         for index, gate in enumerate(graph[op])}
                   for op in ("sub", "pointwise_mul")}
    previous_position = {"sub": -1, "pointwise_mul": -1}
    previous_var_end = None
    masked_count = 0

    def source_wire(source_id: int) -> int:
        canonical_id = graph["source_map"][source_id]["id"]
        return graph["node_wires"][canonical_id]["wires"][0]

    for index, ((left_id, right_id), span) in enumerate(zip(assertions, spans, strict=True)):
        require(type(span) is dict and set(span) == SPAN_FIELDS and
                span["index"] == index,
                "assertion span fields or order differ")
        start, end = span["var_start"], span["var_end"]
        require(type(start) is int and type(end) is int and
                11 <= start <= end <= graph["n_vars"],
                "assertion variable span out of range")
        if previous_var_end is not None:
            require(start == previous_var_end,
                    "assertion variable spans are not contiguous")
        previous_var_end = end
        cursor = start
        owned: set[int] = set()
        new_constants: set[int] = set()
        width = len(source[left_id]["words"])
        require(1 <= width <= 4 and len(source[right_id]["words"]) == width,
                "assertion source width differs")
        left, right = source_wire(left_id), source_wire(right_id)

        def gate(op: str, in0: int, in1: int) -> int:
            nonlocal cursor
            output = cursor
            expected = {"in0": in0, "in1": in1, "out": output}
            actual = gate_by_out[op].get(output)
            require(actual is not None and actual[1] == expected and
                    actual[0] > previous_position[op],
                    "assertion gate opcode, operand, address or order differs")
            previous_position[op] = actual[0]
            owned.add(output)
            cursor += 1
            return output

        if width == 4:
            expected_eq = {"in0": left, "in1": right}
            expected_qm31 = 0
        else:
            diff = gate("sub", left, right)
            mask_key = sum(1 << (32 * coordinate) for coordinate in range(width))
            mask = constants.get(mask_key)
            require(mask is not None and mask <= cursor,
                    "assertion mask constant missing or allocated out of order")
            if mask == cursor:
                owned.add(cursor)
                new_constants.add(cursor)
                cursor += 1
            masked = gate("pointwise_mul", diff, mask)
            expected_eq = {"in0": masked, "in1": 0}
            expected_qm31 = 2
            masked_count += 1
        require(graph["eq"][span["eq_start"]] == expected_eq and
                span["eq_end"] == span["eq_start"] + 1,
                "assertion Eq gate does not bind source wires")
        require(span["qm31_end"] - span["qm31_start"] == expected_qm31,
                "assertion arithmetic gate span differs")
        require(cursor == end and owned == set(range(start, end)),
                "assertion variable allocation has an extra or missing address")
        require(all(at not in range(start, end) or at in new_constants
                    for at in constants.values()),
                "assertion span has an unaccounted interned constant")

    if spans:
        require(previous_var_end == graph["bindings"][0]["conversion_var_start"],
                "variable allocated between assertions and public bindings")
    return {"assertions": len(spans), "masked_assertions": masked_count}
