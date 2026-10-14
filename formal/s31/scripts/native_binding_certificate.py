"""Replay structural M31 public conversion and reserved output copies.

This consumes the compiler-exported conversion variable and gate spans. Its
claim is local to the binding phase: earlier source/assertion allocations and
the later committed proof rows are separate correspondence obligations.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PINNED_SOURCES = {
    "src/frontends/s31/language/relation_compiler.zig":
        "bd7c58706a3e5d8fc9ba89b1ede9528c63ff6d985f4e2520c6cac6e2ef1bd9d5",
    "deps/stwo-zig/src/frontends/circuit/builder/simd.zig":
        "4a0f480064056a7c7a87110666fce4d93a3d147d72dd7e6be8de184b75d78220",
    "deps/stwo-zig/src/frontends/circuit/builder/context.zig":
        "efe7f2bd64402ebd3983d025fbaf6301ae2004e6739bf04f753db3d0191142ef",
}

P = 2**31 - 1
I = 1 << 32
U = 1 << 64
IU = 1 << 96
UNIT_KEYS = (1, I, U, IU)
INV5 = pow(5, P - 2, P)


def key_of(a: int, b: int = 0, c: int = 0, d: int = 0) -> int:
    return a | b << 32 | c << 64 | d << 96


# i²=-1 and u²=2+i. Thus i⁻¹=-i, u⁻¹=(2-i)u/5, and
# (iu)⁻¹=(-1-2i)u/5, all with canonical M31 coordinates.
UNIT_INVERSES = {
    1: key_of(0, P - 1),
    2: key_of(0, 0, 2 * INV5 % P, -INV5 % P),
    3: key_of(0, 0, -INV5 % P, -2 * INV5 % P),
}

SPAN_FIELDS = {"name", "word_start", "word_count", "conversion_var_start",
               "conversion_var_end", "conversion_qm31_start", "conversion_qm31_end",
               "conversion_m31_to_u32_start", "conversion_m31_to_u32_end",
               "binding_qm31_start", "binding_qm31_end"}


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError("native public binding: " + reason)


def check_bindings(graph: dict, raw: dict[str, bytes], inputs: list[dict],
                   finalization_start_var: int) -> dict[str, int]:
    """Check each source-owned outputWord and the eight setOutputs copies."""
    for path, wanted in PINNED_SOURCES.items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == wanted,
                "builder source changed; review binding replay: " + path)

    ssa = json.loads(raw["certificate"])["ssa"]
    public_ids = [spec["id"] for spec in ssa["inputs"]
                  if spec["visibility"] == "public"]
    source_ids = [*public_ids, ssa["output"]]
    bindings = graph["bindings"]
    require(len(bindings) == len(source_ids) and bindings,
            "binding/source port count differs")
    public_raw: dict[int, list[int]] = {}
    public_count = sum(len(inputs[id_]["words"]) for id_ in public_ids)
    public_yields = graph["pointwise_mul"][-public_count:] if public_count else []
    offset = 0
    for id_ in public_ids:
        canonical_id = graph["source_map"][id_]["id"]
        width = len(inputs[id_]["words"])
        public_raw[canonical_id] = [gate["out"] for gate in
                                    public_yields[offset:offset + width]]
        offset += width

    constants = dict(zip(graph["constant_keys"],
                         (var["idx"] for var in graph["constant_vars"]), strict=True))
    gate_by_out = {name: {gate["out"]: (index, gate)
                          for index, gate in enumerate(graph[name])}
                   for name in ("mul", "pointwise_mul")}
    previous_position = {"mul": -1, "pointwise_mul": -1}
    previous_var_end = None
    copy_inputs: list[int] = []
    conversion_gates = 0

    for binding, source_id in zip(bindings, source_ids, strict=True):
        require(type(binding) is dict and set(binding) == SPAN_FIELDS,
                "binding span field roster differs")
        start, end = binding["conversion_var_start"], binding["conversion_var_end"]
        require(type(start) is int and type(end) is int and
                11 <= start <= end <= finalization_start_var,
                "binding variable span out of range")
        if previous_var_end is not None:
            require(start == previous_var_end, "binding variable spans are not contiguous")
        previous_var_end = end
        cursor = start
        owned: set[int] = set()
        new_constants: set[int] = set()
        local_gates = 0

        def intern(key: int) -> int:
            nonlocal cursor
            address = constants.get(key)
            require(address is not None and address <= cursor,
                    "conversion constant missing or allocated out of order")
            if address == cursor:
                owned.add(cursor)
                new_constants.add(cursor)
                cursor += 1
            return address

        def gate(op: str, in0: int, in1: int) -> int:
            nonlocal cursor, local_gates
            output = cursor
            expected = {"in0": in0, "in1": in1, "out": output}
            actual = gate_by_out[op].get(output)
            require(actual is not None and actual[1] == expected and
                    actual[0] > previous_position[op],
                    "conversion gate opcode, address or order differs")
            previous_position[op] = actual[0]
            owned.add(output)
            cursor += 1
            local_gates += 1
            return output

        canonical_id = graph["source_map"][source_id]["id"]
        packed = graph["node_wires"][canonical_id]["wires"][0]
        raw_words = public_raw.get(canonical_id)
        width = binding["word_count"]
        require(1 <= width <= 4 and
                (raw_words is None or len(raw_words) == width),
                "binding width differs from source")
        for coord in range(width):
            if raw_words is not None:
                copy_inputs.append(raw_words[coord])
                continue
            unit = intern(UNIT_KEYS[coord])
            isolated = gate("pointwise_mul", packed, unit)
            copy_inputs.append(isolated if coord == 0 else
                               gate("mul", isolated, intern(UNIT_INVERSES[coord])))

        require(cursor == end and owned == set(range(start, end)),
                "conversion variable allocation has an extra or missing address")
        require(binding["conversion_qm31_end"] -
                binding["conversion_qm31_start"] == local_gates,
                "conversion gate span contains extra or missing gates")
        require(all(at not in range(start, end) or at in new_constants
                    for at in constants.values()),
                "conversion span has an unaccounted interned constant")
        conversion_gates += local_gates

    # setOutputs writes the eight already-reserved addresses without new vars.
    require(previous_var_end == finalization_start_var,
            "variable allocated between bindings and finalization")
    require(len(copy_inputs) <= 8, "public word count exceeds reserved outputs")
    expected_copies = [{"in0": source, "in1": 0, "out": 3 + index}
                       for index, source in enumerate(copy_inputs +
                                                       [0] * (8 - len(copy_inputs)))]
    actual_copies = [gate for gate in graph["add"] if 3 <= gate["out"] <= 10]
    require(actual_copies == expected_copies,
            "reserved output copy gate source, address or order differs")
    return {"conversion_gates": conversion_gates, "bound_public_words": len(copy_inputs)}
