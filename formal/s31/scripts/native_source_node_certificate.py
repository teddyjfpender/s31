"""Replay structural M31 canonical node allocation and exact native gates.

The accepted SSA supplies source IDs, operations and values. The checker
derives each new canonical node's operation or justified constant fold,
then replays constant interning, zero-add erasure and fresh gate addresses.
"""

from __future__ import annotations

from bisect import bisect_left
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
PINNED_SOURCES = {
    "src/frontends/s31/language/canonical.zig":
        "42228724c17cf303de876407ef719cad15136ddf97c760d70d47f4d54fe90706",
    "src/frontends/s31/language/relation_compiler.zig":
        "9004eb71f4060fcf2391e721c0e5afd7ad519a43007e951ae29c59e276588d4d",
    "deps/stwo-zig/src/frontends/circuit/builder/simd.zig":
        "4a0f480064056a7c7a87110666fce4d93a3d147d72dd7e6be8de184b75d78220",
    "deps/stwo-zig/src/frontends/circuit/builder/context.zig":
        "efe7f2bd64402ebd3983d025fbaf6301ae2004e6739bf04f753db3d0191142ef",
}
CANONICAL_FIELDS = {"tag", "kind", "length", "lhs", "rhs", "selector",
                    "index", "constant", "rounds", "body", "input_name",
                    "visibility"}
SPAN_FIELDS = {"id", "var_start", "var_end", "qm31_start", "qm31_end",
               "eq_start", "eq_end", "triple_xor_start", "triple_xor_end",
               "m31_to_u32_start", "m31_to_u32_end", "blake_g_start",
               "blake_g_end"}


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError("native source node: " + reason)


def packed_broadcast(value: int) -> int:
    return sum(value << (32 * coordinate) for coordinate in range(4))


def expected_nodes(inputs: list[dict], nodes: list[dict], specs: list[dict]) -> list[dict]:
    """Reconstruct the canonical tag/operands for every first occurrence."""
    source = inputs + nodes
    expected: list[dict] = []
    require(len(specs) == len(inputs), "source input metadata count differs")
    for item, spec in zip(inputs, specs, strict=True):
        require(item["canonical_id"] == len(expected), "input canonical order differs")
        expected.append({"tag": "input", "length": len(item["words"]),
                         "input_name": item["name"],
                         "visibility": spec["visibility"]})
    for item in nodes:
        cid = item["canonical_id"]
        require(type(cid) is int and 0 <= cid <= len(expected),
                "source canonical ID is not an existing or next node")
        if cid < len(expected):
            continue  # CSE or an identity already checked by source derivation.
        op = item["op"]
        left_id = source[item["lhs"]]["canonical_id"]
        left = expected[left_id]
        right_id = (source[item["rhs"]]["canonical_id"]
                    if item["rhs"] is not None else None)
        right = expected[right_id] if right_id is not None else None
        constant = item["constant"]
        folded = ((op == "mul_const" and constant == 0) or
                  (op in ("add_const", "mul_const") and left["tag"] == "constant") or
                  (right is not None and left["tag"] == right["tag"] == "constant"))
        if folded:
            value = item["words"][0]
            require(all(word == value for word in item["words"]),
                    "folded node has nonuniform source value")
            expected.append({"tag": "constant", "length": len(item["words"]),
                             "constant": value})
        else:
            if op in ("add", "mul") and left_id > right_id:
                left_id, right_id = right_id, left_id
            expected.append({"tag": op, "length": len(item["words"]),
                             "lhs": left_id, "rhs": right_id,
                             "constant": constant})
    return expected


def check_source_nodes(graph: dict, raw: dict[str, bytes], inputs: list[dict],
                       nodes: list[dict]) -> dict[str, int]:
    """Check every canonical source node's variable span and primitive gate."""
    for path, wanted in PINNED_SOURCES.items():
        require(hashlib.sha256((ROOT / path).read_bytes()).hexdigest() == wanted,
                "builder source changed; review node replay: " + path)

    expected = expected_nodes(
        inputs, nodes, json.loads(raw["certificate"])["ssa"]["inputs"])
    canonical, spans, wires = (graph[name] for name in
                               ("canonical_nodes", "node_spans", "node_wires"))
    require(len(expected) == len(canonical) == len(spans) == len(wires),
            "canonical source roster differs")
    for cid, (want, actual) in enumerate(zip(expected, canonical, strict=True)):
        require(type(actual) is dict and set(actual) == CANONICAL_FIELDS and
                actual["tag"] == want["tag"] and actual["kind"] == "m31" and
                actual["length"] == want["length"],
                "canonical tag, kind or width differs")
        if want["tag"] == "input":
            require(actual["input_name"] == want["input_name"] and
                    actual["visibility"] == want["visibility"] and
                    all(actual[field] is None for field in
                        ("lhs", "rhs", "selector", "index", "constant",
                         "rounds", "body")),
                    "canonical input metadata differs")
        else:
            require(all(actual.get(field) == want.get(field) for field in
                        ("lhs", "rhs", "constant")) and
                    all(actual[field] is None for field in
                        ("selector", "index", "rounds", "body", "input_name",
                         "visibility")),
                    "canonical operation or fold differs")
        span = spans[cid]
        require(type(span) is dict and set(span) == SPAN_FIELDS and
                span["id"] == cid and
                all(span[start] == span[end] == 0 for start, end in
                    (("triple_xor_start", "triple_xor_end"),
                     ("m31_to_u32_start", "m31_to_u32_end"),
                     ("blake_g_start", "blake_g_end"))),
                "canonical span field roster or excluded gate families differ")

    constants = dict(zip(graph["constant_keys"],
                         (var["idx"] for var in graph["constant_vars"]), strict=True))
    constant_addresses = sorted(constants.values())
    gate_by_out = {op: {gate["out"]: (index, gate)
                         for index, gate in enumerate(graph[op])}
                   for op in ("add", "sub", "pointwise_mul")}
    previous_position = {"add": -1, "sub": -1, "pointwise_mul": -1}
    previous_var_end = spans[len(inputs) - 1]["var_end"] if inputs else 11
    replayed = 0

    for cid in range(len(inputs), len(expected)):
        want, span = expected[cid], spans[cid]
        start, end = span["var_start"], span["var_end"]
        require(type(start) is int and type(end) is int and
                start == previous_var_end and start <= end <= graph["n_vars"],
                "source-node variable spans are not contiguous")
        previous_var_end = end
        cursor = start
        owned: set[int] = set()
        new_constants: set[int] = set()
        local_gates = 0

        def intern(key: int) -> int:
            nonlocal cursor
            address = constants.get(key)
            require(address is not None and address <= cursor,
                    "source broadcast constant missing or allocated out of order")
            if address == cursor:
                owned.add(cursor)
                new_constants.add(cursor)
                cursor += 1
            return address

        def gate(op: str, left: int, right: int) -> int:
            nonlocal cursor, local_gates
            output = cursor
            actual = gate_by_out[op].get(output)
            require(actual is not None and
                    actual[1] == {"in0": left, "in1": right, "out": output} and
                    actual[0] > previous_position[op],
                    "source gate opcode, operand, address or order differs")
            previous_position[op] = actual[0]
            owned.add(output)
            cursor += 1
            local_gates += 1
            return output

        tag = want["tag"]
        if tag == "constant":
            output = intern(packed_broadcast(want["constant"]))
        else:
            left = wires[want["lhs"]]["wires"][0]
            if tag.endswith("_const"):
                right = intern(packed_broadcast(want["constant"]))
            else:
                right = wires[want["rhs"]]["wires"][0]
            if tag in ("add", "add_const"):
                output = right if left == 0 else left if right == 0 else gate("add", left, right)
            elif tag == "sub":
                output = gate("sub", left, right)
            else:
                require(tag in ("mul", "mul_const"), "unsupported source operation")
                output = gate("pointwise_mul", left, right)

        require(wires[cid]["wires"] == [output],
                "canonical node output wire differs")
        require(cursor == end and owned == set(range(start, end)),
                "source-node variable allocation has extra or missing address")
        require(span["qm31_end"] - span["qm31_start"] == local_gates and
                span["eq_start"] == span["eq_end"],
                "source-node gate span has extra or missing gate")
        lo, hi = bisect_left(constant_addresses, start), bisect_left(constant_addresses, end)
        require(set(constant_addresses[lo:hi]) == new_constants,
                "source-node span has an unaccounted interned constant")
        replayed += 1

    next_start = (graph["assertion_spans"][0]["var_start"]
                  if graph["assertion_spans"] else
                  graph["bindings"][0]["conversion_var_start"])
    require(previous_var_end == next_start,
            "variable allocated between source nodes and assertions/bindings")
    return {"canonical_source_nodes": replayed}
