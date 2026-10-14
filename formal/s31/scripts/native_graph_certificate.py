"""Independent bounded replay of an exported structural M31 direct-Gate graph.

This checks the concrete Zig-owned addresses, values, gate equations, constant
interning, source-node mapping, assertions, and public binding for one accepted
assignment. It does not authenticate committed prover columns or instantiate
the parametric Lean NativeTrace proof; those are separate correspondence gaps.
"""

from __future__ import annotations

from scripts.native_air_projection import check_padded_rows
from scripts.native_finalization_certificate import check_finalization
from scripts.native_input_certificate import check_input_packing

P = 2**31 - 1
SCHEMA = "s31-structural-m31-exact-native-graph-v2"
FIELDS = {"schema", "n_vars", "values", "add", "sub", "mul", "pointwise_mul",
          "eq", "triple_xor", "m31_to_u32", "blake_g_gate", "permutation_ends",
          "permutation_inputs", "permutation_outputs", "output", "constant_keys",
          "constant_vars", "source_map", "canonical_nodes", "node_wires",
          "node_spans", "assertion_spans", "bindings", "finalization", "padded"}


def require(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError("native graph artifact: " + reason)


def address(value: object, bound: int) -> int:
    require(type(value) is int and 0 <= value < bound, "invalid variable address")
    return value


def cmul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
    return ((a[0] * b[0] - a[1] * b[1]) % P,
            (a[0] * b[1] + a[1] * b[0]) % P)


def qmul(a: list[int], b: list[int]) -> list[int]:
    ac, bd = cmul((a[0], a[1]), (b[0], b[1])), cmul((a[2], a[3]), (b[2], b[3]))
    return [(ac[0] + 2 * bd[0] - bd[1]) % P,
            (ac[1] + bd[0] + 2 * bd[1]) % P,
            (a[0] * b[2] - a[1] * b[3] + a[2] * b[0] - a[3] * b[1]) % P,
            (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0]) % P]


def check_graph(graph: dict, raw: dict[str, bytes], inputs: list[dict],
                nodes: list[dict]) -> dict[str, int]:
    """Replay one compiler-owned graph after the Lean source gate has accepted."""
    import json

    require(type(graph) is dict and set(graph) == FIELDS and graph["schema"] == SCHEMA,
            "schema or field roster differs")
    n = graph["n_vars"]
    values = graph["values"]
    require(type(n) is int and 0 < n <= 262144 and type(values) is list and len(values) == n,
            "variable table exceeds bounded profile")
    for quad in values:
        require(type(quad) is list and len(quad) == 4 and
                all(type(x) is int and 0 <= x < P for x in quad),
                "noncanonical four-coordinate value")
    require(values[0] == [0] * 4 and values[1] == [1, 0, 0, 0],
            "reserved zero/one values differ")

    binary: dict[str, list[dict]] = {}
    gate_total = 0
    producers: set[int] = set()
    for op in ("add", "sub", "mul", "pointwise_mul"):
        gates = graph[op]
        require(type(gates) is list and len(gates) <= 262144,
                f"{op} gate count exceeds bound")
        binary[op] = gates
        gate_total += len(gates)
        for gate in gates:
            require(type(gate) is dict and set(gate) == {"in0", "in1", "out"},
                    f"malformed {op} gate")
            a, b, out = (address(gate[key], n) for key in ("in0", "in1", "out"))
            require(out not in producers, "variable has multiple arithmetic producers")
            producers.add(out)
            if op == "add":
                result = [(x + y) % P for x, y in zip(values[a], values[b], strict=True)]
            elif op == "sub":
                result = [(x - y) % P for x, y in zip(values[a], values[b], strict=True)]
            elif op == "pointwise_mul":
                result = [(x * y) % P for x, y in zip(values[a], values[b], strict=True)]
            else:
                result = qmul(values[a], values[b])
            require(values[out] == result, f"{op} gate equation fails")
    require(gate_total <= 262144, "arithmetic gate total exceeds bound")
    for gate in graph["eq"]:
        require(type(gate) is dict and set(gate) == {"in0", "in1"}, "malformed equality gate")
        left, right = address(gate["in0"], n), address(gate["in1"], n)
        require(values[left] == values[right], "equality gate fails")
    for field in ("triple_xor", "m31_to_u32", "blake_g_gate", "permutation_ends",
                  "permutation_inputs", "permutation_outputs"):
        require(graph[field] == [], f"{field} is outside structural M31 profile")
    require(type(graph["eq"]) is list and len(graph["eq"]) <= 262144,
            "equality gate count exceeds bound")

    keys, constant_vars = graph["constant_keys"], graph["constant_vars"]
    require(type(keys) is list and type(constant_vars) is list and
            len(keys) == len(constant_vars) and len(keys) <= n,
            "constant roster malformed")
    for key, var in zip(keys, constant_vars, strict=True):
        require(type(key) is int and 0 <= key < 2**128 and
                type(var) is dict and set(var) == {"idx"}, "constant key malformed")
        at = address(var["idx"], n)
        require(key == sum(value << (32 * i) for i, value in enumerate(values[at])),
                "constant key differs from native variable")
    require(len(set(keys)) == len(keys), "duplicate interned constant")

    source = inputs + nodes
    source_map, wires, canonical = graph["source_map"], graph["node_wires"], graph["canonical_nodes"]
    require(type(source_map) is list and len(source_map) == len(source) and
            type(canonical) is list and type(wires) is list and
            len(canonical) == len(wires) <= len(source), "source map size differs")
    for id_, item in enumerate(source):
        entry = source_map[id_]
        require(type(entry) is dict and set(entry) == {"name", "id"} and
                entry["name"] == item["name"] and entry["id"] == item["canonical_id"],
                "source to canonical map differs")
        cid = entry["id"]
        require(type(cid) is int and 0 <= cid < len(wires) and
                type(wires[cid]) is dict and wires[cid]["id"] == cid and
                type(wires[cid]["wires"]) is list and len(wires[cid]["wires"]) == 1,
                "canonical packed address malformed")
        addr = address(wires[cid]["wires"][0], n)
        require(values[addr][:len(item["words"])] == item["words"],
                "source-derived node value differs")
        if id_ < len(inputs):
            require(canonical[cid]["tag"] == "input" and
                    canonical[cid]["input_name"] == item["name"],
                    "input canonical node differs")

    for id_, entry in enumerate(wires):
        require(entry["id"] == id_ and len(entry["wires"]) == 1,
                "canonical wire roster differs")
        address(entry["wires"][0], n)

    def source_wire(id_: int) -> int:
        return wires[source_map[id_]["id"]]["wires"][0]

    # A source step may map to an existing canonical node (CSE), alias an
    # operand (identity), or fold to a constant. Every remaining step must
    # name a concrete primitive gate with the exact native addresses.
    for node in nodes:
        op = node["op"]
        out, left = source_wire(node["id"]), source_wire(node["lhs"])
        canonical_node = canonical[source_map[node["id"]]["id"]]
        if canonical_node["tag"] == "constant":
            require(values[out] == [canonical_node["constant"]] * 4,
                    "folded constant value differs")
            continue
        if op in ("add_const", "mul_const"):
            constant = node["constant"]
            if out == left and ((op == "add_const" and constant == 0) or
                                (op == "mul_const" and constant == 1)):
                continue
            right_value = [constant] * 4
            right_address = None
        else:
            right_address = source_wire(node["rhs"])
            right_value = values[right_address]
            left_zero = canonical[source_map[node["lhs"]]["id"]]["tag"] == "constant" and values[left] == [0] * 4
            right_zero = canonical[source_map[node["rhs"]]["id"]]["tag"] == "constant" and right_value == [0] * 4
            if (op == "add" and ((out == right_address and left_zero) or
                                  (out == left and right_zero))):
                continue
        native_op = {"add": "add", "sub": "sub", "mul": "pointwise_mul",
                     "add_const": "add", "mul_const": "pointwise_mul"}[op]
        found = False
        for gate in binary[native_op]:
            if gate["out"] != out:
                continue
            in0, in1 = gate["in0"], gate["in1"]
            ordered = in0 == left and (in1 == right_address if right_address is not None
                                       else values[in1] == right_value)
            swapped = op != "sub" and in1 == left and (
                in0 == right_address if right_address is not None else values[in0] == right_value)
            if ordered or swapped:
                found = True
                break
        require(found, "source operation lacks exact native gate or justified erasure")

    spans = graph["node_spans"]
    require(type(spans) is list and len(spans) == len(canonical), "canonical span roster differs")
    previous_arithmetic = 0
    previous_eq = 0
    for id_, span in enumerate(spans):
        require(span["id"] == id_ and
                all(type(span[key]) is int and span[key] >= 0 for key in
                    ("qm31_start", "qm31_end", "eq_start", "eq_end")),
                "canonical span malformed")
        require(span["qm31_start"] <= span["qm31_end"] <= gate_total and
                span["eq_start"] <= span["eq_end"] <= len(graph["eq"]),
                "canonical span out of bounds")
        require(span["qm31_start"] == previous_arithmetic and
                span["eq_start"] == previous_eq,
                "canonical spans are not contiguous")
        previous_arithmetic, previous_eq = span["qm31_end"], span["eq_end"]
        tag = canonical[id_]["tag"]
        if tag in ("add", "sub", "mul", "add_const", "mul_const"):
            node = canonical[id_]
            zero_add = (tag == "add" and any(
                canonical[operand]["tag"] == "constant" and
                canonical[operand]["constant"] == 0
                for operand in (node["lhs"], node["rhs"])))
            require(span["qm31_end"] - span["qm31_start"] == (0 if zero_add else 1) and
                    span["eq_start"] == span["eq_end"],
                    "arithmetic node has extra or missing gates")
            if zero_add:
                other = node["rhs"] if canonical[node["lhs"]]["constant"] == 0 else node["lhs"]
                require(wires[id_]["wires"] == wires[other]["wires"],
                        "zero-add peephole did not alias the other operand")
        else:
            require(tag in ("input", "constant"), "canonical operation outside profile")
            if tag == "constant":
                require(span["qm31_start"] == span["qm31_end"] and
                        span["eq_start"] == span["eq_end"],
                        "constant node emitted unexpected gate")

    check_input_packing(graph, raw, inputs)

    # Public ports are fixed by the native output roster and compiler binding
    # spans, not by a caller-provided address list. Each reserved output wire
    # must have its own explicit copy gate.
    output = graph["output"]
    require(type(output) is list and len(output) == 9 and output[0] == 2 and
            values[2] == [0, 0, 1, 0], "public output roster differs")
    for out in output[1:]:
        at = address(out, n)
        require(sum(g["out"] == at and g["in1"] == 0
                    for g in binary["add"]) == 1, "reserved output lacks unique copy gate")
    assignment = json.loads(raw["assignment"])
    certificate = json.loads(raw["certificate"])["ssa"]
    expected_ports = [(entry["name"], assignment["public_inputs"][entry["name"]])
                      for entry in certificate["inputs"] if entry["visibility"] == "public"]
    expected_ports.append((source[certificate["output"]]["name"], nodes[certificate["output"] - len(inputs)]["words"]
                           if certificate["output"] >= len(inputs) else inputs[certificate["output"]]["words"]))
    bindings = graph["bindings"]
    require(type(bindings) is list and len(bindings) == len(expected_ports),
            "public binding roster differs")
    offset = 0
    conversion_cursor = None
    for binding, (name, words) in zip(bindings, expected_ports, strict=True):
        require(binding["name"] == name and binding["word_start"] == offset and
                binding["word_count"] == len(words) and
                binding["binding_qm31_end"] - binding["binding_qm31_start"] == len(words),
                "public binding span differs")
        if conversion_cursor is None:
            conversion_cursor = binding["conversion_qm31_start"]
        require(binding["conversion_qm31_start"] == conversion_cursor and
                conversion_cursor <= binding["conversion_qm31_end"] <= gate_total and
                binding["conversion_m31_to_u32_start"] == 0 and
                binding["conversion_m31_to_u32_end"] == 0,
                "public conversion spans are not contiguous")
        conversion_cursor = binding["conversion_qm31_end"]
        for word in words:
            offset += 1
            require(values[output[offset]] == [word, 0, 0, 0],
                    "public output word differs")
    require(offset <= 8 and all(values[output[i]] == [0] * 4 for i in range(offset + 1, 9)),
            "public padding differs")

    assertions = graph["assertion_spans"]
    require(type(assertions) is list and len(assertions) == len(certificate["assertions"]),
            "assertion span roster differs")
    for index, span in enumerate(assertions):
        require(span["index"] == index and
                span["qm31_start"] == previous_arithmetic and
                span["qm31_start"] <= span["qm31_end"] <= gate_total and
                span["eq_start"] == previous_eq and
                span["eq_end"] == previous_eq + 1 <= len(graph["eq"]),
                "assertion gate span differs")
        previous_arithmetic, previous_eq = span["qm31_end"], span["eq_end"]
        left, right = certificate["assertions"][index]
        for limb in range(len(source[left]["words"])):
            require(source[left]["words"][limb] == source[right]["words"][limb],
                    "source assertion differs")
    require(bindings[0]["conversion_qm31_start"] == previous_arithmetic and
            conversion_cursor == bindings[0]["binding_qm31_start"] and
            all(binding["binding_qm31_start"] == conversion_cursor + binding["word_start"]
                for binding in bindings) and
            previous_eq == len(graph["eq"]) and
            graph["finalization"] is not None and
            graph["finalization"]["qm31_start"] == conversion_cursor + 8 and
            graph["finalization"]["qm31_end"] == gate_total,
            "node/assertion/public/finalization phases are not contiguous")
    check_finalization(graph, raw, inputs)
    require(producers == set(range(n)), "some variables lack a producing gate")
    padded_summary = check_padded_rows(graph, graph["padded"])
    return {"variables": n, "arithmetic_gates": gate_total,
            "equality_gates": len(graph["eq"]), **padded_summary}
