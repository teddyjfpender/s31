"""Replay exact padded Gate topology and native preprocessed QM31/Eq rows.

The export comes from `PreprocessedCircuit.fromBuilderCircuit` after the
production `padContext` pass. This checks column cells, not their later
commitment root, lookup argument, or committed witness openings.
"""

from __future__ import annotations

P = 2**31 - 1
PAD_MIN = 16


def require(ok: bool, reason: str) -> None:
    if not ok:
        raise ValueError("native AIR projection: " + reason)


def padded_size(count: int) -> int:
    return max(PAD_MIN, 1 << (max(count, 1) - 1).bit_length())


def check_padded_rows(base: dict, padded: dict) -> dict[str, int]:
    gate_names = ("add", "sub", "mul", "pointwise_mul", "eq", "triple_xor",
                  "m31_to_u32", "blake_g_gate", "permutation_ends",
                  "permutation_inputs", "permutation_outputs", "output")
    required = {"n_vars", "values", *gate_names, "qm31_rows", "eq_rows"}
    require(type(padded) is dict and set(padded) == required,
            "padded graph field roster differs")
    raw_n, n = base["n_vars"], padded["n_vars"]
    values = padded["values"]
    require(type(n) is int and raw_n <= n <= 524288 and
            type(values) is list and len(values) == n and
            values[:raw_n] == base["values"],
            "padded variable values do not extend base graph")
    for quad in values:
        require(type(quad) is list and len(quad) == 4 and
                all(type(x) is int and 0 <= x < P for x in quad),
                "padded variable has noncanonical coordinate")
    for field in gate_names:
        require(type(padded[field]) is list and
                padded[field][:len(base[field])] == base[field],
                f"padded {field} changed the compiled prefix")
    for field in ("sub", "mul", "pointwise_mul", "permutation_ends",
                  "permutation_inputs", "permutation_outputs", "output"):
        require(padded[field] == base[field], f"padding unexpectedly added {field}")

    raw_q = sum(len(base[field]) for field in ("add", "sub", "mul", "pointwise_mul"))
    q_size = padded_size(raw_q)
    eq_size = padded_size(len(base["eq"]))
    xor_size = padded_size(len(base["triple_xor"]))
    convert_size = padded_size(len(base["m31_to_u32"]))
    blake_size = padded_size(len(base["blake_g_gate"]))
    require(len(padded["add"]) == len(base["add"]) + q_size - raw_q and
            len(padded["eq"]) == eq_size and
            len(padded["triple_xor"]) == xor_size and
            len(padded["m31_to_u32"]) == convert_size and
            len(padded["blake_g_gate"]) == blake_size,
            "component row counts do not match padContext targets")

    next_var = raw_n
    for gate in padded["add"][len(base["add"]):]:
        require(gate == {"in0": 1, "in1": 1, "out": next_var} and
                values[next_var] == [2, 0, 0, 0], "QM31 padding gate differs")
        next_var += 1
    for gate in padded["eq"][len(base["eq"]):]:
        require(gate == {"in0": 0, "in1": 0}, "Eq padding gate differs")
    for gate in padded["triple_xor"][len(base["triple_xor"]):]:
        require(gate == {"input_a": 0, "input_b": 0, "input_c": 0,
                         "out": next_var} and values[next_var] == [0] * 4,
                "TripleXor padding gate differs")
        next_var += 1
    for gate in padded["m31_to_u32"][len(base["m31_to_u32"]):]:
        require(gate == {"input": 0, "out": next_var} and
                values[next_var] == [0] * 4, "M31ToU32 padding gate differs")
        next_var += 1
    for gate in padded["blake_g_gate"][len(base["blake_g_gate"]):]:
        require(gate == {"input_a": 0, "input_b": 0, "input_c": 0,
                         "input_d": 0, "input_f0": 0, "input_f1": 0,
                         "out_base": next_var} and
                values[next_var:next_var + 4] == [[0] * 4] * 4,
                "BlakeG padding gate differs")
        next_var += 4
    require(next_var == n, "padded variable allocation has unowned tail")

    uses = [0] * n

    def bump(at: int) -> None:
        require(type(at) is int and 0 <= at < n, "padded gate address out of range")
        uses[at] += 1
        require(uses[at] < P, "padded multiplicity exceeds M31")

    for field in ("add", "sub", "mul", "pointwise_mul"):
        for gate in padded[field]:
            bump(gate["in0"])
            bump(gate["in1"])
    for gate in padded["eq"]:
        bump(gate["in0"])
        bump(gate["in1"])
    for gate in padded["triple_xor"]:
        for field in ("input_a", "input_b", "input_c"):
            bump(gate[field])
    for gate in padded["m31_to_u32"]:
        bump(gate["input"])
    for gate in padded["blake_g_gate"]:
        for field in ("input_a", "input_b", "input_c", "input_d", "input_f0", "input_f1"):
            bump(gate[field])
    for out in padded["output"]:
        bump(out)

    expected_q = []
    for opcode, field in enumerate(("add", "sub", "mul", "pointwise_mul")):
        for gate in padded[field]:
            expected_q.append([*(int(i == opcode) for i in range(4)),
                               gate["in0"], gate["in1"], gate["out"], uses[gate["out"]]])
    expected_eq = [[gate["in0"], gate["in1"]] for gate in padded["eq"]]
    require(len(expected_q) == q_size and padded["qm31_rows"] == expected_q,
            "native QM31 preprocessed selector/address/multiplicity row differs")
    require(len(expected_eq) == eq_size and padded["eq_rows"] == expected_eq,
            "native Eq preprocessed address row differs")
    return {"padded_variables": n, "qm31_air_rows": q_size, "eq_air_rows": eq_size}
