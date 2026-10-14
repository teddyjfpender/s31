#!/usr/bin/env python3
"""Generic Lean-checked source to native direct-Gate witness audit controls."""

from __future__ import annotations

import copy
import hashlib
import json
import stat
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

FORMAL = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(FORMAL / "tests/audit"))
sys.path.insert(0, str(FORMAL))
from structural_derivation_lean import artifacts, canonical, source  # noqa: E402
from scripts.general_structural_native_witness import (  # noqa: E402
    MAXIMUM, check, checked_words, native_check,
)
from scripts.native_graph_certificate import check_graph  # noqa: E402
from scripts.native_air_projection import padded_size  # noqa: E402

P = 2**31 - 1

CASES = (
    ("private_only", b"circuit just(private x: [m31; 2]) -> public [m31; 2] { "
     b"let y = x + x; assert_eq(y,y); y }",
     {"public_inputs": {}, "private_inputs": {"x": [7, 9]},
      "public_outputs": {"y": [14, 18]}}),
    ("one_lane_private_first", b"circuit one(private x: [m31; 1], public y: [m31; 1]) "
     b"-> public [m31; 1] { let z = y - x; assert_eq(z,z); z }",
     {"public_inputs": {"y": [12]}, "private_inputs": {"x": [5]},
      "public_outputs": {"z": [7]}}),
    ("two_public", b"circuit two(public x: [m31; 1], public y: [m31; 1], "
     b"private z: [m31; 1]) -> public [m31; 1] { let out = x + y; "
     b"assert_eq(out,z); out }",
     {"public_inputs": {"x": [7], "y": [9]},
      "private_inputs": {"z": [16]}, "public_outputs": {"out": [16]}}),
    ("three_inputs", b"circuit mixed(public a: [m31; 2], private b: [m31; 2], "
     b"private c: [m31; 2]) -> public [m31; 2] { let t = a + b; "
     b"let u = t .* c; let z = u - b; assert_eq(z,z); z }",
     {"public_inputs": {"a": [P - 1, 7]}, "private_inputs": {"b": [2, 3], "c": [4, 5]},
      "public_outputs": {"z": [2, 47]}}),
    ("four_lanes_constants", b"circuit consts(public x: [m31; 4], "
     b"private y: [m31; 4]) -> public [m31; 4] { "
     b"let t = x + splat<4>(7_m31); let z = t .* splat<4>(3_m31); "
     b"assert_eq(z, y); z }",
     {"public_inputs": {"x": [P - 1, 0, 1, 7]},
      "private_inputs": {"y": [18, 21, 24, 42]},
      "public_outputs": {"z": [18, 21, 24, 42]}}),
    ("three_lanes_mixed_order", b"circuit three(private a: [m31; 3], "
     b"public b: [m31; 3], private c: [m31; 3]) -> public [m31; 3] { "
     b"let t = a + b; let z = t - c; assert_eq(z,z); z }",
     {"public_inputs": {"b": [4, 5, 6]},
      "private_inputs": {"a": [10, 20, 30], "c": [1, 2, 3]},
      "public_outputs": {"z": [13, 23, 33]}}),
    ("commutative_cse", b"circuit repeat(public x: [m31; 2], "
     b"private y: [m31; 2]) -> public [m31; 2] { let a = x + y; "
     b"let b = y + x; let z = a .* b; assert_eq(z,z); z }",
     {"public_inputs": {"x": [2, 3]}, "private_inputs": {"y": [4, 5]},
      "public_outputs": {"z": [36, 64]}}),
    ("erased_identities", b"circuit identity(public x: [m31; 2], "
     b"private y: [m31; 2]) -> public [m31; 2] { "
     b"let a = x + splat<2>(0_m31); "
     b"let z = a .* splat<2>(1_m31); assert_eq(y,y); z }",
     {"public_inputs": {"x": [2, 3]}, "private_inputs": {"y": [4, 5]},
      "public_outputs": {"z": [2, 3]}}),
    ("folded_constants", b"circuit folded(public x: [m31; 2], "
     b"private y: [m31; 2]) -> public [m31; 2] { "
     b"let zero = x .* splat<2>(0_m31); "
     b"let z = zero + splat<2>(7_m31); assert_eq(z,y); z }",
     {"public_inputs": {"x": [P - 1, 3]}, "private_inputs": {"y": [7, 7]},
      "public_outputs": {"z": [7, 7]}}),
    ("zero_add_peephole", b"circuit zero_add(public x: [m31; 2], "
     b"private y: [m31; 2]) -> public [m31; 2] { "
     b"let zero = x .* splat<2>(0_m31); let z = zero + y; "
     b"assert_eq(z,y); z }",
     {"public_inputs": {"x": [P - 1, 3]}, "private_inputs": {"y": [7, 9]},
      "public_outputs": {"z": [7, 9]}}),
    ("tuple_helper", source("helper_tuple", 2),
     {"public_inputs": {"x": [7, 11]}, "private_inputs": {"y": [3, 5]},
      "public_outputs": {"z": [4, 6]}}),
)


def case_bytes(source_bytes: bytes, assignment: dict) -> dict[str, bytes]:
    result = artifacts(source_bytes)
    result["assignment"] = canonical(assignment)
    result["statement"] = canonical({key: assignment[key]
                                     for key in ("public_inputs", "public_outputs")})
    return result


def write_case(work: Path, raw: dict[str, bytes]) -> list[Path]:
    paths = []
    for name in MAXIMUM:
        path = work / name
        path.write_bytes(raw[name])
        paths.append(path)
    return paths


def rejected(work: Path, raw: dict[str, bytes], reason: str) -> None:
    try:
        check(write_case(work, raw))
    except ValueError as exc:
        if reason not in str(exc):
            raise AssertionError(f"wrong rejection boundary: {exc}") from exc
    else:
        raise AssertionError("resealed adversarial mutation was accepted")


def reseal(raw: dict[str, bytes]) -> dict[str, bytes]:
    result = dict(raw)
    tree = json.loads(raw["tree"])
    cert = json.loads(raw["certificate"])
    for name in ("source", "relation", "abi"):
        field = "public_abi_sha256" if name == "abi" else name + "_sha256"
        tree[field] = hashlib.sha256(result[name]).hexdigest()
        if name != "abi":
            cert[field] = hashlib.sha256(result[name]).hexdigest()
    result["tree"] = canonical(tree)
    result["certificate"] = canonical(cert)
    return result


def coherent_extra_input_gate(exported: dict) -> dict:
    """Insert a real fresh 0+0 gate before the first source input.

    Shift all subsequently allocated addresses, phase cursors, and padded AIR
    rows. This was accepted before independent input-span replay: uniqueness of
    producers and honest finalization alone do not exclude the extra gate.
    """
    graph = copy.deepcopy(exported)
    first_input = 11  # zero, one, u, and eight reserved public outputs

    def shift(address: int) -> int:
        return address + 1 if address >= first_input else address

    for name in ("add", "sub", "mul", "pointwise_mul"):
        for gate in graph[name]:
            for field in ("in0", "in1", "out"):
                gate[field] = shift(gate[field])
    for gate in graph["eq"]:
        for field in ("in0", "in1"):
            gate[field] = shift(gate[field])
    for var in graph["constant_vars"]:
        var["idx"] = shift(var["idx"])
    for node in graph["node_wires"]:
        node["wires"] = [shift(at) for at in node["wires"]]
    graph["output"] = [shift(at) for at in graph["output"]]
    graph["values"].insert(first_input, [0] * 4)
    graph["n_vars"] += 1
    graph["add"].insert(0, {"in0": 0, "in1": 0, "out": first_input})
    for span in graph["node_spans"]:
        if span["id"] != 0:
            span["qm31_start"] += 1
        span["qm31_end"] += 1
    for span in graph["assertion_spans"]:
        span["qm31_start"] += 1
        span["qm31_end"] += 1
    for binding in graph["bindings"]:
        for field in ("conversion_qm31_start", "conversion_qm31_end",
                      "binding_qm31_start", "binding_qm31_end"):
            binding[field] += 1
    graph["finalization"]["qm31_start"] += 1
    graph["finalization"]["qm31_end"] += 1

    padded = {name: copy.deepcopy(graph[name]) for name in
              ("add", "sub", "mul", "pointwise_mul", "eq", "triple_xor",
               "m31_to_u32", "blake_g_gate", "permutation_ends",
               "permutation_inputs", "permutation_outputs", "output")}
    padded["values"] = copy.deepcopy(graph["values"])
    next_var = graph["n_vars"]
    raw_q = sum(len(graph[name]) for name in
                ("add", "sub", "mul", "pointwise_mul"))
    for _ in range(padded_size(raw_q) - raw_q):
        padded["add"].append({"in0": 1, "in1": 1, "out": next_var})
        padded["values"].append([2, 0, 0, 0])
        next_var += 1
    for _ in range(padded_size(len(graph["eq"])) - len(graph["eq"])):
        padded["eq"].append({"in0": 0, "in1": 0})
    for _ in range(padded_size(0)):
        padded["triple_xor"].append({"input_a": 0, "input_b": 0,
                                     "input_c": 0, "out": next_var})
        padded["values"].append([0] * 4)
        next_var += 1
    for _ in range(padded_size(0)):
        padded["m31_to_u32"].append({"input": 0, "out": next_var})
        padded["values"].append([0] * 4)
        next_var += 1
    for _ in range(padded_size(0)):
        padded["blake_g_gate"].append({
            "input_a": 0, "input_b": 0, "input_c": 0, "input_d": 0,
            "input_f0": 0, "input_f1": 0, "out_base": next_var,
        })
        padded["values"].extend([[0] * 4 for _ in range(4)])
        next_var += 4
    padded["n_vars"] = next_var
    uses = [0] * next_var
    for name in ("add", "sub", "mul", "pointwise_mul", "eq"):
        for gate in padded[name]:
            uses[gate["in0"]] += 1
            uses[gate["in1"]] += 1
    for gate in padded["triple_xor"]:
        for field in ("input_a", "input_b", "input_c"):
            uses[gate[field]] += 1
    for gate in padded["m31_to_u32"]:
        uses[gate["input"]] += 1
    for gate in padded["blake_g_gate"]:
        for field in ("input_a", "input_b", "input_c", "input_d", "input_f0", "input_f1"):
            uses[gate[field]] += 1
    for at in padded["output"]:
        uses[at] += 1
    padded["qm31_rows"] = [
        [*(int(opcode == index) for index in range(4)),
         gate["in0"], gate["in1"], gate["out"], uses[gate["out"]]]
        for opcode, name in enumerate(("add", "sub", "mul", "pointwise_mul"))
        for gate in padded[name]
    ]
    padded["eq_rows"] = [[gate["in0"], gate["in1"]] for gate in padded["eq"]]
    graph["padded"] = padded
    return graph


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-general-structural-native-audit-") as temp:
        work = Path(temp)
        for label, source_bytes, assignment in CASES:
            raw = case_bytes(source_bytes, assignment)
            saved_graph = work / "verified-native-graph.json" if label == "three_inputs" else None
            result = check(write_case(work, raw), saved_graph)
            if result["status"] != "accepted":
                raise AssertionError(f"{label}: honest source rejected")
            if saved_graph is not None:
                if hashlib.sha256(saved_graph.read_bytes()).hexdigest() != result["graph_sha256"]:
                    raise AssertionError("exported graph digest differs from verified bytes")
                if stat.S_IMODE(saved_graph.stat().st_mode) != 0o600:
                    raise AssertionError("private graph artifact is not mode 0600")

        _, source_bytes, assignment = next(case for case in CASES if case[0] == "three_inputs")
        raw = case_bytes(source_bytes, assignment)
        changed_source = {**raw, "source": raw["source"].replace(b"t .* c", b"t + c")}
        rejected(work, reseal(changed_source), "Lean structural statement gate")
        changed_relation = json.loads(raw["relation"])
        changed_relation["nodes"][0]["op"] = "sub"
        rejected(work, reseal({**raw, "relation": canonical(changed_relation)}),
                 "Lean structural statement gate")
        changed_assignment = json.loads(raw["assignment"])
        changed_assignment["private_inputs"]["b"][0] += 1
        rejected(work, {**raw, "assignment": canonical(changed_assignment)},
                 "Lean structural statement gate")
        forged_statement = json.loads(raw["statement"])
        forged_statement["private_inputs"] = {"b": [2, 3]}
        rejected(work, {**raw, "statement": canonical(forged_statement)},
                 "Lean structural statement gate")
        inputs, nodes = checked_words(raw)
        exported = native_check(raw, inputs, nodes, work, export_graph=True)
        check_graph(exported, raw, inputs, nodes)
        graph_mutations = (
            ("extra_gate", lambda g: g["add"].append({"in0": 0, "in1": 0, "out": 0})),
            ("add_operand", lambda g: g["add"][0].__setitem__("in0", 0)),
            ("wire_value", lambda g: g["values"][g["node_wires"][3]["wires"][0]].__setitem__(0, 99)),
            ("source_map", lambda g: g["source_map"][3].__setitem__("id", 0)),
            ("public_port", lambda g: g["output"].__setitem__(1, 0)),
            ("constant_key", lambda g: g["constant_keys"].__setitem__(0, 123)),
            ("assertion_roster", lambda g: g["assertion_spans"].clear()),
            ("air_selector", lambda g: g["padded"]["qm31_rows"][0].__setitem__(0, 0)),
            ("air_address", lambda g: g["padded"]["qm31_rows"][0].__setitem__(4, 0)),
            ("air_multiplicity", lambda g: g["padded"]["qm31_rows"][0].__setitem__(7, 9)),
            ("eq_air_address", lambda g: g["padded"]["eq_rows"][0].__setitem__(0, 0)),
            ("padding_gate", lambda g: g["padded"]["add"][len(exported["add"])].__setitem__("in0", 0)),
            ("padding_value", lambda g: g["padded"]["values"][exported["n_vars"]].__setitem__(0, 3)),
            ("finalization_gate_order", lambda g: g["add"].__setitem__(
                slice(-2, None), list(reversed(g["add"][-2:])))),
        )
        for label, mutate in graph_mutations:
            changed = copy.deepcopy(exported)
            mutate(changed)
            try:
                check_graph(changed, raw, inputs, nodes)
            except ValueError:
                pass
            else:
                raise AssertionError(f"independent graph checker accepted {label}")
        changed = coherent_extra_input_gate(exported)
        # All previous checks, including exact finalization and padded rows,
        # still accept this fully coherent extra input-phase arithmetic gate.
        with patch("scripts.native_graph_certificate.check_input_packing", lambda *_: None):
            check_graph(changed, raw, inputs, nodes)
        try:
            check_graph(changed, raw, inputs, nodes)
        except ValueError as exc:
            if "native input packing:" not in str(exc):
                raise AssertionError(f"wrong extra-input-gate rejection: {exc}") from exc
        else:
            raise AssertionError("coherent extra input gate was accepted")
        changed = copy.deepcopy(exported)
        changed["eq"].insert(0, {"in0": 0, "in1": 0})
        for span in changed["node_spans"]:
            if span["id"] != 0:
                span["eq_start"] += 1
            span["eq_end"] += 1
        for span in changed["assertion_spans"]:
            span["eq_start"] += 1
            span["eq_end"] += 1
        changed["padded"]["eq"].insert(0, {"in0": 0, "in1": 0})
        changed["padded"]["eq"].pop()
        changed["padded"]["eq_rows"] = [
            [gate["in0"], gate["in1"]] for gate in changed["padded"]["eq"]
        ]
        with patch("scripts.native_graph_certificate.check_input_packing", lambda *_: None):
            check_graph(changed, raw, inputs, nodes)
        try:
            check_graph(changed, raw, inputs, nodes)
        except ValueError as exc:
            if "native input packing:" not in str(exc):
                raise AssertionError(f"wrong extra-input-equality rejection: {exc}") from exc
        else:
            raise AssertionError("coherent extra input equality was accepted")
        # Keep the graph equation and its finalization span coherent while
        # adding a satisfiable gate. Equation-only and phase checks accept
        # this shape; exact constant/guess enumeration must reject it.
        changed = copy.deepcopy(exported)
        new_address = changed["n_vars"]
        changed["n_vars"] += 1
        changed["values"].append([0, 0, 0, 0])
        changed["add"].append({"in0": 0, "in1": 0, "out": new_address})
        changed["finalization"]["qm31_end"] += 1
        try:
            check_graph(changed, raw, inputs, nodes)
        except ValueError as exc:
            if "finalization row count differs" not in str(exc):
                raise AssertionError(f"wrong coherent extra-gate rejection: {exc}") from exc
        else:
            raise AssertionError("coherent extra finalization gate was accepted")
        wrong_op = copy.deepcopy(nodes)
        wrong_op[0]["op"] = "sub"
        try:
            native_check(raw, inputs, wrong_op, work)
        except ValueError as exc:
            if "native gate operation or operands differ" not in str(exc):
                raise AssertionError(f"wrong native gate rejection: {exc}") from exc
        else:
            raise AssertionError("native wrong opcode accepted")
        wrong_input = copy.deepcopy(inputs)
        wrong_input[0]["words"][0] += 1
        try:
            native_check(raw, wrong_input, nodes, work)
        except ValueError as exc:
            if "compiled node value differs" not in str(exc):
                raise AssertionError(f"wrong native input rejection: {exc}") from exc
        else:
            raise AssertionError("native wrong input value accepted")
        wrong_map = copy.deepcopy(nodes)
        wrong_map[0]["canonical_id"] += 1
        try:
            native_check(raw, inputs, wrong_map, work)
        except ValueError as exc:
            if "source node address differs" not in str(exc):
                raise AssertionError(f"wrong native CSE map rejection: {exc}") from exc
        else:
            raise AssertionError("native wrong canonical source map accepted")
        for field in ("tamper_extra_gate_for_test", "tamper_changed_gate_for_test"):
            try:
                native_check(raw, inputs, nodes, work, **{field: True})
            except ValueError as exc:
                if "witness and witness-free gate graphs differ" not in str(exc):
                    raise AssertionError(f"wrong gate graph rejection: {exc}") from exc
            else:
                raise AssertionError(f"native {field} accepted")
    print("generic structural/native audit: eleven source families accepted; "
          "four Lean, five native, and seventeen exported-graph/AIR mutations rejected")


if __name__ == "__main__":
    main()
