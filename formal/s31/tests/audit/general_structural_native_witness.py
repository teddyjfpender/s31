#!/usr/bin/env python3
"""Generic Lean-checked source to native direct-Gate witness audit controls."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(FORMAL / "tests/audit"))
sys.path.insert(0, str(FORMAL))
from structural_derivation_lean import artifacts, canonical, source  # noqa: E402
from scripts.general_structural_native_witness import (  # noqa: E402
    MAXIMUM, check, checked_words, native_check,
)
from scripts.native_graph_certificate import check_graph  # noqa: E402

P = 2**31 - 1

CASES = (
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

        raw = case_bytes(CASES[0][1], CASES[0][2])
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
    print("generic structural/native audit: seven source families accepted; "
          "four Lean, five native, and seven exported-graph mutations rejected")


if __name__ == "__main__":
    main()
