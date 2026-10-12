#!/usr/bin/env python3
"""Native-proof and exact AIR-cost gate for static functional abstractions."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from poseidon2_oracle import leaf
from text_frontend import compile_file


MATCHED_COST = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)
EXPECTED_GEOMETRY = {
    "profile": "direct-m31-v4",
    "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
            "qm31_ops": 322, "triple_xor": 0},
    "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
               "qm31_ops": 512, "triple_xor": 0},
    "preprocessed_cells": 4096,
}
EXPECTED_CIRCUIT_GEOMETRY = {
    "profile": "circuit-v1",
    "chip": None,
    "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 8,
            "qm31_ops": 322, "triple_xor": 0},
    "padded": {"blake_g": 16, "eq": 16, "m31_to_u32": 16,
               "qm31_ops": 512, "triple_xor": 16},
    "preprocessed_cells": 4_248_656,
}
EXPECTED_CHIP_GEOMETRY = {
    "canonical_ir_sha256": "4745fc8a96df2874399ca1b9ef0bfea6e9861d9461ec7a19b084fc8a0237583e",
    "profile": "direct-m31-v4",
    "chip": {"constant": 7, "relation_id": 1395863810, "rounds": 16},
    "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
            "qm31_ops": 292, "triple_xor": 0},
    "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
               "qm31_ops": 512, "triple_xor": 0},
    "preprocessed_cells": 4096,
}
EXPECTED_WIDE_GEOMETRY = {
    "canonical_ir_sha256": "6d3202f16b091a7d311015ff62ef710d0eda7505e844bdeaf461ecea13839a7f",
    "profile": "sparse-wide-v5",
    "chip": None,
    "raw": {"blake_g": 0, "eq": 64, "m31_to_u32": 88,
            "qm31_ops": 7888, "triple_xor": 0},
    "padded": {"blake_g": 0, "eq": 64, "m31_to_u32": 128,
               "qm31_ops": 8192, "triple_xor": 0},
    "preprocessed_cells": 131584,
}
EXPECTED_ARRAY_HASH_GEOMETRY = {
    "canonical_ir_sha256": "99ece52057950a12b578f45a9d1e77529b633c7acc1d9e13598b010e610ddfe7",
    "profile": "direct-m31-v4",
    "chip": None,
    "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
            "qm31_ops": 3300, "triple_xor": 0},
    "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
               "qm31_ops": 4096, "triple_xor": 0},
    "preprocessed_cells": 32768,
}


def compare_cost(functional_cost: dict, manual_cost: dict,
                 expected: dict, description: str) -> None:
    different = [name for name in MATCHED_COST
                 if functional_cost[name] != manual_cost[name]]
    if different:
        raise AssertionError(f"{description} changed circuit/AIR cost: {different}")
    changed_geometry = [name for name, value in expected.items()
                        if functional_cost[name] != value]
    if changed_geometry:
        raise AssertionError(f"{description} baseline geometry changed: {changed_geometry}")


def check_circuit_gate(work: Path, functional: Path, manual: Path,
                       assignment_path: Path) -> dict:
    """Qualify source-function erasure through the general circuit AIR path."""
    functional_package = s31.build(functional, work / "functional-circuit", "gate")
    manual_package = s31.build(manual, work / "manual-circuit", "gate")
    cost = json.loads((functional_package / "cost-report.json").read_text())
    manual_cost = json.loads((manual_package / "cost-report.json").read_text())
    compare_cost(cost, manual_cost, EXPECTED_CIRCUIT_GEOMETRY, "functional circuit AIR")
    trial = s31.trial(functional_package, assignment_path, work / "circuit-trial")
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError("functional circuit AIR verifier or oracle failed")
    return {"canonical_ir_sha256": cost["canonical_ir_sha256"],
            "profile": cost["profile"], "raw": cost["raw"],
            "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "proof_bytes": trial["proof_bytes"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": True}


def check_chip(work: Path) -> dict:
    example = S31 / "examples/recurrence/functional_step16"
    functional = example.with_suffix(".s31")
    manual = example.with_name("functional_step16_manual.s31")
    assignment_path = example.with_suffix(".valid.json")
    assignment = json.loads(assignment_path.read_text())
    modulus = (1 << 31) - 1
    expected = assignment["public_inputs"]["x"][:]
    for _ in range(16):
        expected = [(value * value + 7) % modulus for value in expected]
    if assignment["public_outputs"] != {"result": expected}:
        raise AssertionError("recurrence fixture differs from independent 16-round arithmetic")
    relation, _ = compile_file(functional)
    direct_relation, _ = compile_file(manual)
    if relation != direct_relation:
        raise AssertionError("functional recurrence changed normalized relation")
    if relation["nodes"] != [{
        "name": "result", "op": "repeat", "lhs": "x", "rounds": 16,
        "body": [{"op": "square"}, {"op": "add_const", "constant": 7}],
    }]:
        raise AssertionError("functional recurrence did not become one expected chip node")

    functional_package = s31.build(functional, work / "functional-chip", "direct-chip")
    manual_package = s31.build(manual, work / "manual-chip", "direct-chip")
    cost = json.loads((functional_package / "cost-report.json").read_text())
    manual_cost = json.loads((manual_package / "cost-report.json").read_text())
    compare_cost(cost, manual_cost, EXPECTED_CHIP_GEOMETRY, "functional chip")
    trial = s31.trial(functional_package, assignment_path, work / "chip-trial")
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError("functional chip verifier acceptance or claim rejection missing")
    return {"canonical_ir_sha256": cost["canonical_ir_sha256"],
            "chip": cost["chip"], "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": True}


def check_captured_chip(work: Path) -> dict:
    example = S31 / "examples/recurrence/captured_step16"
    functional = example.with_suffix(".s31")
    manual = example.with_name("captured_step16_manual.s31")
    assignment_path = example.with_suffix(".valid.json")
    assignment = json.loads(assignment_path.read_text())
    modulus = (1 << 31) - 1
    expected = assignment["public_inputs"]["x"][:]
    for _ in range(16):
        expected = [(value * value + 7) % modulus for value in expected]
    if assignment["public_outputs"] != {"result": expected}:
        raise AssertionError("captured recurrence fixture differs from independent arithmetic")
    relation, _ = compile_file(functional)
    direct_relation, _ = compile_file(manual)
    if relation != direct_relation:
        raise AssertionError("captured step changed normalized relation")
    if relation["nodes"] != [{
        "name": "result", "op": "repeat", "lhs": "x", "rounds": 16,
        "body": [{"op": "square"}, {"op": "add_const", "constant": 7}],
    }]:
        raise AssertionError("captured step did not become one expected chip node")
    functional_package = s31.build(functional, work / "captured-chip", "direct-chip")
    manual_package = s31.build(manual, work / "captured-chip-manual", "direct-chip")
    cost = json.loads((functional_package / "cost-report.json").read_text())
    manual_cost = json.loads((manual_package / "cost-report.json").read_text())
    compare_cost(cost, manual_cost, EXPECTED_CHIP_GEOMETRY, "captured functional chip")
    trial = s31.trial(functional_package, assignment_path, work / "captured-chip-trial")
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError("captured chip verifier acceptance or claim rejection missing")
    return {"canonical_ir_sha256": cost["canonical_ir_sha256"],
            "chip": cost["chip"], "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": True}


def check_sparse_wide(work: Path) -> dict:
    example = S31 / "examples/wide/functional_u256_sum"
    functional = example.with_suffix(".s31")
    manual = example.with_name("functional_u256_sum_manual.s31")
    assignment_path = S31 / "examples/wide/u256_sum_checked.valid.json"
    assignment = json.loads(assignment_path.read_text())
    values = assignment["private_inputs"]
    numbers = [sum(word << (16 * index) for index, word in enumerate(values[name]))
               for name in ("a", "b", "c")]
    total = sum(numbers)
    if total >= 1 << 256:
        raise AssertionError("wide fixture unexpectedly overflows")
    expected_limbs = [(total >> (16 * index)) & 0xffff for index in range(16)]
    if assignment["public_outputs"] != {"root": leaf(expected_limbs)}:
        raise AssertionError("wide fixture differs from independent integer/hash arithmetic")
    relation, _ = compile_file(functional)
    direct_relation, _ = compile_file(manual)
    if relation != direct_relation:
        raise AssertionError("functional wide arithmetic changed normalized relation")
    if [node["op"] for node in relation["nodes"]] != [
        "u256_add_checked", "u256_add_checked", "cast_m31", "hash_poseidon2_leaf"
    ]:
        raise AssertionError("functional wide arithmetic did not use the expected primitives")

    functional_package = s31.build(functional, work / "functional-wide", "sparse-wide-gate")
    manual_package = s31.build(manual, work / "manual-wide", "sparse-wide-gate")
    cost = json.loads((functional_package / "cost-report.json").read_text())
    manual_cost = json.loads((manual_package / "cost-report.json").read_text())
    compare_cost(cost, manual_cost, EXPECTED_WIDE_GEOMETRY, "functional sparse-wide")
    trial = s31.trial(functional_package, assignment_path, work / "wide-trial")
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError("functional wide verifier acceptance or claim rejection missing")
    return {"canonical_ir_sha256": cost["canonical_ir_sha256"],
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": trial["changed_public_statement_rejected"]}


def check_array_hash(work: Path) -> dict:
    example = S31 / "examples/arrays/functional_rotate_hash"
    functional = example.with_suffix(".s31")
    manual = example.with_name("functional_rotate_hash_manual.s31")
    assignment_path = example.with_suffix(".valid.json")
    relation, _ = compile_file(functional)
    direct_relation, _ = compile_file(manual)
    if relation != direct_relation:
        raise AssertionError("functional array/hash changed normalized relation")
    if [node["op"] for node in relation["nodes"]] != [
        "array_slice", "array_slice", "array_concat", "add_const", "hash_poseidon2_leaf"
    ]:
        raise AssertionError("array/hash program did not emit expected views and hash")
    assignment = json.loads(assignment_path.read_text())
    source = assignment["private_inputs"]["x"]
    rotated = source[2:] + source[:2]
    expected = leaf([(value + 7) % ((1 << 31) - 1) for value in rotated])
    if assignment["public_outputs"] != {"result": expected}:
        raise AssertionError("array/hash fixture differs from independent view and hash")

    functional_package = s31.build(functional, work / "functional-array-hash", "direct-gate")
    manual_package = s31.build(manual, work / "manual-array-hash", "direct-gate")
    cost = json.loads((functional_package / "cost-report.json").read_text())
    manual_cost = json.loads((manual_package / "cost-report.json").read_text())
    compare_cost(cost, manual_cost, EXPECTED_ARRAY_HASH_GEOMETRY, "functional array/hash")
    trial = s31.trial(functional_package, assignment_path, work / "array-hash-trial")
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError("functional array/hash verifier or oracle failed")
    return {"canonical_ir_sha256": cost["canonical_ir_sha256"],
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": trial["changed_public_statement_rejected"]}


def main() -> None:
    example = S31 / "examples/arithmetic/functional_square4"
    functional = example.with_suffix(".s31")
    manual = example.with_name("functional_square4_manual.s31")
    assignment_path = example.with_suffix(".valid.json")
    assignment = json.loads(assignment_path.read_text())
    modulus = (1 << 31) - 1
    expected = [pow(x, 4, modulus) for x in assignment["public_inputs"]["x"]]
    if assignment["public_outputs"] != {"result": expected}:
        raise AssertionError("functional fixture differs from independent x^4 calculation")
    for source in (functional, manual):
        relation, _ = compile_file(source)
        if [node["op"] for node in relation["nodes"]] != ["mul", "mul"]:
            raise AssertionError(f"{source.name} did not lower to two multiplications")

    with tempfile.TemporaryDirectory(prefix="s31-functional-core-") as directory:
        work = Path(directory)
        functional_package = s31.build(functional, work / "functional", "direct-gate")
        manual_package = s31.build(manual, work / "manual", "direct-gate")
        functional_cost = json.loads((functional_package / "cost-report.json").read_text())
        manual_cost = json.loads((manual_package / "cost-report.json").read_text())
        compare_cost(functional_cost, manual_cost, EXPECTED_GEOMETRY, "functional arithmetic")
        trial = s31.trial(functional_package, assignment_path, work / "trial")
        if (not trial["native_verifier_accepted"] or
                not trial["changed_public_statement_rejected"] or
                trial["independent_value_oracle"]["status"] != "passed"):
            raise AssertionError("native verifier acceptance or claim rejection missing")
        circuit_report = check_circuit_gate(work, functional, manual, assignment_path)
        chip_report = check_chip(work)
        captured_chip_report = check_captured_chip(work)
        wide_report = check_sparse_wide(work)
        array_hash_report = check_array_hash(work)
        print(json.dumps({
            "schema": "s31-functional-core-acceptance-v4",
            "arithmetic": {
                "canonical_ir_sha256": functional_cost["canonical_ir_sha256"],
                "raw": functional_cost["raw"],
                "padded": functional_cost["padded"],
                "preprocessed_cells": functional_cost["preprocessed_cells"],
                "native_verifier_accepted": True,
                "changed_public_statement_rejected": trial["changed_public_statement_rejected"],
            },
            "circuit_air": circuit_report,
            "recurrence_chip": chip_report,
            "captured_recurrence_chip": captured_chip_report,
            "sparse_wide": wide_report,
            "array_hash": array_hash_report,
        }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
