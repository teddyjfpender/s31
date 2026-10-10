#!/usr/bin/env python3
"""Native zero-cost and soundness gate for functional math and hash calls."""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/python/generated"))

import s31
from poseidon2_oracle import leaf, pair
from test_functional_library_generated import math_cases, pair_sources
from text_frontend import compile_text


P = (1 << 31) - 1
MATCHED_COST = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)
EXPECTED_GEOMETRY: dict[str, dict] = {
    "curried_sum": {
        "canonical_ir_sha256": "969fd73181498025b6ffa9de584601fa3ac70788044c7fbcc37bb2e6ea617fd4",
        "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                "qm31_ops": 275, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                   "qm31_ops": 512, "triple_xor": 0},
        "preprocessed_cells": 4096,
    },
    "polynomial": {
        "canonical_ir_sha256": "c1ead6e85081a721a339bb65733a2eb055d50bfc7599bfc512a65d64168f32a7",
        "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                "qm31_ops": 318, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                   "qm31_ops": 512, "triple_xor": 0},
        "preprocessed_cells": 4096,
    },
    "matrix": {
        "canonical_ir_sha256": "0151cd9fda93eb77be8e22ec09f6da5769a3745a0fbca941ce246f2306a9ca0e",
        "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                "qm31_ops": 326, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                   "qm31_ops": 512, "triple_xor": 0},
        "preprocessed_cells": 4096,
    },
    "poseidon_pair": {
        "canonical_ir_sha256": "b6a2363f1cb1b9bd6d55f03ab9debb0bef89cf45297ee14dd31fea260e46c7a9",
        "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                "qm31_ops": 11840, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                   "qm31_ops": 16384, "triple_xor": 0},
        "preprocessed_cells": 131072,
    },
}


@dataclass(frozen=True)
class Case:
    name: str
    functional: str
    direct: str
    private_inputs: dict[str, list[int]]
    expected: list[int]
    expected_ops: tuple[str, ...]


def cases() -> list[Case]:
    x = [0, 1, P - 1, 7]
    y = [P - 1, 2, 3, 5]
    poly_source = S31 / "examples/arithmetic/functional_poly4.s31"
    polynomial = Case(
        "polynomial", poly_source.read_text(),
        poly_source.with_name("functional_poly4_manual.s31").read_text(),
        {"x": [0, 1, 2, 7]}, [2 * value * value + 3 * value + 7
                             for value in (0, 1, 2, 7)],
        ("mul_const", "add_const", "mul", "add_const"),
    )
    curried_source = S31 / "examples/arithmetic/curried_sum.s31"
    curried = Case(
        "curried_sum", curried_source.read_text(),
        curried_source.with_name("curried_sum_manual.s31").read_text(),
        {"a": [P - 1], "b": [2]}, [(P - 1 + 2) % P], ("add",),
    )
    matrix = next(case for case in math_cases() if case.family == "matmul")
    matrix_functional, matrix_direct = matrix.sources()
    result = [polynomial, curried, Case("matrix", matrix_functional, matrix_direct,
                               {"x": x, "y": y}, matrix.value(x, y),
                               ("mul", "add"))]
    functional, direct = pair_sources()
    left = list(range(1, 9))
    right = list(range(9, 17))
    result.append(Case("poseidon_pair", functional, direct,
                       {"x": left, "y": right}, pair(leaf(left), leaf(right)),
                       ("hash_poseidon2_leaf", "hash_poseidon2_leaf",
                        "hash_poseidon2_pair")))
    return result


def check_case(work: Path, case: Case) -> dict:
    relation, _ = compile_text(case.functional, f"{case.name}-functional.s31")
    direct_relation, _ = compile_text(case.direct, f"{case.name}-direct.s31")
    if relation != direct_relation:
        raise AssertionError(f"{case.name}: closure added or changed relation operations")
    operations = [node["op"] for node in relation["nodes"]]
    if case.name == "poseidon_pair":
        if operations != list(case.expected_ops):
            raise AssertionError(f"{case.name}: hash tree operations changed: {operations}")
    elif case.name == "polynomial":
        if operations != list(case.expected_ops):
            raise AssertionError(f"{case.name}: Horner operation schedule changed: {operations}")
    elif not set(case.expected_ops).issubset(operations):
        raise AssertionError(f"{case.name}: expected nontrivial field operations")

    output_name = relation["public_outputs"][0]
    assignment = {"public_inputs": {}, "private_inputs": case.private_inputs,
                  "public_outputs": {output_name: case.expected}}
    if case.name in {"polynomial", "curried_sum"}:
        fixture_name = ("functional_poly4" if case.name == "polynomial" else
                        "curried_sum")
        fixture = json.loads((S31 / f"examples/arithmetic/{fixture_name}.valid.json").read_text())
        if assignment != fixture:
            raise AssertionError(f"{case.name}: fixture differs from independent arithmetic")
    functional_path = work / f"{case.name}-functional.s31"
    direct_path = work / f"{case.name}-direct.s31"
    assignment_path = work / f"{case.name}.valid.json"
    functional_path.write_text(case.functional)
    direct_path.write_text(case.direct)
    assignment_path.write_text(json.dumps(assignment, sort_keys=True) + "\n")

    functional_package = s31.build(functional_path, work / f"{case.name}-functional",
                                   "direct-gate")
    direct_package = s31.build(direct_path, work / f"{case.name}-direct", "direct-gate")
    cost = json.loads((functional_package / "cost-report.json").read_text())
    direct_cost = json.loads((direct_package / "cost-report.json").read_text())
    mismatched = [key for key in MATCHED_COST if cost[key] != direct_cost[key]]
    if mismatched:
        raise AssertionError(f"{case.name}: functional AIR cost changed: {mismatched}")
    if cost["profile"] != "direct-m31-v4" or cost["raw"]["qm31_ops"] <= 0:
        raise AssertionError(f"{case.name}: direct arithmetic AIR was not selected")
    geometry = EXPECTED_GEOMETRY[case.name]
    changed = [key for key, value in geometry.items() if cost[key] != value]
    if changed:
        raise AssertionError(f"{case.name}: pinned AIR geometry changed: {changed}")

    trial = s31.trial(functional_package, assignment_path, work / f"{case.name}-trial")
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError(f"{case.name}: native acceptance or claim rejection failed")
    return {"name": case.name, "canonical_ir_sha256": cost["canonical_ir_sha256"],
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "proof_bytes": trial["proof_bytes"], "native_verifier_accepted": True,
            "changed_public_statement_rejected": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=[case.name for case in cases()],
                        help="run one named native case during development")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="s31-functional-library-") as directory:
        work = Path(directory)
        reports = [check_case(work, case) for case in cases()
                   if args.case is None or case.name == args.case]
    print(json.dumps({"schema": "s31-functional-library-native-v1", "cases": reports},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
