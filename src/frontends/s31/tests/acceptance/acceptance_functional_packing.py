#!/usr/bin/env python3
"""Native zero-cost gate for functional arrays straddling QM31 wire boundaries."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/python/generated"))

import s31
from test_functional_packing_generated import P, expected, sources
from text_frontend import compile_text


LENGTHS = (3, 5, 9)
MATCHED_COST = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)
EXPECTED_GEOMETRY = {
    3: {"canonical_ir_sha256": "e3ea83e889bd057863f9a0c4ffe0718a841294d5cd84b4085ec9ea63dcdba457",
        "raw_qm31_rows": 311},
    5: {"canonical_ir_sha256": "2300f6cbb72cbc19e133198760f171bc45b02d312f9fd813d6eb8c6f7fc1965f",
        "raw_qm31_rows": 319},
    9: {"canonical_ir_sha256": "4f9dd7ee7297c46dfb52c9c396418ce520e4e5ea3d443540b6d6d8f7cbed1d6f",
        "raw_qm31_rows": 328},
}


def assignment(length: int, choice: int, output_name: str) -> dict:
    x = [(index * 257 + length) % P for index in range(length)]
    y = [(P - 1 - index * 131) % P for index in range(length)]
    return {
        "public_inputs": {},
        "private_inputs": {"choice": [choice], "x": x, "y": y},
        "public_outputs": {output_name: [expected(choice, x, y)]},
    }


def check_length(work: Path, length: int) -> dict:
    functional, direct = sources(length)
    relation, _ = compile_text(functional, f"packed-{length}.s31")
    reference, _ = compile_text(direct, f"direct-{length}.s31")
    if relation != reference:
        raise AssertionError(f"length {length}: functional IR changed")
    output_name = relation["public_outputs"][0]
    function_path = work / f"functional-{length}.s31"
    direct_path = work / f"direct-{length}.s31"
    function_path.write_text(functional)
    direct_path.write_text(direct)
    function_package = s31.build(function_path, work / f"functional-{length}", "direct-gate")
    direct_package = s31.build(direct_path, work / f"direct-{length}", "direct-gate")
    cost = json.loads((function_package / "cost-report.json").read_text())
    reference_cost = json.loads((direct_package / "cost-report.json").read_text())
    mismatched = [key for key in MATCHED_COST if cost[key] != reference_cost[key]]
    if mismatched:
        raise AssertionError(f"length {length}: functional circuit/AIR cost changed: {mismatched}")
    if cost["profile"] != "direct-m31-v4" or cost["raw"]["qm31_ops"] <= 0:
        raise AssertionError(f"length {length}: expected a live direct arithmetic AIR")
    expected_cost = EXPECTED_GEOMETRY[length]
    if (cost["canonical_ir_sha256"] != expected_cost["canonical_ir_sha256"] or
            cost["raw"]["qm31_ops"] != expected_cost["raw_qm31_rows"] or
            cost["padded"]["qm31_ops"] != 512 or
            cost["preprocessed_cells"] != 4096):
        raise AssertionError(f"length {length}: audited AIR geometry changed")

    proofs = []
    for choice in (0, 1):
        case = assignment(length, choice, output_name)
        path = work / f"assignment-{length}-{choice}.json"
        path.write_text(json.dumps(case, sort_keys=True) + "\n")
        result = s31.trial(function_package, path, work / f"trial-{length}-{choice}")
        if (not result["native_verifier_accepted"] or
                not result["changed_public_statement_rejected"] or
                result["independent_value_oracle"]["status"] != "passed"):
            raise AssertionError(f"length {length}, choice {choice}: native proof gate failed")
        proofs.append({"choice": choice, "output": case["public_outputs"][output_name][0],
                       "proof_bytes": result["proof_bytes"]})
    return {
        "length": length,
        "canonical_ir_sha256": cost["canonical_ir_sha256"],
        "raw_qm31_rows": cost["raw"]["qm31_ops"],
        "padded_qm31_rows": cost["padded"]["qm31_ops"],
        "preprocessed_cells": cost["preprocessed_cells"],
        "proofs": proofs,
    }


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-functional-packing-") as directory:
        work = Path(directory)
        reports = [check_length(work, length) for length in LENGTHS]
    print(json.dumps({"schema": "s31-functional-packing-v1", "cases": reports},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
