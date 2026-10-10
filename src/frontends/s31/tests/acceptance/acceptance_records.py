#!/usr/bin/env python3
"""Native proof and exact AIR-cost gate for nominal source records."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from oracle import OracleError, evaluate_relation
from text_frontend import compile_file


MATCHED_COST = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)


def check_case(work: Path, source: Path, *, expected_nodes: list[str]) -> dict:
    manual = source.with_name(source.stem + "_manual.s31")
    assignment_path = source.with_suffix(".valid.json")
    relation, _ = compile_file(source)
    manual_relation, _ = compile_file(manual)
    if relation != manual_relation:
        raise AssertionError(f"{source.name}: record changed the normalized relation")
    if [node["op"] for node in relation["nodes"]] != expected_nodes:
        raise AssertionError(f"{source.name}: changed computation nodes")
    assignment = json.loads(assignment_path.read_text())
    if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
        raise AssertionError(f"{source.name}: independent oracle rejected valid assignment")
    output_name = next(iter(assignment["public_outputs"]))
    false_claim = json.loads(assignment_path.read_text())
    false_claim["public_outputs"][output_name][0] ^= 1
    try:
        evaluate_relation(relation, false_claim)
    except OracleError:
        pass
    else:
        raise AssertionError(f"{source.name}: oracle accepted a false public result")

    packages = {
        label: s31.build(path, work / f"{source.stem}-{label}", "direct-gate")
        for label, path in (("record", source), ("manual", manual))
    }
    costs = {label: json.loads((package / "cost-report.json").read_text())
             for label, package in packages.items()}
    if any(costs["record"][field] != costs["manual"][field] for field in MATCHED_COST):
        raise AssertionError(f"{source.name}: record changed circuit or AIR cost")
    cost = costs["record"]
    if (cost["profile"] != "direct-m31-v4" or cost["raw"]["eq"] != 0 or
            cost["raw"]["m31_to_u32"] != 0):
        raise AssertionError(f"{source.name}: expected arithmetic-only proof profile")
    trial = s31.trial(packages["record"], assignment_path,
                      work / f"{source.stem}-trial")
    if (not trial["native_verifier_accepted"] or
            not trial["changed_public_statement_rejected"] or
            trial["independent_value_oracle"]["status"] != "passed"):
        raise AssertionError(f"{source.name}: native proof control failed")
    return {
        "source": source.name,
        "same_normalized_relation": True,
        "same_cost_fields": list(MATCHED_COST),
        "canonical_ir_sha256": cost["canonical_ir_sha256"],
        "profile": cost["profile"],
        "raw": cost["raw"],
        "padded": cost["padded"],
        "preprocessed_cells": cost["preprocessed_cells"],
        "proof_bytes": trial["proof_bytes"],
        "native_verifier_accepted": True,
        "changed_public_statement_rejected": True,
        "false_claim_rejected_by_oracle": True,
    }


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-acceptance-") as temporary:
        work = Path(temporary)
        cases = [
            check_case(work, S31 / "examples/arithmetic/record_square_sum.s31",
                       expected_nodes=["mul", "add", "add"]),
            check_case(work, S31 / "examples/math/division/record_i32_division.s31",
                       expected_nodes=["int_view", "int_view", "int_div_rem",
                                       "array_slice", "array_slice", "int_view", "int_view"]),
        ]
    print(json.dumps({"schema": "s31-record-native-acceptance-v1", "cases": cases},
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
