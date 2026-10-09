#!/usr/bin/env python3
"""Native selector proof and exact AIR-cost gate for total functional `if`."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from text_frontend import compile_file


MATCHED_COST = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)
EXPECTED_GEOMETRY = {
    "profile": "direct-m31-v4",
    "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
            "qm31_ops": 282, "triple_xor": 0},
    "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
               "qm31_ops": 512, "triple_xor": 0},
    "preprocessed_cells": 4096,
}


def main() -> None:
    example = S31 / "examples/control/total_if"
    conditional = example.with_suffix(".s31")
    manual = example.with_name("total_if_manual.s31")
    assignments = (example.with_suffix(".valid.json"),
                   example.with_suffix(".alternate.valid.json"))
    source_relation, _ = compile_file(conditional)
    manual_relation, _ = compile_file(manual)
    if [node["op"] for node in source_relation["nodes"]] != ["mul", "add_const", "select"]:
        raise AssertionError("conditional did not emit the two arms and one select")
    if [node["op"] for node in manual_relation["nodes"]] != ["mul", "add_const", "select"]:
        raise AssertionError("manual selector has different primitive operations")

    with tempfile.TemporaryDirectory(prefix="s31-total-if-") as directory:
        work = Path(directory)
        conditional_package = s31.build(conditional, work / "conditional", "direct-gate")
        manual_package = s31.build(manual, work / "manual", "direct-gate")
        cost = json.loads((conditional_package / "cost-report.json").read_text())
        manual_cost = json.loads((manual_package / "cost-report.json").read_text())
        different = [key for key in MATCHED_COST if cost[key] != manual_cost[key]]
        if different:
            raise AssertionError(f"if syntax changed circuit/AIR geometry: {different}")
        changed = [key for key, expected in EXPECTED_GEOMETRY.items()
                   if cost[key] != expected]
        if changed:
            raise AssertionError(f"conditional baseline geometry changed: {changed}")

        for bit, expected, assignment_path in ((1, 25, assignments[0]),
                                               (0, 10, assignments[1])):
            assignment = json.loads(assignment_path.read_text())
            if assignment["public_inputs"]["choice"] != [bit] or assignment["public_outputs"] != {"result": [expected]}:
                raise AssertionError("conditional fixture differs from independent arithmetic")
            trial = s31.trial(conditional_package, assignment_path, work / f"trial-{bit}")
            if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
                raise AssertionError(f"native verifier did not enforce choice={bit} statement")

        print(json.dumps({
            "schema": "s31-total-if-acceptance-v1",
            "canonical_ir_sha256": cost["canonical_ir_sha256"],
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "both_choices_verified": True,
            "changed_public_statements_rejected": True,
        }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
