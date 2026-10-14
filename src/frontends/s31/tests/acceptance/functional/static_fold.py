#!/usr/bin/env python3
"""Native proof and complete AIR-cost gate for a captured static left fold."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
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
            "qm31_ops": 318, "triple_xor": 0},
    "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
               "qm31_ops": 512, "triple_xor": 0},
    "preprocessed_cells": 4096,
}
P = (1 << 31) - 1


def main() -> None:
    example = S31 / "examples/functional/static_fold"
    folded = example / "horner.s31"
    manual = example / "manual.s31"
    assignment = example / "valid.json"
    folded_relation, _ = compile_file(folded)
    manual_relation, _ = compile_file(manual)
    operations = ["mul", "add", "mul", "add"]
    if ([node["op"] for node in folded_relation["nodes"]] != operations or
            [node["op"] for node in manual_relation["nodes"]] != operations):
        raise AssertionError("Horner relation arithmetic changed")
    values = json.loads(assignment.read_text())
    private = values["private_inputs"]
    expected = [((a * x + b) * x + c) % P for x, a, b, c in zip(
        private["x"], private["a"], private["b"], private["c"])]
    if values["public_outputs"] != {"out": expected}:
        raise AssertionError("Horner assignment differs from independent field arithmetic")

    with tempfile.TemporaryDirectory(prefix="s31-static-fold-") as temporary:
        work = Path(temporary)
        packages = {
            "folded": s31.build(folded, work / "folded", "direct-gate"),
            "manual": s31.build(manual, work / "manual", "direct-gate"),
        }
        costs = {name: json.loads((package / "cost-report.json").read_text())
                 for name, package in packages.items()}
        different = [field for field in MATCHED_COST
                     if costs["folded"][field] != costs["manual"][field]]
        if different:
            raise AssertionError(f"static fold changed canonical IR or AIR geometry: {different}")
        changed = [field for field, expected in EXPECTED_GEOMETRY.items()
                   if costs["folded"][field] != expected]
        if changed:
            raise AssertionError(f"static fold baseline AIR geometry changed: {changed}")
        trial = s31.trial(packages["folded"], assignment, work / "trial")
        if (not trial["native_verifier_accepted"] or
                not trial["changed_public_statement_rejected"] or
                trial["independent_value_oracle"]["status"] != "passed"):
            raise AssertionError("static fold native proof or changed-claim control failed")
        print(json.dumps({
            "schema": "s31-static-fold-acceptance-v1",
            "same_canonical_ir_sha256": True,
            "canonical_ir_sha256": costs["folded"]["canonical_ir_sha256"],
            "same_air_fields": list(MATCHED_COST),
            "profile": costs["folded"]["profile"],
            "raw": costs["folded"]["raw"],
            "padded": costs["folded"]["padded"],
            "preprocessed_cells": costs["folded"]["preprocessed_cells"],
            "proof_bytes": trial["proof_bytes"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": True,
        }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
