#!/usr/bin/env python3
"""Native proof and exact AIR-cost gate for source-only product parameters."""

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
EXPECTED = {
    "direct-gate": {
        "profile": "direct-m31-v4",
        "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                "qm31_ops": 277, "triple_xor": 0},
        "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
                   "qm31_ops": 512, "triple_xor": 0},
        "preprocessed_cells": 4096,
    },
    "gate": {
        "profile": "circuit-v1",
        "raw": {"blake_g": 0, "eq": 0, "m31_to_u32": 3,
                "qm31_ops": 277, "triple_xor": 0},
        "padded": {"blake_g": 16, "eq": 16, "m31_to_u32": 16,
                   "qm31_ops": 512, "triple_xor": 16},
        "preprocessed_cells": 4_248_656,
    },
}


def main() -> None:
    example = S31 / "examples/functional/pattern_parameters"
    functional = example / "weighted.s31"
    manual = example / "weighted_manual.s31"
    assignment = example / "weighted.valid.json"
    relation, _ = compile_file(functional)
    reference, _ = compile_file(manual)
    if relation != reference:
        raise AssertionError("pattern parameter changed the normalized relation")
    if [node["op"] for node in relation["nodes"]] != ["mul", "add"]:
        raise AssertionError("weighted example must emit exactly mul and add")
    values = json.loads(assignment.read_text())
    x = values["public_inputs"]["x"][0]
    y = values["public_inputs"]["y"][0]
    if values["public_outputs"] != {"result": [(x * y + x) % ((1 << 31) - 1)]}:
        raise AssertionError("fixture differs from independent field arithmetic")

    reports = {}
    with tempfile.TemporaryDirectory(prefix="s31-pattern-parameters-") as temporary:
        work = Path(temporary)
        for profile in ("direct-gate", "gate"):
            packages = {
                "pattern": s31.build(functional, work / f"{profile}-pattern", profile),
                "manual": s31.build(manual, work / f"{profile}-manual", profile),
            }
            costs = {name: json.loads((package / "cost-report.json").read_text())
                     for name, package in packages.items()}
            differing = [field for field in MATCHED_COST
                         if costs["pattern"][field] != costs["manual"][field]]
            if differing:
                raise AssertionError(f"pattern parameter changed {profile} AIR: {differing}")
            changed_baseline = [field for field, value in EXPECTED[profile].items()
                                if costs["pattern"][field] != value]
            if changed_baseline:
                raise AssertionError(f"{profile} baseline geometry changed: {changed_baseline}")
            trial = s31.trial(packages["pattern"], assignment, work / f"{profile}-trial")
            if (not trial["native_verifier_accepted"] or
                    not trial["changed_public_statement_rejected"] or
                    trial["independent_value_oracle"]["status"] != "passed"):
                raise AssertionError(f"{profile} verifier or oracle control failed")
            reports[profile] = {
                "canonical_ir_sha256": costs["pattern"]["canonical_ir_sha256"],
                "raw": costs["pattern"]["raw"],
                "padded": costs["pattern"]["padded"],
                "preprocessed_cells": costs["pattern"]["preprocessed_cells"],
                "proof_bytes": trial["proof_bytes"],
                "native_verifier_accepted": True,
                "changed_public_statement_rejected": True,
            }
    print(json.dumps({"schema": "s31-pattern-parameters-acceptance-v1",
                      "same_normalized_relation": True,
                      "same_air_fields": list(MATCHED_COST),
                      "profiles": reports}, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
