#!/usr/bin/env python3
"""Native zero-cost gate for a higher-order static array map."""

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
            "qm31_ops": 321, "triple_xor": 0},
    "padded": {"blake_g": 0, "eq": 0, "m31_to_u32": 0,
               "qm31_ops": 512, "triple_xor": 0},
    "preprocessed_cells": 4096,
}


def main() -> None:
    example = S31 / "examples/functional/static_map"
    functional = example / "map.s31"
    manual = example / "manual.s31"
    assignment = example / "valid.json"
    relation, _ = compile_file(functional)
    direct, _ = compile_file(manual)
    if relation != direct:
        raise AssertionError("static map changed the normalized relation")
    if [node["op"] for node in relation["nodes"]] != ["mul", "mul", "array_concat"]:
        raise AssertionError("static map arithmetic graph changed")
    values = json.loads(assignment.read_text())
    expected = [word * word % ((1 << 31) - 1)
                for name in ("x", "y") for word in values["private_inputs"][name]]
    if values["public_outputs"] != {"out": expected}:
        raise AssertionError("static map fixture differs from independent M31 arithmetic")

    with tempfile.TemporaryDirectory(prefix="s31-static-map-") as temporary:
        work = Path(temporary)
        mapped_package = s31.build(functional, work / "mapped", "direct-gate")
        manual_package = s31.build(manual, work / "manual", "direct-gate")
        costs = [json.loads((package / "cost-report.json").read_text())
                 for package in (mapped_package, manual_package)]
        differing = [field for field in MATCHED_COST if costs[0][field] != costs[1][field]]
        if differing:
            raise AssertionError(f"static map changed direct-gate AIR geometry: {differing}")
        changed = [field for field, value in EXPECTED_GEOMETRY.items()
                   if costs[0][field] != value]
        if changed:
            raise AssertionError(f"static map baseline geometry changed: {changed}")
        trial = s31.trial(mapped_package, assignment, work / "trial")
        if (not trial["native_verifier_accepted"] or
                not trial["changed_public_statement_rejected"] or
                trial["independent_value_oracle"]["status"] != "passed"):
            raise AssertionError("static map proof or changed-claim control failed")
        print(json.dumps({
            "schema": "s31-static-map-acceptance-v1",
            "same_normalized_relation": True,
            "same_air_fields": list(MATCHED_COST),
            "profile": costs[0]["profile"],
            "raw": costs[0]["raw"],
            "padded": costs[0]["padded"],
            "preprocessed_cells": costs[0]["preprocessed_cells"],
            "proof_bytes": trial["proof_bytes"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": True,
        }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
