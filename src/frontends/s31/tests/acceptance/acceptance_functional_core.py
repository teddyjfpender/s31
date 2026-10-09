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
        different = [name for name in MATCHED_COST
                     if functional_cost[name] != manual_cost[name]]
        if different:
            raise AssertionError(f"functional syntax changed circuit/AIR cost: {different}")
        changed_geometry = [name for name, expected in EXPECTED_GEOMETRY.items()
                            if functional_cost[name] != expected]
        if changed_geometry:
            raise AssertionError(f"functional baseline geometry changed: {changed_geometry}")
        trial = s31.trial(functional_package, assignment_path, work / "trial")
        if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
            raise AssertionError("native verifier acceptance or claim rejection missing")
        print(json.dumps({
            "schema": "s31-functional-core-acceptance-v1",
            "canonical_ir_sha256": functional_cost["canonical_ir_sha256"],
            "raw": functional_cost["raw"],
            "padded": functional_cost["padded"],
            "preprocessed_cells": functional_cost["preprocessed_cells"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": trial["changed_public_statement_rejected"],
        }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
