#!/usr/bin/env python3
"""Native proof and AIR-cost gate for an ignored total static-sum payload."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31
from text_frontend import compile_text


P = (1 << 31) - 1
STEP = "fn step(v: [m31; 4]) -> [m31; 4] { v .* v + splat<4>(7_m31) }\n"
CIRCUIT = "circuit p(public x: [m31; 4]) -> public [m31; 4] {\n"
WRAPPED = ("enum Choice { Left: [m31; 4], Right: [m31; 4] }\n" + STEP + CIRCUIT +
           "    let ignored = Choice::Left(x .* x);\n"
           "    let result = iterate<16>(step, x);\n"
           "    result\n}\n")
DIRECT = STEP + CIRCUIT + "    let result = iterate<16>(step, x);\n    result\n}\n"
COST_FIELDS = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)


def run() -> dict:
    wrapped_relation, wrapped_map = compile_text(WRAPPED)
    direct_relation, _ = compile_text(DIRECT)
    if wrapped_relation != direct_relation or wrapped_relation["nodes"] != [{
        "name": "result", "op": "repeat", "lhs": "x", "rounds": 16,
        "body": [{"op": "square"}, {"op": "add_const", "constant": 7}],
    }]:
        raise AssertionError("unused total enum payload changed the one-node chip relation")
    if set(wrapped_map) != {"result"}:
        raise AssertionError("source map still contains a removed payload node")

    inputs = [0, 1, 2, 7]
    expected = inputs[:]
    for _ in range(16):
        expected = [(value * value + 7) % P for value in expected]
    assignment = {"public_inputs": {"x": inputs}, "private_inputs": {},
                  "public_outputs": {"result": expected}}

    with tempfile.TemporaryDirectory(prefix="s31-static-sum-dce-") as directory:
        work = Path(directory)
        wrapped_source = work / "wrapped.s31"
        direct_source = work / "direct.s31"
        assignment_path = work / "assignment.json"
        wrapped_source.write_text(WRAPPED)
        direct_source.write_text(DIRECT)
        assignment_path.write_text(json.dumps(assignment, sort_keys=True) + "\n")

        wrapped_package = s31.build(wrapped_source, work / "wrapped-package", "direct-chip")
        direct_package = s31.build(direct_source, work / "direct-package", "direct-chip")
        wrapped_cost = json.loads((wrapped_package / "cost-report.json").read_text())
        direct_cost = json.loads((direct_package / "cost-report.json").read_text())
        mismatches = [field for field in COST_FIELDS if wrapped_cost[field] != direct_cost[field]]
        if mismatches:
            raise AssertionError(f"static enum abstraction changed native AIR geometry: {mismatches}")
        if wrapped_cost["chip"] is None:
            raise AssertionError("dedicated repeat chip was not selected")

        trial = s31.trial(wrapped_package, assignment_path, work / "trial")
        if (not trial["native_verifier_accepted"] or
                not trial["changed_public_statement_rejected"] or
                trial["independent_value_oracle"]["status"] != "passed"):
            raise AssertionError("static-sum chip proof, oracle, or changed-claim rejection failed")
        return {
            "canonical_ir_sha256": wrapped_cost["canonical_ir_sha256"],
            "profile": wrapped_cost["profile"], "chip": wrapped_cost["chip"],
            "raw": wrapped_cost["raw"], "padded": wrapped_cost["padded"],
            "preprocessed_cells": wrapped_cost["preprocessed_cells"],
            "proof_bytes": trial["proof_bytes"],
            "native_verifier_accepted": True,
            "changed_public_statement_rejected": True,
            "equal_native_air_geometry": True,
        }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
