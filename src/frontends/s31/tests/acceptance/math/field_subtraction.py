#!/usr/bin/env python3
"""Compare native one-gate M31 subtraction with the old negation-plus-add form."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31
from oracle import evaluate_relation
from text_frontend import compile_text


P = (1 << 31) - 1
HEADER = "circuit subtract(private a: [m31; 4], private b: [m31; 4]) -> public [m31; 4] {\n"
SOURCES = {
    "native": HEADER + "    let out = a - b;\n    out\n}\n",
    "expanded": HEADER + "    let minus_b = std::math::neg(b);\n"
                 "    let out = a + minus_b;\n    out\n}\n",
}
ASSIGNMENTS = (
    ([0, 1, P - 1, 7], [1, P - 1, P - 1, 11]),
    ([P - 1, 0, 1234567, P - 2], [P - 1, 1, 7654321, 0]),
)


def run() -> dict:
    with tempfile.TemporaryDirectory(prefix="s31-field-sub-") as directory:
        work = Path(directory)
        costs: dict[str, dict] = {}
        proofs: dict[str, list[int]] = {}
        for form, source in SOURCES.items():
            source_path = work / f"{form}.s31"
            source_path.write_text(source)
            relation, _ = compile_text(source, str(source_path))
            operations = [node["op"] for node in relation["nodes"]]
            if operations != (["sub"] if form == "native" else ["mul_const", "add"]):
                raise AssertionError(f"{form}: unexpected residual operations {operations}")
            package = s31.build(source_path, work / form, "direct-gate")
            cost = json.loads((package / "cost-report.json").read_text())
            if cost["profile"] != "direct-m31-v4":
                raise AssertionError(f"{form}: expected direct M31 profile")
            costs[form] = cost
            proofs[form] = []
            for index, (left, right) in enumerate(ASSIGNMENTS):
                expected = [(a - b) % P for a, b in zip(left, right)]
                assignment = {"public_inputs": {}, "private_inputs": {"a": left, "b": right},
                              "public_outputs": {"out": expected}}
                if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
                    raise AssertionError(f"{form}: independent modular oracle disagrees")
                assignment_path = work / f"{form}-{index}.json"
                s31.write_json(assignment_path, assignment)
                trial = s31.trial(package, assignment_path, work / f"{form}-{index}-trial")
                if (not trial["native_verifier_accepted"] or
                        not trial["changed_public_statement_rejected"] or
                        trial["independent_value_oracle"]["status"] != "passed"):
                    raise AssertionError(f"{form}: native proof or changed-claim control failed")
                proofs[form].append(trial["proof_bytes"])
        native, expanded = costs["native"], costs["expanded"]
        if native["raw"]["qm31_ops"] >= expanded["raw"]["qm31_ops"]:
            raise AssertionError("one-node subtraction did not reduce native QM31 rows")
        if native["padded"] != expanded["padded"]:
            raise AssertionError("unexpected padded-trace change in this small fixture")
        return {"schema": "s31-field-subtraction-native-v1",
                "native_raw": native["raw"], "expanded_raw": expanded["raw"],
                "native_proof_bytes": proofs["native"],
                "expanded_proof_bytes": proofs["expanded"],
                "honest_proofs_accepted": 4, "changed_claims_rejected": 4}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
