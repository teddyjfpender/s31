#!/usr/bin/env python3
"""Prove and challenge a subtraction result in a short final SIMD row."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from text_frontend import compile_text  # noqa: E402


P = (1 << 31) - 1
SOURCE = """circuit subtract5(private a: [m31; 5], private b: [m31; 5]) -> public [m31; 5] {
    let out = a - b;
    out
}
"""
LEFT = [0, 1, P - 1, 7, 123456789]
RIGHT = [1, P - 1, P - 1, 11, 9876]


def run() -> dict:
    relation, _ = compile_text(SOURCE)
    if [node["op"] for node in relation["nodes"]] != ["sub"]:
        raise AssertionError("five-lane field subtraction did not remain one relation node")
    expected = [(a - b) % P for a, b in zip(LEFT, RIGHT)]
    assignment = {"public_inputs": {}, "private_inputs": {"a": LEFT, "b": RIGHT},
                  "public_outputs": {"out": expected}}
    if evaluate_relation(relation, assignment) != assignment["public_outputs"]:
        raise AssertionError("independent modular oracle disagrees")

    with tempfile.TemporaryDirectory(prefix="s31-field-sub-partial-") as directory:
        work = Path(directory)
        source = work / "subtract5.s31"
        source.write_text(SOURCE)
        package = s31.build(source, work / "package", "direct-gate")
        assignment_path = work / "assignment.json"
        s31.write_json(assignment_path, assignment)
        trial_dir = work / "trial"
        trial = s31.trial(package, assignment_path, trial_dir)
        cost = json.loads((package / "cost-report.json").read_text())
        if cost["profile"] != "direct-m31-v4":
            raise AssertionError("five-lane subtraction selected the wrong AIR profile")
        if (not trial["native_verifier_accepted"] or
                trial["changed_public_statement_rejected"] != "public_outputs.out[0]" or
                trial["independent_value_oracle"]["status"] != "passed"):
            raise AssertionError("native proof, first-lane mutation, or oracle failed")

        statement = json.loads((trial_dir / "statement.json").read_text())
        if statement["public_outputs"]["out"] != expected:
            raise AssertionError("native statement changed the fifth output lane")
        statement["public_outputs"]["out"][4] = (expected[4] + 1) % P
        changed = work / "fifth-lane-changed-statement.json"
        s31.write_json(changed, statement)
        name = json.loads((package / "manifest.json").read_text())["name"]
        verifier = package / "bin" / f"s31-{name}-native-verifier"
        try:
            s31.invoke(str(verifier), str(trial_dir / "proof.bin"), str(changed),
                       str(package / "verification-key.json"))
        except RuntimeError:
            pass
        else:
            raise AssertionError("native verifier accepted a changed fifth-lane claim")

        return {"schema": "s31-field-subtraction-partial-native-v1",
                "profile": cost["profile"], "source_words": 5,
                "raw_qm31_rows": cost["raw"]["qm31_ops"],
                "padded_qm31_rows": cost["padded"]["qm31_ops"],
                "proof_bytes": trial["proof_bytes"],
                "honest_proof_accepted": True,
                "changed_first_lane_rejected": True,
                "changed_fifth_lane_rejected": True,
                "independent_oracle_passed": True}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
