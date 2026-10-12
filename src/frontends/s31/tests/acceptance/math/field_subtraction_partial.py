#!/usr/bin/env python3
"""Prove a zero-cost functional subtraction across a short final SIMD row."""

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
FUNCTIONAL_SOURCE = """fn difference(x: [m31; 5], y: [m31; 5]) -> [m31; 5] { x - y }
circuit subtract5(private a: [m31; 5], private b: [m31; 5]) -> public [m31; 5] {
    let out = difference(a, b);
    out
}
"""
MATCHED_COST = (
    "canonical_ir_sha256", "profile", "chip", "raw", "padded",
    "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
    "input_packing", "public_binding", "finalization", "fri",
)
LEFT = [0, 1, P - 1, 7, 123456789]
RIGHT = [1, P - 1, P - 1, 11, 9876]


def run() -> dict:
    relation, _ = compile_text(SOURCE)
    functional_relation, _ = compile_text(FUNCTIONAL_SOURCE)
    if functional_relation != relation:
        raise AssertionError("named subtraction helper changed normalized relation IR")
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
        functional_source = work / "subtract5-functional.s31"
        functional_source.write_text(FUNCTIONAL_SOURCE)
        direct_package = s31.build(source, work / "direct-package", "direct-gate")
        package = s31.build(functional_source, work / "functional-package", "direct-gate")
        direct_cost = json.loads((direct_package / "cost-report.json").read_text())
        cost = json.loads((package / "cost-report.json").read_text())
        different = [key for key in MATCHED_COST if cost[key] != direct_cost[key]]
        if different:
            raise AssertionError(f"functional helper changed AIR geometry: {different}")
        assignment_path = work / "assignment.json"
        s31.write_json(assignment_path, assignment)
        trial_dir = work / "trial"
        trial = s31.trial(package, assignment_path, trial_dir)
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

        return {"schema": "s31-field-subtraction-partial-native-v2",
                "profile": cost["profile"], "source_words": 5,
                "raw_qm31_rows": cost["raw"]["qm31_ops"],
                "padded_qm31_rows": cost["padded"]["qm31_ops"],
                "proof_bytes": trial["proof_bytes"],
                "functional_ir_and_geometry_equal": True,
                "honest_proof_accepted": True,
                "changed_first_lane_rejected": True,
                "changed_fifth_lane_rejected": True,
                "independent_oracle_passed": True}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
