#!/usr/bin/env python3
"""Honest package and native proof for independently checked record source."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from package.record_source_fragment import (  # noqa: E402
    CAPABILITY, check_package_record_source_relation, parse_record_source_fragment,
)
from package.verify import verify_package  # noqa: E402
from text_frontend import compile_text  # noqa: E402

SOURCE = """struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let p = x.left .* y.right;
    let q = p + x.right;
    Pair { right: x.right, left: q }
}
"""
ASSIGNMENT = {
    "public_inputs": {"_s31_abi_input_0": [2], "_s31_abi_input_1": [3]},
    "private_inputs": {"_s31_abi_input_2": [5], "_s31_abi_input_3": [7]},
    "public_outputs": {"q": [17], "_s31_abi_input_1": [3]},
}
EXPECTED_LEAVES = [
    ("x.left", [2]), ("x.right", [3]),
    ("result.left", [17]), ("result.right", [3]),
]


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def source_derived_leaves(relation: dict, assignment: dict) -> list[tuple[str, list[int]]]:
    roots = [root for root in relation["public_abi"]["inputs"]
             if root["visibility"] == "public"] + [relation["public_abi"]["result"]]
    result: list[tuple[str, list[int]]] = []
    for root in roots:
        for leaf in root["leaves"]:
            path = ".".join(str(next(iter(part.values()))) for part in leaf["path"])
            category = "public_outputs" if root["name"] == "result" else "public_inputs"
            result.append((path, assignment[category][leaf["wire"]]))
    return result


def run() -> dict:
    source_bytes = SOURCE.encode()
    checked_relation = parse_record_source_fragment(source_bytes)
    compiled_relation, _ = compile_text(SOURCE)
    if checked_relation != compiled_relation:
        raise AssertionError("independent record relation differs from production compiler")
    if source_derived_leaves(checked_relation, ASSIGNMENT) != EXPECTED_LEAVES:
        raise AssertionError("source-derived public statement order differs from hand computation")
    if 2 * 7 + 3 != 17:
        raise AssertionError("hand computation fixture is wrong")

    with tempfile.TemporaryDirectory(prefix="s31-record-source-fragment-") as temporary:
        work = Path(temporary)
        source_path = work / "mix.s31"
        source_path.write_bytes(source_bytes)
        package = s31.build(source_path, work / "package", "direct-gate")
        verify_package(package)
        audit = check_package_record_source_relation(package)
        if audit["capability"] != CAPABILITY:
            raise AssertionError("record source audit returned the wrong capability")
        relation = json.loads((package / "source.s31.json").read_bytes())
        if relation != checked_relation:
            raise AssertionError("built relation differs from independent source parse")
        assignment_path = work / "assignment.json"
        assignment_path.write_bytes(canonical(ASSIGNMENT))
        trial_dir = work / "trial"
        trial = s31.trial(package, assignment_path, trial_dir)
        if (trial["native_verifier_accepted"] is not True or
                trial["independent_value_oracle"]["status"] != "passed"):
            raise AssertionError("native proof or independent value oracle failed")
        statement = json.loads((trial_dir / "statement.json").read_bytes())
        actual_leaves = [
            (".".join(str(next(iter(part.values()))) for part in leaf["path"]), leaf["words"])
            for leaf in statement["leaves"]
        ]
        if (statement["version"] != 2 or actual_leaves != EXPECTED_LEAVES or
                statement["abi_sha256"] != json.loads((package / "public-abi.json").read_bytes())
                ["boundary_sha256"]):
            raise AssertionError("native proof statement differs from checked field order")

        # Change a nonaliased public result so the typed statement remains
        # well formed. Rejection must occur at proof binding, after ABI parsing.
        changed = json.loads((trial_dir / "statement.json").read_bytes())
        changed["leaves"][2]["words"] = [18]
        changed_path = work / "changed-valid-statement.json"
        changed_path.write_bytes(canonical(changed))
        verifier = package / "bin" / "s31-mix-native-verifier"
        failure = subprocess.run(
            (str(verifier), str(trial_dir / "proof.bin"), str(changed_path),
             str(package / "verification-key.json")),
            capture_output=True, text=True, check=False,
        )
        if (failure.returncode != 1 or "error:" not in failure.stderr or
                any(label in failure.stderr for label in
                    ("InvalidRecordStatement", "InvalidRecordAbi", "InvalidVerificationKey", "panic:"))):
            raise AssertionError("ABI-valid changed claim did not fail native proof binding: " +
                                 failure.stderr[-1000:])
        return {"schema": "s31-record-source-fragment-native-v2",
                "capability": audit["capability"],
                "source_sha256": audit["source_sha256"],
                "relation_sha256": audit["relation_sha256"],
                "abi_sha256": statement["abi_sha256"],
                "public_words": [2, 3, 17, 3, 0, 0, 0, 0],
                "native_verifier_accepted": True,
                "abi_valid_changed_claim_rejected_by_proof": True,
                "proof_bytes": trial["proof_bytes"]}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
