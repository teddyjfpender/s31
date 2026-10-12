#!/usr/bin/env python3
"""Prove a private M31 subtraction feeding the authenticated repeat chip."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import evaluate_relation


P = (1 << 31) - 1
SOURCE = {
    "version": 1, "name": "sub_feeder",
    "inputs": [
        {"name": "x", "kind": "m31", "length": 4, "visibility": "private"},
        {"name": "y", "kind": "m31", "length": 4, "visibility": "private"},
    ],
    "nodes": [
        {"name": "feeder", "op": "sub", "lhs": "x", "rhs": "y"},
        {"name": "step", "op": "repeat", "lhs": "feeder", "rounds": 16,
         "body": [{"op": "square"}, {"op": "add_const", "constant": 13}]},
        {"name": "out", "op": "add", "lhs": "step", "rhs": "x"},
    ],
    "assertions": [], "public_outputs": ["out"],
}


def run(*args: str, accepted: bool = True) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(args, capture_output=True, text=True, timeout=300)
    if (result.returncode == 0) != accepted or result.returncode < 0:
        raise AssertionError(f"unexpected exit {result.returncode}: {args}\n"
                             f"stdout={result.stdout}\nstderr={result.stderr}")
    return result


def main() -> None:
    x = [0, 1, P - 1, 7]
    y = [1, P - 1, P - 1, 11]
    current = [(a - b) % P for a, b in zip(x, y)]
    for _ in range(16):
        current = [(value * value + 13) % P for value in current]
    out = [(a + b) % P for a, b in zip(current, x)]
    assignment = {"public_inputs": {}, "private_inputs": {"x": x, "y": y},
                  "public_outputs": {"out": out}}
    if evaluate_relation(SOURCE, assignment) != assignment["public_outputs"]:
        raise AssertionError("independent field arithmetic disagrees with relation oracle")

    with tempfile.TemporaryDirectory(prefix="s31-sub-feeder-") as directory:
        work = Path(directory)
        source = work / "sub_feeder.s31.json"
        source.write_text(json.dumps(SOURCE, sort_keys=True, indent=2) + "\n")
        input_path = work / "assignment.json"
        input_path.write_text(json.dumps(assignment, sort_keys=True, indent=2) + "\n")
        prefix = work / "package"
        run("zig", "build", "--build-file", str(S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=1",
            "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source}",
            "-Ds31-name=sub_feeder", "-j2", "--prefix", str(prefix))
        binaries = prefix / "bin"
        prover = binaries / "s31-sub_feeder-mixed-general-prover"
        verifier = binaries / "s31-sub_feeder-mixed-general-native-verifier"
        manifest_bin = binaries / "s31-sub_feeder-mixed-general-manifest"
        manifest = json.loads(run(str(manifest_bin)).stdout)
        if (manifest["call_count"] != 1 or manifest["slot_count"] != 3 or
                manifest["source_sha256"] != hashlib.sha256(source.read_bytes()).hexdigest()):
            raise AssertionError("source-bound mixed component roster differs")
        proof = work / "proof.bin"
        statement = work / "statement.json"
        run(str(prover), str(input_path), str(proof), str(statement))
        run(str(verifier), str(proof), str(statement))
        changed = json.loads(statement.read_text())
        if changed["public_words"] != out + [0] * (8 - len(out)):
            raise AssertionError("native public statement changed the computed result")
        changed["public_words"][0] = (changed["public_words"][0] + 1) % P
        changed_path = work / "changed-statement.json"
        changed_path.write_text(json.dumps(changed, sort_keys=True, indent=2) + "\n")
        run(str(verifier), str(proof), str(changed_path), accepted=False)
        print(json.dumps({"schema": "s31-mixed-field-sub-feeder-v1",
                          "proof_bytes": proof.stat().st_size,
                          "component_slots": manifest["slot_count"],
                          "honest_proof_accepted": True,
                          "changed_claim_rejected": True}, sort_keys=True))


if __name__ == "__main__":
    main()
