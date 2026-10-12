#!/usr/bin/env python3
"""Check optional native phase telemetry preserves the source-bound proof."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ACCEPTANCE = Path(__file__).resolve().parents[2] / "tests" / "acceptance" / "mixed_boundary"
sys.path.insert(0, str(ACCEPTANCE))
from source_pinned_general import build, family  # noqa: E402


def run(*args: str, phases: bool = False) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    env.pop("S31_MIXED_NATIVE_PHASES", None)
    if phases:
        env["S31_MIXED_NATIVE_PHASES"] = "1"
    result = subprocess.run(args, env=env, text=True, capture_output=True, check=False)
    if result.returncode:
        raise AssertionError(f"{args} failed: {result.stderr}")
    return result


def tagged(stderr: str, tag: str) -> dict:
    matches = [json.loads(line[len(tag) + 1:]) for line in stderr.splitlines()
               if line.startswith(tag + " ")]
    if len(matches) != 1:
        raise AssertionError(f"expected one {tag} record; saw {len(matches)}")
    return matches[0]


def check(count: int) -> dict:
    source, assignment = family(count)
    with tempfile.TemporaryDirectory(prefix="s31-mixed-phases-") as temporary:
        work = Path(temporary)
        source_path = work / "source.s31.json"
        assignment_path = work / "assignment.json"
        source_path.write_text(json.dumps(source, separators=(",", ":")))
        assignment_path.write_text(json.dumps(assignment, separators=(",", ":")))
        prover, verifier, _ = build(source_path, work / "build")
        outputs = []
        for label, phases in (("plain", False), ("timed", True)):
            proof = work / f"{label}.proof"
            statement = work / f"{label}.statement"
            result = run(str(prover), str(assignment_path), str(proof), str(statement),
                         phases=phases)
            run(str(verifier), str(proof), str(statement))
            stage = tagged(result.stderr, "S31_MIXED_STAGE_V1")
            native = stage["stages_ns"]["native_prove_including_setup_ns"]
            if native <= 0:
                raise AssertionError("missing native prove interval")
            if phases:
                timing = tagged(result.stderr, "S31_MIXED_NATIVE_PHASE_V1")
                if (timing["schema"] != "s31-mixed-native-phase-v1" or
                        timing["source_sha256"] != stage["source_sha256"] or
                        timing["circuit_identity_sha256"] != stage["circuit_identity_sha256"] or
                        timing["native_prove_including_setup_ns"] != native):
                    raise AssertionError("phase identity or native interval differs")
                interaction = timing["interaction_pow_ns"]
                fri = timing["fri_pow_ns"]
                pcs = timing["pcs_prove_ns"]
                if not (0 < interaction <= native and 0 < fri <= pcs <= native and
                        timing["prove_body_ns"] <= native and
                        timing["pcs_without_fri_pow_ns"] == pcs - fri and
                        timing["native_without_reported_pow_ns"] == native - interaction - fri):
                    raise AssertionError("phase accounting is inconsistent")
            elif "S31_MIXED_NATIVE_PHASE_V1" in result.stderr:
                raise AssertionError("ordinary prover emitted opt-in phase telemetry")
            outputs.append((proof.read_bytes(), statement.read_bytes()))
        if outputs[0] != outputs[1]:
            raise AssertionError("timing changed proof or statement bytes")
        return {"schema": "s31-mixed-phase-equivalence-v1", "calls": count,
                "source_sha256": hashlib.sha256(source_path.read_bytes()).hexdigest(),
                "proof_sha256": hashlib.sha256(outputs[0][0]).hexdigest(),
                "statement_sha256": hashlib.sha256(outputs[0][1]).hexdigest(),
                "proof_bytes": len(outputs[0][0]), "both_native_verified": True,
                "phase_accounting_checked": True}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--count", type=int, default=2, choices=range(1, 9))
    args = parser.parse_args()
    print(json.dumps(check(args.count), sort_keys=True))
