#!/usr/bin/env python3
"""Finite accepted and adversarial controls for the control claim trace join."""

from __future__ import annotations

import argparse
import json
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.compiler.control_claim_trace_audit import audit, run_native  # noqa: E402


def controls(package: Path, proof: Path, statement: Path, assignment: Path,
             lean_checker: Path) -> dict[str, object]:
    accepted = audit(package, proof, statement, assignment, lean_checker)
    with tempfile.TemporaryDirectory(prefix="s31-control-claim-trace-") as directory:
        temporary = Path(directory)
        original = json.loads(assignment.read_text())
        private = original["private_inputs"]
        if set(private) != {"a", "b"} or len(private["a"]) != 4:
            raise ValueError("control claim trace controls: unexpected private fixture")
        changed = json.loads(assignment.read_text())
        changed["private_inputs"]["a"][0] = (private["a"][0] + 1) % (2**31 - 1)
        altered_assignment = temporary / "changed-unused-branch.json"
        altered_assignment.write_text(json.dumps(changed))
        try:
            run_native(package / "source.s31.json", altered_assignment, proof, statement)
        except ValueError as exc:
            if "reconstructed base cells differ from committed main root" not in str(exc):
                raise
        else:
            raise ValueError("control claim trace controls: altered private row accepted")
        raw = bytearray(proof.read_bytes())
        if raw[:8] != b"S31NAT1\0" or len(raw) < 32:
            raise ValueError("control claim trace controls: unexpected proof envelope")
        raw[16] = (raw[16] + 1) % 256
        altered_proof = temporary / "changed-interaction-claim.proof"
        altered_proof.write_bytes(raw)
        try:
            run_native(package / "source.s31.json", assignment, altered_proof, statement)
        except ValueError as exc:
            if "interaction claim differs from committed base-cell lookup reconstruction" not in str(exc):
                raise
        else:
            raise ValueError("control claim trace controls: altered component claim accepted")
    return {
        "schema": "s31-control-claim-trace-controls-v1",
        "accepted_proof": accepted["proof_sha256"],
        "changed_private_base_root_rejected": True,
        "changed_interaction_claim_rejected": True,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("statement", type=Path)
    parser.add_argument("assignment", type=Path)
    parser.add_argument("--lean-checker", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(controls(args.package.resolve(), args.proof.resolve(),
                              args.statement.resolve(), args.assignment.resolve(),
                              args.lean_checker.resolve()), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
