#!/usr/bin/env python3
"""Reconstruct one accepted transparent control proof's committed Gate trace.

This bounded diagnostic consumes a private assignment locally and reports only
commitment and component-match booleans. It does not authenticate the trace of
an arbitrary accepted proof independently of the installed PCS/FRI verifier.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.compiler.control_public_statement_audit import audit as statement_audit  # noqa: E402
SCHEMA = "s31-control-claim-trace-v1"
COUNTS = [329, 0, 5, 0]


def run_native(source: Path, assignment: Path, proof: Path, statement: Path,
               *, root: Path = ROOT) -> dict[str, object]:
    command = ["zig", "build", "--build-file", "scripts/compiler/control_claim_trace/build.zig",
               "audit", "-Doptimize=ReleaseFast", "-j4", "--",
               str(source), str(assignment), str(proof), str(statement)]
    result = subprocess.run(command, cwd=root, capture_output=True, text=True,
                            check=False, timeout=240)
    if result.returncode:
        raise ValueError("control claim trace audit: native reconstruction rejected: " +
                         result.stderr[-1600:])
    try:
        receipt = json.loads(result.stderr.strip().splitlines()[-1])
    except (IndexError, json.JSONDecodeError) as exc:
        raise ValueError("control claim trace audit: native receipt missing") from exc
    if receipt != {"schema": SCHEMA, "base_root_match": True,
                   "interaction_root_match": True,
                   "all_component_claims_match": True,
                   "producer_counts": COUNTS}:
        raise ValueError("control claim trace audit: native receipt changed")
    return receipt


def audit(package: Path, proof: Path, statement: Path, assignment: Path,
          lean_checker: Path, *, root: Path = ROOT) -> dict[str, object]:
    package, proof, statement, assignment = (path.resolve() for path in
                                             (package, proof, statement, assignment))
    prior = statement_audit(package, proof, statement, lean_checker)
    manifest = json.loads((package / "manifest.json").read_text())
    if manifest.get("name") != "control_air" or manifest.get("lowering") != "gate":
        raise ValueError("control claim trace audit: expected sealed control Gate package")
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD:deps/stwo-zig"], cwd=root, text=True).strip()
    checkout = subprocess.check_output(
        ["git", "-C", "deps/stwo-zig", "rev-parse", "HEAD"], cwd=root,
        text=True).strip()
    if revision != checkout:
        raise ValueError("control claim trace audit: engine checkout differs from gitlink")
    native = run_native(package / "source.s31.json", assignment, proof, statement,
                        root=root)
    return {
        **native,
        "program_sha256": prior["program_sha256"],
        "proof_sha256": prior["proof_sha256"],
        "statement_sha256": prior["statement_sha256"],
        "preprocessed_root": prior["preprocessed_root"],
        "engine_gitlink": revision,
        "native_verifier_accepted": prior["native_verifier_accepted"],
        "arbitrary_accepted_proof_trace_authenticated": False,
        "global_logup_soundness_proved": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("statement", type=Path)
    parser.add_argument("assignment", type=Path)
    parser.add_argument("--lean-checker", type=Path, default=(
        ROOT / "formal/s31/.lake/build/bin/s31-pure-field-derivation-bytes-check"))
    args = parser.parse_args()
    print(json.dumps(audit(args.package, args.proof, args.statement, args.assignment,
                           args.lean_checker), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
