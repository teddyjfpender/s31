#!/usr/bin/env python3
"""Check an honestly reconstructed v1 transparent Gate proof trace.

This diagnostic accepts any sealed S31 v1 Gate program on the legacy,
single-fold profile. It compares a supplied witness reconstruction with one
accepted proof. It does not turn PCS/FRI acceptance into a global trace theorem.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.verify import verify_package  # noqa: E402
from scripts.compiler.control_claim_trace_audit import run_native  # noqa: E402


def _digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(package: Path, proof: Path, statement: Path, assignment: Path,
          *, root: Path = ROOT) -> dict[str, object]:
    package, proof, statement, assignment = (path.resolve() for path in
                                             (package, proof, statement, assignment))
    verify_package(package)
    manifest = json.loads((package / "manifest.json").read_text())
    source = json.loads((package / "source.s31.json").read_text())
    key = json.loads((package / "verification-key.json").read_text())
    if (manifest.get("lowering") != "gate" or source.get("version") != 1 or
            source.get("proof_mode", "transparent") != "transparent" or
            manifest.get("channel_profile", "legacy") != "legacy" or
            manifest.get("fri_fold_step") != 1 or
            key.get("profile") != "circuit-v1" or key.get("chip") is not None or
            key.get("fri") != {"fold_step": 1, "last_layer_degree_bound": 1,
                               "log_blowup_factor": 1, "pow_bits": 26,
                               "queries": 70}):
        raise ValueError("Gate claim trace audit: unsupported source or proof profile")
    revision = subprocess.check_output(
        ["git", "rev-parse", "HEAD:deps/stwo-zig"], cwd=root, text=True).strip()
    checkout = subprocess.check_output(
        ["git", "-C", "deps/stwo-zig", "rev-parse", "HEAD"], cwd=root,
        text=True).strip()
    if revision != checkout:
        raise ValueError("Gate claim trace audit: engine checkout differs from gitlink")
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    sealed_paths = (package / "manifest.json", package / "source.s31.json",
                    package / "verification-key.json", verifier,
                    assignment, proof, statement)
    sealed_digests = tuple(_digest(path) for path in sealed_paths)
    proof_digest = _digest(proof)
    statement_digest = _digest(statement)
    accepted = subprocess.run((str(verifier), str(proof), str(statement),
                               str(package / "verification-key.json")),
                              capture_output=True, text=True, check=False, timeout=120)
    if (accepted.returncode != 0 or "native verification accepted" not in
            accepted.stdout + accepted.stderr):
        raise ValueError("Gate claim trace audit: packaged native verifier rejected proof")
    native = run_native(package / "source.s31.json", assignment, proof, statement,
                        root=root, expected_counts=None)
    verify_package(package)
    if tuple(_digest(path) for path in sealed_paths) != sealed_digests:
        raise ValueError("Gate claim trace audit: package or inputs changed during audit")
    return {
        "schema": "s31-gate-claim-trace-audit-v1",
        "program_sha256": manifest["program_sha256"],
        "proof_sha256": proof_digest,
        "statement_sha256": statement_digest,
        "engine_gitlink": revision,
        "producer_counts": native["producer_counts"],
        "source_nodes_mapped": native["source_nodes_mapped"],
        "source_semantics_match": True,
        "base_root_match": True,
        "interaction_root_match": True,
        "all_component_claims_match": True,
        "native_verifier_accepted": True,
        "arbitrary_accepted_proof_trace_authenticated": False,
        "global_logup_soundness_proved": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("statement", type=Path)
    parser.add_argument("assignment", type=Path)
    args = parser.parse_args()
    print(json.dumps(audit(args.package, args.proof, args.statement, args.assignment),
                     indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
