#!/usr/bin/env python3
"""Strict proof verification for the bounded M31 structural release class.

This entry point requires an externally pinned Lean checker and package. It
does not admit record-v2, non-M31, or source syntax outside the Lean checker.
It lives outside the compiler fingerprint roster so adding the independent
gate does not change native compiler identities or sealed fixed-row fixtures.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.context import invoke  # noqa: E402
from package.lean_effects_admission import _pinned_checker  # noqa: E402
from package.source_relation_fragment import (  # noqa: E402
    LEAN_EFFECTS_PROFILE, check_source_relation_certificate,
)
from package.trust import admitted_snapshot  # noqa: E402
from runtime.proof_inputs import proof_inputs_snapshot  # noqa: E402

REQUIRED = ("source.s31", "source.s31.json", "public-abi.json",
            "source-relation-certificate.json", "typed-structural-derivation.json")
MAX_TEXT = 65536
MAX_TREE = 131072


def check_structural_snapshot(snapshot: Path, manifest: dict,
                              checker: Path) -> None:
    """Run Lean before any native proof or key verification on this snapshot."""
    if (manifest.get("lowering") != "direct-gate" or
            type(manifest.get("text_frontend_version")) is not int or
            manifest["text_frontend_version"] != 1 or
            "source_text_sha256" not in manifest):
        raise ValueError("structural release requires a direct-gate text package")
    artifacts = manifest.get("artifacts")
    if not isinstance(artifacts, dict) or not set(REQUIRED).issubset(artifacts):
        raise ValueError("structural release requires every source, tree, relation, and ABI artifact")
    source, relation, abi, certificate, tree = (snapshot / name for name in REQUIRED)
    for path, limit in ((source, 16384), (relation, MAX_TEXT), (abi, MAX_TEXT),
                        (certificate, MAX_TEXT), (tree, MAX_TREE)):
        if not path.is_file() or path.stat().st_size > limit:
            raise ValueError(f"structural release artifact is missing or oversized: {path.name}")
    relation_json = json.loads(relation.read_bytes())
    if type(relation_json) is not dict or type(relation_json.get("version")) is not int or \
            relation_json["version"] != 1:
        raise ValueError("structural release admits only normalized relation v1")
    checked = check_source_relation_certificate(
        source.read_bytes(), relation.read_bytes(), certificate.read_bytes())
    if (checked.get("lean_semantic_profile") != LEAN_EFFECTS_PROFILE or
            checked.get("unmodeled_features") != []):
        raise ValueError("structural release requires the bounded M31 effects profile")
    try:
        result = subprocess.run(
            [str(checker), str(source), str(tree), str(certificate),
             str(relation), str(abi)],
            capture_output=True, text=True, timeout=30, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ValueError("pinned Lean structural checker did not complete") from exc
    if result.returncode or result.stdout.strip() != "accepted: structural tree/source/relation/public ABI":
        detail = (result.stderr + result.stdout).strip()[:512]
        raise ValueError(f"Lean structural package check rejected: {detail}")


def verify(package: Path, proof: Path, statement: Path | None,
           pins: dict[str, str], checker_path: Path, checker_sha256: str) -> str:
    """Require Lean acceptance, then run the native verifier on the same copy."""
    with proof_inputs_snapshot(proof, statement) as (captured_proof, captured_statement):
        with _pinned_checker(checker_path, checker_sha256) as checker:
            with admitted_snapshot(package, pins) as (snapshot, manifest):
                check_structural_snapshot(snapshot, manifest, checker)
                verifier = snapshot / "bin" / f"s31-{manifest['name']}-native-verifier"
                key = snapshot / "verification-key.json"
                if json.loads(key.read_bytes()).get("schema") != \
                        "s31-verification-key-direct-manifest-v2":
                    raise ValueError("structural release requires a v2 direct-gate key")
                invoke(str(verifier), "check-key", str(key))
                return invoke(str(verifier), str(captured_proof),
                              str(captured_statement), str(key))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("--statement", type=Path)
    parser.add_argument("--lean-checker", type=Path, required=True)
    parser.add_argument("--lean-checker-sha256", required=True)
    for kind in ("source", "key", "prover", "verifier", "text"):
        parser.add_argument(f"--{kind}-sha256", required=True)
    args = parser.parse_args(argv)
    pins = {kind: getattr(args, f"{kind}_sha256") for kind in
            ("source", "key", "prover", "verifier", "text")}
    try:
        print(verify(args.package, args.proof, args.statement, pins,
                     args.lean_checker, args.lean_checker_sha256), end="")
    except (OSError, ValueError, RuntimeError, KeyError, json.JSONDecodeError) as exc:
        print(f"structural release rejected: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
