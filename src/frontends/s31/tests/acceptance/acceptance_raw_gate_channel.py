#!/usr/bin/env python3
"""Raw Gate roundtrip, proof/key separation, and package downgrade controls."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))
import s31

SOURCE = S31 / "examples/arithmetic/affine4_v1.s31.json"
ASSIGNMENT = S31 / "examples/arithmetic/affine4_v1.valid.json"
RAW = "raw-blake2s-rejection-v1"
NAME = "affine4_v1"


def call(*args: str, accept: bool) -> None:
    result = subprocess.run(args, cwd=s31.ROOT, capture_output=True, text=True)
    if (result.returncode == 0) != accept:
        raise AssertionError(f"unexpected exit {result.returncode}: {args}\n{result.stdout}{result.stderr}")


def reject_package(path: Path) -> None:
    try:
        s31.verify_package(path)
    except (ValueError, FileNotFoundError):
        return
    raise AssertionError(f"re-sealed package profile was accepted: {path}")


def resealed_copy(source: Path, target: Path, kind: str) -> None:
    shutil.copytree(source, target)
    manifest_path = target / "manifest.json"
    key_path = target / "verification-key.json"
    manifest = json.loads(manifest_path.read_text())
    key = json.loads(key_path.read_text())
    if kind == "raw-to-legacy":
        manifest.pop("channel_profile")
        key.pop("channel_profile")
        key["schema"] = "s31-verification-key-gate-roster-v1"
        key["profile"] = "circuit-v1"
    elif kind == "legacy-to-raw":
        manifest["channel_profile"] = RAW
        key["channel_profile"] = RAW
        key["schema"] = "s31-verification-key-gate-raw-v1"
        key["profile"] = "circuit-raw-v1"
    elif kind == "legacy-missing-recursion":
        manifest["artifacts"].pop("recursive-verification-key.json")
        (target / "recursive-verification-key.json").unlink()
    else:
        raise AssertionError(kind)
    s31.write_json(key_path, key)
    manifest["artifacts"]["verification-key.json"] = s31.file_hash(key_path)
    s31.write_json(manifest_path, manifest)
    reject_package(target)


def run(raw: Path, legacy: Path, work: Path) -> None:
    raw_manifest = s31.verify_package(raw)
    legacy_manifest = s31.verify_package(legacy)
    raw_key = json.loads((raw / "verification-key.json").read_text())
    if (raw_manifest.get("channel_profile") != RAW or
            raw_key.get("channel_profile") != RAW or
            raw_key.get("schema") != "s31-verification-key-gate-raw-v1" or
            raw_key.get("profile") != "circuit-raw-v1" or
            legacy_manifest.get("channel_profile") is not None or
            any("recursive" in name or "fold" in name for name in raw_manifest["artifacts"])):
        raise AssertionError("raw and legacy packages are not separately sealed")
    try:
        s31.build(SOURCE, work / "invalid-raw-step4", "gate", fri_fold_step=4,
                  channel_profile=RAW)
    except ValueError:
        pass
    else:
        raise AssertionError("raw Gate admitted unreviewed FRI fold step 4")

    assignment = json.loads(ASSIGNMENT.read_text())
    statement = work / "statement.json"
    s31.write_json(statement, {"public_inputs": assignment["public_inputs"],
                               "public_outputs": assignment["public_outputs"]})
    proofs = {}
    for label, package, magic in (("raw", raw, b"S31NAT8R"),
                                  ("legacy", legacy, b"S31NAT1\0")):
        proof = work / f"{label}.proof"
        call(str(package / f"bin/s31-{NAME}-prover"), "prove", str(ASSIGNMENT),
             str(proof), accept=True)
        if proof.read_bytes()[:8] != magic:
            raise AssertionError(f"{label} proof magic changed")
        call(str(package / f"bin/s31-{NAME}-native-verifier"), str(proof),
             str(statement), str(package / "verification-key.json"), accept=True)
        proofs[label] = proof

    for label, package, foreign, foreign_package in (
            ("raw", raw, proofs["legacy"], legacy),
            ("legacy", legacy, proofs["raw"], raw)):
        verifier = str(package / f"bin/s31-{NAME}-native-verifier")
        call(verifier, str(foreign), str(statement),
             str(package / "verification-key.json"), accept=False)
        call(verifier, "check-key", str(foreign_package / "verification-key.json"),
             accept=False)
    call(str(raw / f"bin/s31-{NAME}-prover"), "recurse-keygen",
         str(raw / "verification-key.json"), str(work / "unexpected-recursive-key.json"),
         accept=False)
    for kind, package in (("raw-to-legacy", raw), ("legacy-to-raw", legacy),
                          ("legacy-missing-recursion", legacy)):
        resealed_copy(package, work / kind, kind)
    print(json.dumps({"raw_proof_bytes": proofs["raw"].stat().st_size,
                      "legacy_proof_bytes": proofs["legacy"].stat().st_size,
                      "cross_profile_rejected": True,
                      "resealed_package_swaps_rejected": True}, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--raw-package", type=Path)
    parser.add_argument("--legacy-package", type=Path)
    args = parser.parse_args()
    if (args.raw_package is None) != (args.legacy_package is None):
        parser.error("supply both package paths or neither")
    with tempfile.TemporaryDirectory(prefix="s31-raw-channel-") as temporary:
        work = Path(temporary)
        raw = args.raw_package.resolve() if args.raw_package else s31.build(
            SOURCE, work / "raw-package", "gate", channel_profile=RAW)
        legacy = args.legacy_package.resolve() if args.legacy_package else s31.build(
            SOURCE, work / "legacy-package", "gate")
        run(raw, legacy, work)


if __name__ == "__main__":
    main()
