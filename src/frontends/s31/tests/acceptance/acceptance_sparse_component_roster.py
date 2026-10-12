#!/usr/bin/env python3
"""One native sparse proof and coherent key/sidecar tamper controls."""

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
from package.sparse_component_roster import ARTIFACT, COMPONENTS, KEY_SCHEMA, digest

SOURCE = S31 / "examples/arithmetic/affine4_v1.s31.json"
ASSIGNMENT = S31 / "examples/arithmetic/affine4_v1.valid.json"


def run(package: Path, work: Path) -> None:
    s31.verify_package(package)
    key = json.loads((package / "verification-key.json").read_text())
    report = json.loads((package / "cost-report.json").read_text())
    roster = json.loads((package / ARTIFACT).read_text())
    if (key["schema"] != KEY_SCHEMA or
            roster != report["sparse_component_roster"] or
            key["sparse_component_roster_sha256"] != digest(roster) or
            report["sparse_component_roster_sha256"] != digest(roster) or
            roster["claimed_sums"] != 3 or
            [row["source_index"] for row in roster["components"]] !=
            [spec[1] for spec in COMPONENTS] or
            [row["proof_index"] for row in roster["components"]] != [0, 1, 2] or
            [row["claimed_sum_index"] for row in roster["components"]] != [0, 1, 2] or
            len(roster["preprocessed_columns"]) != 12 or
            [row["commitment_index"] for row in roster["preprocessed_columns"]] != list(range(12))):
        raise AssertionError("sparse roster does not describe the compiled AIR")
    trial = s31.trial(package, ASSIGNMENT, work / "trial")
    if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
        raise AssertionError("valid proof or changed public claim control failed")
    if ((work / "trial/proof.bin").read_bytes()[:8] != b"S31NAT3G" or
            (package / "verification-key.json").stat().st_size > 1536):
        raise AssertionError("sparse proof envelope or bounded key size changed")

    forged = dict(key)
    forged["sparse_component_roster_sha256"] = "f" * 64
    if forged["sparse_component_roster_sha256"] == key["sparse_component_roster_sha256"]:
        forged["sparse_component_roster_sha256"] = "e" * 64
    forged_path = work / "forged-key.json"
    s31.write_json(forged_path, forged)
    prefix = work / "forged-bin"
    s31.invoke("zig", "build", "--build-file", str(s31.BUILD_FILE), "install",
               "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=sparse-gate",
               f"-Ds31-source={SOURCE}", "-Ds31-name=affine4_v1",
               f"-Ds31-key={forged_path}", "--prefix", str(prefix))
    result = subprocess.run(
        [str(prefix / "bin/s31-affine4_v1-native-verifier"),
         str(work / "trial/proof.bin"), str(work / "trial/statement.json"), str(forged_path)],
        cwd=s31.ROOT, capture_output=True, text=True,
    )
    if result.returncode == 0 or "InvalidVerificationKey" not in result.stdout + result.stderr:
        raise AssertionError(f"resealed sparse roster key was not rejected: {result.stderr}")

    copied = work / "tampered-sidecar"
    shutil.copytree(package, copied)
    sidecar = copied / ARTIFACT
    edited = json.loads(sidecar.read_text())
    before = edited["preprocessed_columns"][0]["values_sha256"]
    edited["preprocessed_columns"][0]["values_sha256"] = (
        "0" if before[0] != "0" else "1") + before[1:]
    s31.write_json(sidecar, edited)
    envelope = json.loads((copied / "manifest.json").read_text())
    envelope["artifacts"][ARTIFACT] = s31.file_hash(sidecar)
    s31.write_json(copied / "manifest.json", envelope)
    try:
        s31.verify_package(copied)
    except ValueError:
        pass
    else:
        raise AssertionError("rehashed sparse roster sidecar was accepted")

    downgraded = work / "downgraded"
    shutil.copytree(package, downgraded)
    downgraded_key = json.loads((downgraded / "verification-key.json").read_text())
    downgraded_key["schema"] = "s31-verification-key-v3"
    downgraded_key.pop("sparse_component_roster_sha256")
    s31.write_json(downgraded / "verification-key.json", downgraded_key)
    (downgraded / ARTIFACT).unlink()
    downgraded_manifest = json.loads((downgraded / "manifest.json").read_text())
    downgraded_manifest["artifacts"].pop(ARTIFACT)
    downgraded_manifest["artifacts"]["verification-key.json"] = s31.file_hash(
        downgraded / "verification-key.json")
    s31.write_json(downgraded / "manifest.json", downgraded_manifest)
    try:
        s31.verify_package(downgraded)
    except ValueError:
        pass
    else:
        raise AssertionError("sparse package key downgrade was accepted")

    print(json.dumps({"accepted_proof_bytes": trial["proof_bytes"],
                      "key_bytes": (package / "verification-key.json").stat().st_size,
                      "components": 3, "preprocessed_columns": 12,
                      "resealed_key_rejected": True, "rehashed_sidecar_rejected": True,
                      "downgrade_rejected": True}, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--package", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="s31-sparse-roster-") as directory:
        work = Path(directory)
        package = (args.package.resolve() if args.package else
                   s31.build(SOURCE, work / "package", "sparse-gate"))
        run(package, work)


if __name__ == "__main__":
    main()
