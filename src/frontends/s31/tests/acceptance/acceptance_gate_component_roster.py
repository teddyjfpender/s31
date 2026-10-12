#!/usr/bin/env python3
"""Gate AIR roster: emitted geometry, accepted proof, resealed-key rejection."""

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
from package.gate_component_roster import ARTIFACT, KEY_SCHEMA, NAMES, digest

SOURCE = S31 / "examples/arithmetic/affine4_v1.s31.json"
ASSIGNMENT = S31 / "examples/arithmetic/affine4_v1.valid.json"


def run(package: Path, work: Path) -> None:
    s31.verify_package(package)
    key = json.loads((package / "verification-key.json").read_text())
    report = json.loads((package / "cost-report.json").read_text())
    roster = json.loads((package / ARTIFACT).read_text())
    if (key["schema"] != KEY_SCHEMA or
            roster != report["gate_component_roster"] or
            key["gate_component_roster_sha256"] != digest(roster) or
            report["gate_component_roster_sha256"] != digest(roster) or
            roster["claimed_sums"] != 11 or
            [entry["name"] for entry in roster["components"]] != list(NAMES) or
            [entry["proof_index"] for entry in roster["components"]] != list(range(11)) or
            [entry["commitment_index"] for entry in roster["preprocessed_columns"]] !=
            list(range(len(roster["preprocessed_columns"]))) or
            any(entry["rows"] != 1 << entry["log_size"] for entry in roster["preprocessed_columns"])):
        raise AssertionError("gate manifest does not describe its compiled AIR")
    trial = s31.trial(package, ASSIGNMENT, work / "trial")
    if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
        raise AssertionError("valid or changed-claim native control failed")

    # A verifier with a freshly sealed altered digest still has the same
    # embedded source. Its independent roster rebuild must reject the key.
    forged = dict(key)
    forged["gate_component_roster_sha256"] = "f" * 64
    if forged["gate_component_roster_sha256"] == key["gate_component_roster_sha256"]:
        forged["gate_component_roster_sha256"] = "e" * 64
    forged_path = work / "forged-key.json"
    s31.write_json(forged_path, forged)
    prefix = work / "forged-bin"
    s31.invoke("zig", "build", "--build-file", str(s31.BUILD_FILE), "install",
               "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=gate",
               f"-Ds31-source={SOURCE}", "-Ds31-name=affine4_v1",
               f"-Ds31-key={forged_path}", "--prefix", str(prefix))
    result = subprocess.run(
        [str(prefix / "bin/s31-affine4_v1-native-verifier"),
         str(work / "trial/proof.bin"), str(work / "trial/statement.json"), str(forged_path)],
        cwd=s31.ROOT, capture_output=True, text=True,
    )
    if result.returncode == 0 or "InvalidVerificationKey" not in result.stdout + result.stderr:
        raise AssertionError(f"resealed gate roster key was not rejected: {result.stderr}")

    # The package reader keeps historical v1 keys readable. A newly built
    # verifier is sealed to its roster-bearing key, so stripping the roster
    # cannot downgrade that installed verifier to historical semantics.
    downgraded = dict(key)
    downgraded["schema"] = "s31-verification-key-v1"
    downgraded.pop("gate_component_roster_sha256")
    downgraded_path = work / "downgraded-key.json"
    s31.write_json(downgraded_path, downgraded)
    installed = package / "bin/s31-affine4_v1-native-verifier"
    result = subprocess.run(
        [str(installed), "check-key", str(downgraded_path)],
        cwd=s31.ROOT, capture_output=True, text=True,
    )
    if result.returncode == 0 or "InvalidVerificationKey" not in result.stdout + result.stderr:
        raise AssertionError(f"installed verifier accepted a downgraded key: {result.stderr}")

    # A copied sidecar with a recomputed package file hash still fails the
    # package consistency check. The native test above covers coherent
    # mutation of the sealed key itself.
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
        raise AssertionError("rehashed gate roster sidecar was accepted")
    print(json.dumps({"accepted_proof_bytes": trial["proof_bytes"],
                      "components": len(roster["components"]),
                      "preprocessed_columns": len(roster["preprocessed_columns"]),
                      "resealed_key_rejected": True, "rehashed_sidecar_rejected": True,
                      "installed_verifier_downgrade_rejected": True},
                     sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--package", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="s31-gate-roster-") as directory:
        work = Path(directory)
        package = args.package.resolve() if args.package else s31.build(SOURCE, work / "package", "gate")
        run(package, work)


if __name__ == "__main__":
    main()
