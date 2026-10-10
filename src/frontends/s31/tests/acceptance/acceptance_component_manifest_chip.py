#!/usr/bin/env python3
"""One-call direct-chip roster, package and re-sealed native-key controls."""

from __future__ import annotations

import copy
import json
import shutil
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from package.context import BUILD_FILE, file_hash, write_json
from package.manifest_digest import direct_chip_v2_digest


def reject_native(verifier: Path, proof: Path, statement: Path, key: Path) -> None:
    try:
        s31.invoke(str(verifier), str(proof), str(statement), str(key))
    except RuntimeError as exc:
        if "InvalidVerificationKey" not in str(exc):
            raise AssertionError(f"native verifier rejected for another reason: {exc}") from exc
    else:
        raise AssertionError("native verifier accepted a re-sealed false chip roster")


def reject_package(package: Path, work: Path, name: str, target: str, mutate) -> None:
    forged = work / f"{name}-{target}"
    shutil.copytree(package, forged)
    artifact_name = "component-manifest.json" if target == "sidecar" else "cost-report.json"
    artifact = forged / artifact_name
    value = json.loads(artifact.read_text())
    mutate(value if target == "sidecar" else value["component_manifest"])
    write_json(artifact, value)
    outer = json.loads((forged / "manifest.json").read_text())
    outer["artifacts"][artifact_name] = file_hash(artifact)
    write_json(forged / "manifest.json", outer)
    try:
        s31.verify_package(forged)
    except ValueError as exc:
        if "component manifest does not match sealed key" not in str(exc):
            raise AssertionError(f"package rejected for another reason: {exc}") from exc
    else:
        raise AssertionError(f"rehashed {target} was admitted")


def reject_rehashed_digest(package: Path, work: Path) -> None:
    forged = work / "forged-manifest-digest"
    shutil.copytree(package, forged)
    for artifact_name in ("verification-key.json", "cost-report.json"):
        artifact = forged / artifact_name
        value = json.loads(artifact.read_text())
        value["manifest_precommitment_sha256"] = "0" * 64
        write_json(artifact, value)
    outer = json.loads((forged / "manifest.json").read_text())
    for artifact_name in ("verification-key.json", "cost-report.json"):
        outer["artifacts"][artifact_name] = file_hash(forged / artifact_name)
    write_json(forged / "manifest.json", outer)
    try:
        s31.verify_package(forged)
    except ValueError as exc:
        if "component manifest does not match sealed key" not in str(exc):
            raise AssertionError(f"package rejected digest for another reason: {exc}") from exc
    else:
        raise AssertionError("rehashed false manifest digest was admitted")


def reject_resealed(package: Path, work: Path, name: str, key: dict, proof: Path,
                    statement: Path, mutate) -> None:
    forged_key = copy.deepcopy(key)
    mutate(forged_key["component_manifest"])
    key_path = work / f"{name}-key.json"
    write_json(key_path, forged_key)
    prefix = work / f"{name}-sealed"
    s31.invoke(
        "zig", "build", "--build-file", str(BUILD_FILE), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-chip",
        f"-Ds31-source={package / 'source.s31.json'}", f"-Ds31-name={key['name']}",
        f"-Ds31-key={key_path}", "--prefix", str(prefix),
    )
    verifier = prefix / "bin" / f"s31-{key['name']}-native-verifier"
    reject_native(verifier, proof, statement, key_path)


def mutations(private: bool):
    yield "chip-constant", lambda m: m["chip_call"].__setitem__("constant", m["chip_call"]["constant"] + 1)
    yield "trace-log", lambda m: m["components"][1].__setitem__("trace_log_size", m["components"][1]["trace_log_size"] + 1)
    yield "sum-position", lambda m: m["components"][1].__setitem__("claimed_sum_index", 0)
    yield "omitted-component", lambda m: m["components"].pop()
    yield "extra-component", lambda m: m["components"].append(copy.deepcopy(m["components"][-1]))
    yield "component-order", lambda m: m["components"].__setitem__(slice(0, 2), m["components"][:2][::-1])
    if private:
        yield "bridge-address", lambda m: m["chip_call"]["private_boundary"]["input"].__setitem__(0, m["chip_call"]["private_boundary"]["input"][0] + 1)


def check_case(source: Path, assignment: Path, private: bool) -> dict:
    with tempfile.TemporaryDirectory(prefix="s31-chip-manifest-") as directory:
        work = Path(directory)
        package = s31.build(source, work / "package", "direct-chip")
        s31.verify_package(package)
        key = json.loads((package / "verification-key.json").read_text())
        report = json.loads((package / "cost-report.json").read_text())
        sidecar = json.loads((package / "component-manifest.json").read_text())
        if (key["schema"] != "s31-verification-key-direct-chip-manifest-v2" or
                sidecar != key["component_manifest"] or sidecar != report["component_manifest"] or
                sidecar["schema"] != "s31-component-manifest-direct-chip-v2" or
                key.get("manifest_precommitment_sha256") != report.get("manifest_precommitment_sha256") or
                len(key.get("manifest_precommitment_sha256", "")) != 64 or
                len(sidecar["components"]) != (3 if private else 2) or
                sidecar["claimed_sums"] != (3 if private else 2) or
                [component["claimed_sum_index"] for component in sidecar["components"]] != list(range(3 if private else 2)) or
                [component["name"] for component in sidecar["components"]] !=
                (["qm31_ops", "repeated_step_chip", "private_boundary_bridge"] if private else
                 ["qm31_ops", "repeated_step_chip"]) or
                sidecar["chip_call"]["call_id"] != 0 or
                (sidecar["chip_call"]["private_boundary"] is not None) != private):
            raise AssertionError("generated one-call chip manifest has the wrong roster")
        if direct_chip_v2_digest(sidecar) != key["manifest_precommitment_sha256"]:
            raise AssertionError("Python and native typed manifest digests differ")
        without_identity = copy.deepcopy(sidecar)
        without_identity["circuit_hash"] = "0" * 64
        if direct_chip_v2_digest(without_identity) != key["manifest_precommitment_sha256"]:
            raise AssertionError("manifest precommitment contains its dependent circuit hash")
        trial = s31.trial(package, assignment, work / "trial")
        if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
            raise AssertionError("native chip proof control failed")
        reject_rehashed_digest(package, work)
        controls = list(mutations(private))
        for name, mutate in controls:
            reject_package(package, work, name, "sidecar", mutate)
            reject_package(package, work, name, "report", mutate)
            reject_resealed(package, work, name, key, work / "trial/proof.bin",
                            work / "trial/statement.json", mutate)
        # A re-sealed key cannot substitute a different transcript precommitment
        # even when the manifest roster and source bytes are left untouched.
        forged_key = copy.deepcopy(key)
        forged_key["manifest_precommitment_sha256"] = "0" * 64
        wrong_digest = work / "wrong-digest-key.json"
        write_json(wrong_digest, forged_key)
        prefix = work / "wrong-digest-sealed"
        s31.invoke("zig", "build", "--build-file", str(BUILD_FILE), "install",
                   "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-chip",
                   f"-Ds31-source={package / 'source.s31.json'}", f"-Ds31-name={key['name']}",
                   f"-Ds31-key={wrong_digest}", "--prefix", str(prefix))
        reject_native(prefix / "bin" / f"s31-{key['name']}-native-verifier",
                      work / "trial/proof.bin", work / "trial/statement.json", wrong_digest)
        proof = (work / "trial/proof.bin").read_bytes()
        assert proof[:8] == (b"S31NAT6P" if private else b"S31NAT6C")
        old_magic = b"S31NAT5P" if private else b"S31NAT4C"
        old_proof = work / "old-version-proof.bin"
        old_proof.write_bytes(old_magic + proof[8:])
        try:
            s31.invoke(str(package / "bin" / f"s31-{key['name']}-native-verifier"),
                       str(old_proof), str(work / "trial/statement.json"),
                       str(package / "verification-key.json"))
        except RuntimeError as exc:
            if "InvalidNativeProof" not in str(exc):
                raise AssertionError(f"cross-version proof rejected for another reason: {exc}") from exc
        else:
            raise AssertionError("v2 verifier accepted a v1-tagged proof")
        return {
            "program": key["name"], "private": private,
            "components": len(sidecar["components"]),
            "proof_bytes": (work / "trial/proof.bin").stat().st_size,
            "native_proof_accepted": True,
            "changed_claim_rejected": True,
            "rehashed_sidecar_rejected": len(controls),
            "rehashed_report_rejected": len(controls),
            "resealed_native_key_rejected": len(controls),
            "wrong_manifest_digest_rejected": True,
            "cross_version_proof_rejected": True,
        }


def main() -> None:
    cases = [
        check_case(S31 / "examples/arithmetic/arith4_m31.s31.json",
                   S31 / "examples/arithmetic/arith4.valid.json", False),
        check_case(S31 / "examples/boundary/private_affine_square16.s31",
                   S31 / "examples/boundary/private_affine_square16.valid.json", True),
    ]
    print(json.dumps({"schema": "s31-component-manifest-chip-acceptance-v1", "cases": cases},
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
