#!/usr/bin/env python3
"""Native direct-gate component manifest generation and tamper controls."""

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
from package.manifest_digest import direct_gate_v2_digest


def reject(call: tuple[str, ...], expected: str) -> None:
    try:
        s31.invoke(*call)
    except RuntimeError as exc:
        if expected not in str(exc):
            raise AssertionError(f"rejected for the wrong reason: {exc}") from exc
    else:
        raise AssertionError(f"accepted corrupted component manifest: {call}")


def mutate_order(value: dict) -> None:
    columns = value["preprocessed_columns"]
    columns[0], columns[1] = columns[1], columns[0]


def mutate_index(value: dict) -> None:
    indices = value["components"][0]["preprocessed_indices"]
    indices[0] = (indices[0] + 1) % len(value["preprocessed_columns"])


def mutate_hash(value: dict) -> None:
    column = value["preprocessed_columns"][0]
    digest = column["values_sha256"]
    column["values_sha256"] = ("0" if digest[0] != "0" else "1") + digest[1:]


def reject_resealed_key(work: Path, source: Path, name: str, original_key: dict,
                        proof: Path, statement: Path, mutation) -> None:
    forged_key = copy.deepcopy(original_key)
    if mutation is None:
        forged_key["manifest_precommitment_sha256"] = "0" * 64
    else:
        mutation(forged_key["component_manifest"])
        forged_key["manifest_precommitment_sha256"] = direct_gate_v2_digest(forged_key["component_manifest"])
    forged_path = work / f"{name}-key.json"
    write_json(forged_path, forged_key)
    prefix = work / f"{name}-sealed"
    s31.invoke(
        "zig", "build", "--build-file", str(BUILD_FILE), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-gate",
        "-Ds31-direct-gate-manifest-version=2",
        f"-Ds31-source={source.resolve()}", "-Ds31-name=math_polynomial4",
        f"-Ds31-key={forged_path}", "--prefix", str(prefix),
    )
    verifier = prefix / "bin/s31-math_polynomial4-native-verifier"
    reject((str(verifier), str(proof), str(statement), str(forged_path)),
           "InvalidVerificationKey")


def reject_rehashed_sidecar(work: Path, package: Path, mutation, name: str) -> None:
    forged = work / f"{name}-sidecar"
    shutil.copytree(package, forged)
    sidecar = forged / "component-manifest.json"
    value = json.loads(sidecar.read_text())
    mutation(value)
    write_json(sidecar, value)
    package_manifest = json.loads((forged / "manifest.json").read_text())
    package_manifest["artifacts"]["component-manifest.json"] = file_hash(sidecar)
    write_json(forged / "manifest.json", package_manifest)
    try:
        s31.verify_package(forged)
    except ValueError as exc:
        if "component manifest does not match sealed key" not in str(exc):
            raise AssertionError(f"sidecar rejected for the wrong reason: {exc}") from exc
    else:
        raise AssertionError("rehashed component manifest sidecar was admitted")


def reject_rehashed_report(work: Path, package: Path, mutation, name: str) -> None:
    forged = work / f"{name}-report"
    shutil.copytree(package, forged)
    report = forged / "cost-report.json"
    value = json.loads(report.read_text())
    mutation(value["component_manifest"])
    write_json(report, value)
    package_manifest = json.loads((forged / "manifest.json").read_text())
    package_manifest["artifacts"]["cost-report.json"] = file_hash(report)
    write_json(forged / "manifest.json", package_manifest)
    try:
        s31.verify_package(forged)
    except ValueError as exc:
        if "component manifest does not match sealed key" not in str(exc):
            raise AssertionError(f"report rejected for the wrong reason: {exc}") from exc
    else:
        raise AssertionError("rehashed report component manifest was admitted")


def main() -> None:
    source = S31 / "examples/arithmetic/math_polynomial4.s31.json"
    assignment = S31 / "examples/arithmetic/math_polynomial4.valid.json"
    with tempfile.TemporaryDirectory(prefix="s31-component-manifest-") as directory:
        work = Path(directory)
        package = s31.build(source, work / "package", "direct-gate")
        s31.verify_package(package)
        key = json.loads((package / "verification-key.json").read_text())
        report = json.loads((package / "cost-report.json").read_text())
        sidecar = json.loads((package / "component-manifest.json").read_text())
        component = sidecar["components"]
        columns = sidecar["preprocessed_columns"]
        if (key["schema"] != "s31-verification-key-direct-manifest-v2" or
                sidecar != key["component_manifest"] or sidecar != report["component_manifest"] or
                sidecar["schema"] != "s31-component-manifest-direct-gate-v2" or
                key["manifest_precommitment_sha256"] != direct_gate_v2_digest(sidecar) or
                report["manifest_precommitment_sha256"] != key["manifest_precommitment_sha256"] or
                len(component) != 1 or component[0]["name"] != "qm31_ops" or
                component[0]["source_index"] != 1 or component[0]["proof_index"] != 0 or
                component[0]["base_trace_columns"] != 12 or
                component[0]["interaction_trace_columns"] != 8 or
                sidecar["claimed_sums"] != 1 or len(columns) != 8 or
                [item["commitment_index"] for item in columns] != list(range(8)) or
                any(item["rows"] != (1 << item["log_size"]) for item in columns)):
            raise AssertionError("direct-gate manifest does not describe the selected AIR")
        trial = s31.trial(package, assignment, work / "trial")
        if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
            raise AssertionError("native direct-gate proof control failed")
        proof = (work / "trial/proof.bin").read_bytes()
        if proof[:8] != b"S31NAT7G":
            raise AssertionError("direct-gate manifest v2 proof used an old envelope")
        old_tag = work / "old-envelope.proof.bin"
        old_tag.write_bytes(b"S31NAT4G" + proof[8:])
        reject((str(package / "bin/s31-math_polynomial4-native-verifier"), str(old_tag),
                str(work / "trial/statement.json"), str(package / "verification-key.json")),
               "InvalidNativeProof")
        for mutation in (mutate_order, mutate_index, mutate_hash):
            changed = copy.deepcopy(sidecar)
            mutation(changed)
            if direct_gate_v2_digest(changed) == key["manifest_precommitment_sha256"]:
                raise AssertionError("typed manifest digest ignored a changed roster field")
        without_identity = copy.deepcopy(sidecar)
        without_identity["circuit_hash"] = "0" * 64
        if direct_gate_v2_digest(without_identity) != key["manifest_precommitment_sha256"]:
            raise AssertionError("gate precommitment unexpectedly includes cyclic circuit identity")

        for name, mutation in (("order", mutate_order), ("index", mutate_index),
                               ("column-hash", mutate_hash)):
            reject_rehashed_sidecar(work, package, mutation, name)
            reject_rehashed_report(work, package, mutation, name)
            reject_resealed_key(work, source, name, key, work / "trial/proof.bin",
                                work / "trial/statement.json", mutation)
        reject_resealed_key(work, source, "precommitment", key, work / "trial/proof.bin",
                            work / "trial/statement.json", None)
        print(json.dumps({
            "schema": "s31-component-manifest-acceptance-v2",
            "profile": "direct-m31-v4",
            "key_schema": key["schema"],
            "components": len(component), "preprocessed_columns": len(columns),
            "honest_proof_accepted": True, "changed_claim_rejected": True,
            "rehashed_sidecar_mutations_rejected": 3,
            "rehashed_report_mutations_rejected": 3,
            "resealed_native_key_mutations_rejected": 4,
        }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
