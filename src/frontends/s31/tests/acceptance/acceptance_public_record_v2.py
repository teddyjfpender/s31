#!/usr/bin/env python3
"""Output-only record ABI v2: native statement controls and zero AIR-row cost."""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from package.context import BUILD_FILE, write_json
from text_frontend import compile_text

SOURCE = """struct Pair { square: [m31; 1], again: [m31; 1] }
circuit pair(public x: [m31; 1]) -> public Pair {
    let square = x .* x;
    Pair { square: square, again: square }
}
"""


def canonical(value: dict) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def reject(verifier: Path, proof: Path, statement: Path, key: Path,
           value: bytes, label: str, expected_error: str) -> None:
    statement.write_bytes(value)
    result = subprocess.run((str(verifier), str(proof), str(statement), str(key)),
                            capture_output=True, text=True)
    if result.returncode != 1 or f"error: {expected_error}" not in result.stderr:
        raise AssertionError(f"native verifier accepted, crashed, or returned the wrong "
                             f"error on {label}: exit={result.returncode} {result.stderr}")


def reject_resealed_key(work: Path, package: Path, proof: Path,
                        statement: Path) -> None:
    forged = copy.deepcopy(json.loads((package / "verification-key.json").read_text()))
    forged["public_abi_sha256"] = "0" * 64
    key_path = work / "forged-record-key.json"
    write_json(key_path, forged)
    prefix = work / "forged-sealed"
    s31.invoke(
        "zig", "build", "--build-file", str(BUILD_FILE), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-gate",
        f"-Ds31-source={(package / 'source.s31.json').resolve()}", "-Ds31-name=pair",
        f"-Ds31-key={key_path}",
        f"-Ds31-stdlib-sha256={forged['stdlib_lock_sha256']}",
        "--prefix", str(prefix),
    )
    verifier = prefix / "bin/s31-pair-native-verifier"
    try:
        s31.invoke(str(verifier), str(proof), str(statement), str(key_path))
    except RuntimeError as exc:
        if "InvalidVerificationKey" not in str(exc):
            raise AssertionError(f"forged key rejected for unexpected reason: {exc}") from exc
    else:
        raise AssertionError("native verifier accepted resealed key with wrong ABI digest")


def check_release_safe_alias(work: Path, package: Path, proof: Path,
                             statement: Path, key_path: Path,
                             alias_mutation: bytes) -> None:
    key = json.loads(key_path.read_text())
    prefix = work / "release-safe-sealed"
    s31.invoke(
        "zig", "build", "--build-file", str(BUILD_FILE), "install",
        "-Doptimize=ReleaseSafe", "-Ds31-version=1", "-Ds31-lowering=direct-gate",
        f"-Ds31-source={(package / 'source.s31.json').resolve()}", "-Ds31-name=pair",
        f"-Ds31-key={key_path}",
        f"-Ds31-stdlib-sha256={key['stdlib_lock_sha256']}",
        "--prefix", str(prefix),
    )
    verifier = prefix / "bin/s31-pair-native-verifier"
    s31.invoke(str(verifier), str(proof), str(statement), str(key_path))
    reject(verifier, proof, work / "release-safe-alias.json", key_path,
           alias_mutation, "alias under ReleaseSafe", "InvalidRecordStatement")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-public-record-v2-") as temporary:
        work = Path(temporary)
        source = work / "pair.s31"
        source.write_text(SOURCE)
        relation, _ = compile_text(SOURCE)
        if relation["version"] != 2 or relation["public_outputs"] != ["square"]:
            raise AssertionError("record alias added a proof word")
        manual = {**relation, "version": 1, "name": "pair_flat"}
        del manual["public_abi"]
        manual_path = work / "pair_flat.s31.json"
        manual_path.write_text(json.dumps(manual, sort_keys=True, indent=2) + "\n")
        assignment = work / "assignment.json"
        assignment.write_text(json.dumps({
            "public_inputs": {"x": [7]}, "private_inputs": {},
            "public_outputs": {"square": [49]},
        }) + "\n")

        package = s31.build(source, work / "record-package", "direct-gate")
        flat_package = s31.build(manual_path, work / "flat-package", "direct-gate")
        record_cost = json.loads((package / "cost-report.json").read_text())
        flat_cost = json.loads((flat_package / "cost-report.json").read_text())
        for field in ("raw", "padded", "preprocessed_cells", "preprocessed_columns"):
            if record_cost[field] != flat_cost[field]:
                raise AssertionError(f"record grouping changed {field}")
        trial = s31.trial(package, assignment, work / "trial")
        if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
            raise AssertionError("record proof did not pass native positive/negative controls")
        flat_trial = s31.trial(flat_package, assignment, work / "flat-trial")
        if not flat_trial["native_verifier_accepted"]:
            raise AssertionError("flat v1 control proof did not verify")
        key = package / "verification-key.json"
        verifier = package / "bin/s31-pair-native-verifier"
        proof = work / "trial/proof.bin"
        statement = work / "mutated-statement.json"
        honest = json.loads((work / "trial/statement.json").read_text())
        mutations = {}
        changed = copy.deepcopy(honest)
        changed["leaves"][2]["words"][0] ^= 1
        mutations["alias"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][1]["path"][1]["field"] = "other"
        mutations["field_name"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][1], changed["leaves"][2] = changed["leaves"][2], changed["leaves"][1]
        mutations["field_order"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["abi_sha256"] = "0" * 64
        mutations["digest"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][0]["words"][0] = 2**31 - 1
        mutations["noncanonical_m31"] = canonical(changed)
        mutations["v1_statement"] = canonical({"public_inputs": {"x": [7]},
                                                 "public_outputs": {"square": [49]}})
        mutations["duplicate_key"] = (work / "trial/statement.json").read_bytes().replace(
            b'"version":2', b'"version":2,"version":2')
        mutations["noncanonical_json"] = json.dumps(honest, indent=2).encode() + b"\n"
        for label, value in mutations.items():
            expected_error = ("DuplicateField" if label == "duplicate_key" else
                              "InvalidRecordAbi" if label == "v1_statement" else
                              "InvalidRecordStatement")
            reject(verifier, proof, statement, key, value, label, expected_error)
        reject_resealed_key(work, package, proof, work / "trial/statement.json")
        check_release_safe_alias(work, package, proof, work / "trial/statement.json",
                                 key, mutations["alias"])

        print(json.dumps({
            "schema": "s31-public-record-v2-acceptance",
            "native_proof_accepted": True,
            "flat_v1_proof_accepted": True,
            "rejected_statement_mutations": list(mutations),
            "resealed_key_with_wrong_abi_digest_rejected": True,
            "release_safe_alias_rejected_cleanly": True,
            "zero_extra_arithmetic_rows": True,
            "raw": record_cost["raw"], "padded": record_cost["padded"],
            "public_abi_sha256": record_cost["public_abi_sha256"],
        }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
