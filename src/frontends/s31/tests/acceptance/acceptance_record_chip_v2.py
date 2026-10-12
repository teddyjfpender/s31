#!/usr/bin/env python3
"""Native proof gate for source-bound public records on the one-call chip."""

from __future__ import annotations

import copy
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from package.context import BUILD_FILE, file_hash, write_json
from package.manifest_digest import direct_chip_v2_digest
from package.verify import verify_package
from text_frontend import compile_text

SOURCE = """struct Lanes { words: [m31; 4] }
struct Result { words: [m31; 4], again: [m31; 4] }
fn step(v: [m31; 4]) -> [m31; 4] {
    v .* v + splat<4>(7_m31)
}
circuit record_chip(public x: Lanes) -> public Result {
    let y = iterate<16>(step, x.words);
    Result { words: y, again: y }
}
"""
P = (1 << 31) - 1


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def rejected(verifier: Path, proof: Path, statement: Path, key: Path,
             payload: bytes, label: str) -> None:
    statement.write_bytes(payload)
    result = subprocess.run((str(verifier), str(proof), str(statement), str(key)),
                            capture_output=True, text=True)
    if result.returncode == 0:
        raise AssertionError(f"native record-chip verifier accepted {label}")


def resealed_wrong_key_rejected(work: Path, package: Path, proof: Path,
                               statement: Path, field: str) -> None:
    key = copy.deepcopy(json.loads((package / "verification-key.json").read_text()))
    if field == "public_abi_sha256":
        key[field] = "0" * 64
    elif field == "component_manifest":
        key[field]["components"][1]["program_binding_sha256"] = "0" * 64
        key["manifest_precommitment_sha256"] = direct_chip_v2_digest(key[field])
    else:
        raise AssertionError("unrecognized resealed key mutation")
    key_path = work / f"wrong-{field}-key.json"
    write_json(key_path, key)
    prefix = work / f"wrong-{field}-sealed"
    options = ([f"-Ds31-stdlib-sha256={key['stdlib_lock_sha256']}"]
               if key.get("stdlib_lock_sha256") else [])
    s31.invoke("zig", "build", "--build-file", str(BUILD_FILE), "install",
               "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-chip",
               f"-Ds31-source={(package / 'source.s31.json').resolve()}",
               "-Ds31-name=record_chip", f"-Ds31-key={key_path}",
               *options, "--prefix", str(prefix))
    verifier = prefix / "bin/s31-record_chip-native-verifier"
    result = subprocess.run((str(verifier), str(proof), str(statement), str(key_path)),
                            capture_output=True, text=True)
    if result.returncode == 0 or "InvalidVerificationKey" not in result.stderr:
        raise AssertionError(f"resealed wrong {field} was not rejected by native source check")


def native_visibility_swap_rejected(work: Path, relation: dict) -> None:
    changed = copy.deepcopy(relation)
    changed["public_abi"]["inputs"][0]["visibility"] = "private"
    source = work / "visibility-swap.s31.json"
    write_json(source, changed)
    prefix = work / "visibility-swap-build"
    s31.invoke("zig", "build", "--build-file", str(BUILD_FILE), "install",
               "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-chip",
               f"-Ds31-source={source}", "-Ds31-name=record_chip",
               "--prefix", str(prefix))
    prover = prefix / "bin/s31-record_chip-prover"
    result = subprocess.run((str(prover), "check"), capture_output=True, text=True)
    if result.returncode == 0 or "InvalidRecordAbi" not in result.stderr:
        raise AssertionError("native source parser accepted swapped record visibility")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-chip-v2-") as temporary:
        work = Path(temporary)
        source = work / "record_chip.s31"
        source.write_text(SOURCE)
        relation, _ = compile_text(SOURCE)
        flat = {**relation, "version": 1, "name": "flat_chip"}
        del flat["public_abi"]
        flat_path = work / "flat_chip.s31.json"
        write_json(flat_path, flat)
        initial = [0, 1, 2, 7]
        final = initial[:]
        for _ in range(16):
            final = [(value * value + 7) % P for value in final]
        typed_assignment = {
            "version": 2, "public_inputs": {"x": {"words": initial}},
            "private_inputs": {}, "result": {"words": final, "again": final},
        }
        typed_path = work / "typed-assignment.json"
        typed_path.write_bytes(canonical(typed_assignment))
        flat_assignment = {
            "public_inputs": {relation["inputs"][0]["name"]: initial},
            "private_inputs": {},
            "public_outputs": {relation["public_outputs"][0]: final},
        }
        flat_assignment_path = work / "flat-assignment.json"
        write_json(flat_assignment_path, flat_assignment)
        package = s31.build(source, work / "record-package", "direct-chip")
        flat_package = s31.build(flat_path, work / "flat-package", "direct-chip")
        verify_package(package)
        key = json.loads((package / "verification-key.json").read_text())
        if (key["schema"] != "s31-verification-key-direct-record-chip-v2" or
                key["profile"] != "direct-m31-v4" or key.get("private_boundary") is not None or
                key["component_manifest"]["schema"] != "s31-component-manifest-direct-chip-v2" or
                key["component_manifest"]["claimed_sums"] != 2):
            raise AssertionError("record chip used an unexpected sealed one-call roster")
        record_cost = json.loads((package / "cost-report.json").read_text())
        flat_cost = json.loads((flat_package / "cost-report.json").read_text())
        for field in ("raw", "padded", "preprocessed_cells", "preprocessed_columns"):
            if record_cost[field] != flat_cost[field]:
                raise AssertionError(f"record wrapper changed {field} arithmetic geometry")
        trial = s31.trial(package, typed_path, work / "record-trial")
        flat_trial = s31.trial(flat_package, flat_assignment_path, work / "flat-trial")
        if (not trial["native_verifier_accepted"] or
                not trial["changed_public_statement_rejected"] or
                not flat_trial["native_verifier_accepted"]):
            raise AssertionError("native record or flat chip proof gate failed")
        verifier = package / "bin/s31-record_chip-native-verifier"
        proof = work / "record-trial/proof.bin"
        honest_path = work / "record-trial/statement.json"
        honest = json.loads(honest_path.read_text())
        statement = work / "mutation.json"
        key_path = package / "verification-key.json"
        controls: dict[str, bytes] = {}
        changed = copy.deepcopy(honest)
        changed["leaves"][0]["path"][1]["field"] = "forged"
        controls["input_field_path"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][1]["path"][1]["field"] = "forged"
        controls["output_field_path"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"].reverse()
        controls["field_order"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][1]["words"][0] = (changed["leaves"][1]["words"][0] + 1) % P
        controls["output_word"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][2]["words"][0] = (changed["leaves"][2]["words"][0] + 1) % P
        controls["alias_disagreement"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][0]["words"][0] = P
        controls["noncanonical_m31"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["abi_sha256"] = "0" * 64
        controls["abi_digest"] = canonical(changed)
        controls["duplicate_json_key"] = canonical(honest).replace(
            b'"version":2', b'"version":2,"version":2')
        controls["flat_v1_statement"] = canonical(flat_assignment)
        for label, payload in controls.items():
            rejected(verifier, proof, statement, key_path, payload, label)
        for field in ("public_abi_sha256", "component_manifest"):
            resealed_wrong_key_rejected(work, package, proof, honest_path, field)
        native_visibility_swap_rejected(work, relation)
        flat_verifier = flat_package / "bin/s31-flat_chip-native-verifier"
        flat_key = flat_package / "verification-key.json"
        rejected(verifier, work / "flat-trial/proof.bin", statement, key_path,
                 honest_path.read_bytes(), "flat v1 proof with typed v2 statement")
        flat_statement = work / "flat-trial/statement.json"
        rejected(flat_verifier, proof, statement, flat_key,
                 flat_statement.read_bytes(), "record v2 proof with flat v1 statement")
        altered = work / "altered-sidecar"
        shutil.copytree(package, altered)
        display = json.loads((altered / "public-abi.json").read_text())
        display["boundary"]["result"]["type"]["fields"][0]["name"] = "forged"
        write_json(altered / "public-abi.json", display)
        manifest = json.loads((altered / "manifest.json").read_text())
        manifest["artifacts"]["public-abi.json"] = file_hash(altered / "public-abi.json")
        write_json(altered / "manifest.json", manifest)
        try:
            verify_package(altered)
        except ValueError:
            pass
        else:
            raise AssertionError("package reader trusted resealed ABI sidecar")
        altered_manifest = work / "altered-manifest"
        shutil.copytree(package, altered_manifest)
        component = json.loads((altered_manifest / "component-manifest.json").read_text())
        component["components"][1]["program_binding_sha256"] = "0" * 64
        write_json(altered_manifest / "component-manifest.json", component)
        outer = json.loads((altered_manifest / "manifest.json").read_text())
        outer["artifacts"]["component-manifest.json"] = file_hash(
            altered_manifest / "component-manifest.json")
        write_json(altered_manifest / "manifest.json", outer)
        try:
            verify_package(altered_manifest)
        except ValueError:
            pass
        else:
            raise AssertionError("package reader trusted rehashed manifest sidecar")
        print(json.dumps({
            "schema": "s31-record-chip-v2-acceptance",
            "native_record_and_flat_chip_proofs_accepted": True,
            "same_arithmetic_geometry": True,
            "rejected_statement_mutations": list(controls),
            "resealed_wrong_abi_and_manifest_keys_rejected": True,
            "native_visibility_swap_rejected": True,
            "resealed_abi_sidecar_rejected": True,
            "rehashed_manifest_sidecar_rejected": True,
            "v1_v2_cross_profile_replay_rejected": True,
            "public_abi_sha256": key["public_abi_sha256"],
            "raw": record_cost["raw"], "padded": record_cost["padded"],
        }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
