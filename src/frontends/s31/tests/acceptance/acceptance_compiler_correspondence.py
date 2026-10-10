#!/usr/bin/env python3
"""A real direct-gate proof and a resealed compiler-mutation rejection."""

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
from package import verify as package_verify
from package.build import build_json
from package.context import file_hash, sha256, write_json
from package.correspondence import (KEY_FIELDS, canonical, check_package,
                                    digest, read_canonical_json)


def main() -> None:
    source = S31 / "examples/arithmetic/functional_square4_manual.s31"
    assignment = S31 / "examples/arithmetic/functional_square4.valid.json"
    with tempfile.TemporaryDirectory(prefix="s31-correspondence-") as directory:
        work = Path(directory)
        duplicate = work / "duplicate.json"
        duplicate.write_text('{"op":"mul","op":"add"}\n')
        try:
            read_canonical_json(duplicate)
        except ValueError as exc:
            if "duplicate JSON key" not in str(exc):
                raise AssertionError(f"wrong ambiguous-JSON rejection: {exc}") from exc
        else:
            raise AssertionError("duplicate JSON keys were admitted")
        honest = s31.build(source, work / "honest", "direct-gate")
        checked = check_package(honest)
        if checked["status"]["source_to_normalized"] != "source-to-normalized-checked":
            raise AssertionError("honest package lacks the source correspondence status")
        if not s31.trial(honest, assignment, work / "honest-proof")["native_verifier_accepted"]:
            raise AssertionError("honest certified native proof was rejected")
        missing = work / "missing-certificate"
        shutil.copytree(honest, missing)
        (missing / "correspondence-certificate.json").unlink()
        missing_manifest = json.loads((missing / "manifest.json").read_text())
        del missing_manifest["artifacts"]["correspondence-certificate.json"]
        write_json(missing / "manifest.json", missing_manifest)
        try:
            s31.verify_package(missing)
        except ValueError as exc:
            if "correspondence certificate is absent or changed" not in str(exc):
                raise AssertionError(f"wrong missing-certificate rejection: {exc}") from exc
        else:
            raise AssertionError("eligible source package omitted its required certificate")

        relation = json.loads((honest / "source.s31.json").read_text())
        forged_relation = copy.deepcopy(relation)
        forged_relation["nodes"][0]["op"] = "add"
        forged_source = work / "mutated.s31.json"
        write_json(forged_source, forged_relation)
        library_lock = json.loads((honest / "stdlib-lock.json").read_text())
        forged = build_json(forged_source, work / "forged", "direct-gate", library_lock)
        forged_assignment = {
            "public_inputs": {"x": [0, 1, 2, 7]},
            "private_inputs": {},
            "public_outputs": {"result": [0, 4, 16, 196]},
        }
        forged_assignment_path = work / "forged.valid.json"
        write_json(forged_assignment_path, forged_assignment)
        if not s31.trial(forged, forged_assignment_path, work / "forged-proof")["native_verifier_accepted"]:
            raise AssertionError("resealed mutated relation did not produce a native proof")

        for name in ("source.s31", "source-map.json", "typed-interface.json"):
            shutil.copy2(honest / name, forged / name)
        manifest = json.loads((forged / "manifest.json").read_text())
        manifest["source_text_sha256"] = sha256(source.read_bytes())
        manifest["text_frontend_version"] = 1
        for name in ("source.s31", "source-map.json", "typed-interface.json"):
            manifest["artifacts"][name] = file_hash(forged / name)
        key = json.loads((forged / "verification-key.json").read_text())
        component = json.loads((forged / "component-manifest.json").read_text())
        fake = copy.deepcopy(checked)
        fake["relation_sha256"] = file_hash(forged / "source.s31.json")
        fake["source_ssa"]["instructions"][0]["op"] = "add"
        fake["gate_schedule"][1]["op"] = "add"
        fake["air_profile"]["component_manifest_sha256"] = digest(canonical(component))
        fake["key_core"] = {field: key.get(field) for field in KEY_FIELDS}
        write_json(forged / "correspondence-certificate.json", fake)
        manifest["artifacts"]["correspondence-certificate.json"] = file_hash(
            forged / "correspondence-certificate.json")
        write_json(forged / "manifest.json", manifest)

        # Simulate a compiler and package rechecker both endorsing the altered
        # relation. The independent source parser must still stop admission.
        source_map = json.loads((forged / "source-map.json").read_text())["nodes"]
        old_lower = package_verify.lower_text
        package_verify.lower_text = lambda _: (
            forged_relation, (forged / "source.s31.json").read_bytes(), source_map)
        try:
            try:
                package_verify.verify_package(forged)
            except ValueError as exc:
                if "normalized relation differs from independent source parse" not in str(exc):
                    raise AssertionError(f"wrong rejection boundary: {exc}") from exc
            else:
                raise AssertionError("resealed mul-to-add compiler mutation was admitted")
        finally:
            package_verify.lower_text = old_lower

        print(json.dumps({
            "schema": "s31-compiler-correspondence-acceptance-v1",
            "fragment": "public four-lane direct-gate add/mul/static-let",
            "honest_native_proof_accepted": True,
            "resealed_mutant_native_proof_accepted_under_mutant_relation": True,
            "resealed_mutant_package_admission_rejected": True,
            "duplicate_json_key_rejected": True,
            "missing_certificate_rejected": True,
            "certificate_status": checked["status"],
        }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
