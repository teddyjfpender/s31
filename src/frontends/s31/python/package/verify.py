"""Check artifact hashes and the source, key, AIR and verifier bindings."""

from __future__ import annotations

import json
from pathlib import Path

import proof_privacy
from package.manifest_digest import direct_chip_v2_digest
from package.context import (
    AIR_BUNDLE_SHA256, LIBRARY_SOURCE_FILES, PROJECTION_SHA256, abi, file_hash,
    lower_text, text_interface,
)


def verify_package(package: Path) -> dict:
    manifest = json.loads((package / "manifest.json").read_text())
    if manifest.get("schema") != "s31-package-v1":
        raise ValueError("invalid S31 package manifest")
    name = manifest.get("name")
    artifacts = manifest.get("artifacts")
    if not isinstance(name, str) or not name or not isinstance(artifacts, dict):
        raise ValueError("incomplete S31 package manifest")
    capabilities = manifest.get("capabilities", [])
    if (not isinstance(capabilities, list) or any(not isinstance(item, str) for item in capabilities) or
            (any(item in capabilities for item in ("s31-state-fold-batch-v1", "s31-state-fold-batch-v2")) and
             "state-fold-verification-key.json" not in artifacts) or
            ("s31-fixed-fold-batch-v1" in capabilities and
             (manifest.get("lowering") not in {"gate", "sparse-wide-gate"} or
              "fixed-fold-verification-key.json" not in artifacts))):
        raise ValueError("invalid S31 package capabilities")
    required_artifacts = {
        "source.s31.json", "verification-key.json", "public-abi.json",
        "cost-report.json", f"bin/s31-{name}-prover",
        f"bin/s31-{name}-native-verifier",
    }
    if not required_artifacts.issubset(artifacts):
        raise ValueError("S31 package is missing required artifacts")
    source = json.loads((package / "source.s31.json").read_text())
    if source.get("version") not in (1, 2):
        raise ValueError("unsupported S31 relation version")
    if source["version"] == 2 and manifest.get("lowering") != "direct-gate":
        raise ValueError("record ABI v2 requires direct-gate lowering")
    privacy = proof_privacy.policy_for(source, manifest.get("lowering"), manifest.get("fri_fold_step", 1))
    fri_fold_step = manifest.get("fri_fold_step", 1)
    if (type(fri_fold_step) is not int or fri_fold_step not in (1, 4) or
            (fri_fold_step == 4 and manifest.get("lowering") not in {"gate", "sparse-wide-gate"})):
        raise ValueError("invalid S31 package FRI fold step")
    if privacy is None and manifest.get("lowering") in {"gate", "sparse-wide-gate"}:
        if not {"recursive-verification-key.json", "recursive-verification-key-level2.json"}.issubset(artifacts):
            raise ValueError("recursive package is missing its verification keys")
        recursive_key = json.loads((package / "recursive-verification-key.json").read_text())
        recursive_next_key = json.loads((package / "recursive-verification-key-level2.json").read_text())
        wide = manifest["lowering"] == "sparse-wide-gate"
        expected_schema = "s31-recursive-verification-key-v3" if wide else "s31-recursive-verification-key-v2"
        expected_recursive_step = 4 if wide else fri_fold_step
        actual_recursive_step = manifest.get("recursive_fri_fold_step")
        if (wide and (type(actual_recursive_step) is not int or actual_recursive_step != 4)) or (
                not wide and actual_recursive_step is not None and
                (type(actual_recursive_step) is not int or actual_recursive_step != expected_recursive_step)):
            raise ValueError("S31 recursive FRI schedule does not match the package profile")
        first_outer_step = recursive_key.get("outer_fri_fold_step")
        second_outer_step = recursive_next_key.get("outer_fri_fold_step")
        if (wide and (type(first_outer_step) is not int or first_outer_step != 4 or
                      type(second_outer_step) is not int or second_outer_step != 4)) or (
                not wide and (first_outer_step is not None or second_outer_step is not None)):
            raise ValueError("S31 recursive keys have an invalid FRI schedule")
        if (recursive_key.get("schema") != expected_schema or
                recursive_key.get("child_key_sha256") != file_hash(package / "verification-key.json") or
                recursive_key.get("projection_sha256") != PROJECTION_SHA256 or
                recursive_key.get("air_bundle_sha256") != AIR_BUNDLE_SHA256):
            raise ValueError("S31 recursive key does not match the child key and pinned AIR")
        if (recursive_next_key.get("schema") != expected_schema or
                recursive_next_key.get("child_key_sha256") != file_hash(package / "recursive-verification-key.json") or
                recursive_next_key.get("projection_sha256") != PROJECTION_SHA256 or
                recursive_next_key.get("air_bundle_sha256") != AIR_BUNDLE_SHA256):
            raise ValueError("S31 level-2 recursive key does not match its child key and pinned AIR")
        if wide:
            if "fixed-fold-verification-key.json" not in artifacts:
                raise ValueError("sparse-wide package is missing its fixed-fold key")
            fold_key = json.loads((package / "fixed-fold-verification-key.json").read_text())
            if (fold_key.get("schema") != "s31-fixed-fold-verification-key-v4" or
                    type(fold_key.get("outer_fri_fold_step")) is not int or
                    fold_key["outer_fri_fold_step"] != 4 or
                    fold_key.get("base_recursive_key_sha256") != file_hash(package / "recursive-verification-key-level2.json") or
                    fold_key.get("projection_sha256") != PROJECTION_SHA256 or
                    fold_key.get("air_bundle_sha256") != AIR_BUNDLE_SHA256):
                raise ValueError("S31 wide fixed-fold key does not match its base key and pinned AIR")
    if privacy is None and manifest.get("lowering") == "gate":
        if not {"recursive-verification-key.json", "recursive-verification-key-level2.json", "fixed-fold-verification-key.json"}.issubset(artifacts):
            raise ValueError("gate package is missing its recursive verification keys")
        fold_key = json.loads((package / "fixed-fold-verification-key.json").read_text())
        if (fold_key.get("schema") != "s31-fixed-fold-verification-key-v3" or
                fold_key.get("base_recursive_key_sha256") != file_hash(package / "recursive-verification-key.json") or
                fold_key.get("projection_sha256") != PROJECTION_SHA256 or
                fold_key.get("air_bundle_sha256") != AIR_BUNDLE_SHA256):
            raise ValueError("S31 fold key does not match its base key and pinned AIR")
        report = json.loads((package / "cost-report.json").read_text())
        if "state-fold-verification-key.json" in artifacts:
            state_fold_key = json.loads((package / "state-fold-verification-key.json").read_text())
            fold_step = report.get("state_fold_step")
            common_valid = (state_fold_key.get("base_recursive_key_sha256") == file_hash(package / "recursive-verification-key.json") and
                            state_fold_key.get("projection_sha256") == PROJECTION_SHA256 and
                            state_fold_key.get("air_bundle_sha256") == AIR_BUNDLE_SHA256)
            # The v1 shape remains readable for packages built before the
            # general step compiler; its installed verifier is sealed to v1.
            if state_fold_key.get("schema") == "s31-state-fold-verification-key-v1":
                old_step = report.get("repeated_step")
                valid_step = (isinstance(old_step, dict) and
                              state_fold_key.get("source_rounds") == old_step.get("rounds") and
                              state_fold_key.get("step_constant") == old_step.get("constant"))
            else:
                valid_step = (state_fold_key.get("schema") in
                              ("s31-state-fold-verification-key-v2", "s31-state-fold-verification-key-v3") and
                              isinstance(fold_step, dict) and
                              state_fold_key.get("source_rounds") == fold_step.get("rounds") and
                              state_fold_key.get("step_body") == fold_step.get("body") and
                              (state_fold_key.get("schema") != "s31-state-fold-verification-key-v3" or
                               state_fold_key.get("counter_bits") == 32))
            if not common_valid or not valid_step:
                raise ValueError("S31 state-fold key does not match its base key and pinned AIR")
        elif any(report.get(name) is not None for name in ("state_fold_step", "repeated_step")):
            raise ValueError("supported recurrence package is missing its state-fold key")
    for name, expected in artifacts.items():
        if not isinstance(name, str) or not isinstance(expected, str):
            raise ValueError("invalid S31 package artifact entry")
        path = (package / name).resolve()
        if not path.is_relative_to(package.resolve()) or file_hash(path) != expected:
            raise ValueError(f"S31 package artifact changed: {name}")
    if file_hash(package / "source.s31.json") != manifest["program_sha256"]:
        raise ValueError("S31 package source changed")
    # A self-authored manifest hash only checks that public-abi.json was copied
    # consistently. Re-derive the displayed statement schema from the sealed
    # relation so package consumers cannot be shown different public fields.
    if json.loads((package / "public-abi.json").read_text()) != abi(source, manifest["lowering"]):
        raise ValueError("S31 public ABI does not match the sealed relation")
    key = json.loads((package / "verification-key.json").read_text())
    fri_config = key.get("fri")
    if (not isinstance(fri_config, dict) or
            key.get("name") != manifest["name"] or
            key.get("program_sha256") != manifest["program_sha256"] or
            key.get("canonical_ir_sha256") != manifest.get("canonical_ir_sha256") or
            fri_config.get("fold_step") != fri_fold_step):
        raise ValueError("S31 package key does not match manifest")
    report = json.loads((package / "cost-report.json").read_text())
    proof_privacy.validate_package(source, manifest, key, report)
    inspected_key_fields = (
        "program_sha256", "canonical_ir_sha256", "profile", "chip",
        "preprocessed_root", "circuit_hash", "padded", "trace_log_size", "fri",
    )
    if any(report.get(field) != key.get(field) for field in inspected_key_fields):
        raise ValueError("S31 package cost report does not match key")
    if source["version"] == 2:
        expected_abi = abi(source, manifest["lowering"])["boundary_sha256"]
        if (key.get("schema") != "s31-verification-key-direct-record-v2" or
                key.get("public_abi_sha256") != expected_abi or
                report.get("public_abi_sha256") != expected_abi):
            raise ValueError("record ABI v2 key or cost report differs from source")
    elif key.get("public_abi_sha256") is not None or report.get("public_abi_sha256") is not None:
        raise ValueError("version 1 key cannot carry a record ABI digest")
    if manifest.get("lowering") == "direct-gate":
        if source["version"] == 1 and key.get("schema") == "s31-verification-key-v4":
            # Existing sealed verifiers still accept their own v4 keys. Keep
            # those packages readable, but never interpret a partial v1
            # component manifest as an optional extension to the old schema.
            if (key.get("profile") != "direct-m31-v4" or
                    "component-manifest.json" in artifacts or
                    (package / "component-manifest.json").exists() or
                    "component_manifest" in key or "component_manifest" in report):
                raise ValueError("invalid legacy S31 direct-gate component manifest")
        else:
            declared = key.get("component_manifest")
            if ("component-manifest.json" not in artifacts or
                    key.get("schema") != ("s31-verification-key-direct-record-v2" if source["version"] == 2 else "s31-verification-key-direct-manifest-v1") or
                    key.get("profile") != "direct-m31-v4" or
                    not isinstance(declared, dict) or
                    declared.get("schema") != "s31-component-manifest-direct-gate-v1" or
                    declared.get("profile") != key["profile"] or
                    any(declared.get(field) != key.get(field) for field in (
                        "program_sha256", "canonical_ir_sha256", "preprocessed_root", "circuit_hash",
                        "air_bundle_sha256")) or
                    report.get("component_manifest") != declared or
                    json.loads((package / "component-manifest.json").read_text()) != declared):
                raise ValueError("S31 direct-gate component manifest does not match sealed key")
    elif manifest.get("lowering") == "direct-chip":
        legacy_schema = ("s31-verification-key-v5p" if key.get("profile") == "direct-m31-private-v5"
                         else "s31-verification-key-v4")
        if key.get("schema") == legacy_schema:
            if (key.get("profile") not in {"direct-m31-v4", "direct-m31-private-v5"} or
                    "component-manifest.json" in artifacts or
                    (package / "component-manifest.json").exists() or
                    key.get("component_manifest") is not None or
                    report.get("component_manifest") is not None):
                raise ValueError("invalid legacy S31 direct-chip component manifest")
        else:
            declared = key.get("component_manifest")
            chip_call = declared.get("chip_call") if isinstance(declared, dict) else None
            expected_components = (3 if key.get("profile") == "direct-m31-private-v5" else 2)
            chip_v2 = key.get("schema") == "s31-verification-key-direct-chip-manifest-v2"
            try:
                expected_digest = direct_chip_v2_digest(declared) if chip_v2 and isinstance(declared, dict) else None
            except (KeyError, TypeError, ValueError) as exc:
                raise ValueError("S31 direct-chip component manifest does not match sealed key") from exc
            if ("component-manifest.json" not in artifacts or
                    key.get("schema") not in {"s31-verification-key-direct-chip-manifest-v1", "s31-verification-key-direct-chip-manifest-v2"} or
                    key.get("profile") not in {"direct-m31-v4", "direct-m31-private-v5"} or
                    not isinstance(key.get("chip"), dict) or
                    not isinstance(declared, dict) or
                    declared.get("schema") != ("s31-component-manifest-direct-chip-v2" if chip_v2 else "s31-component-manifest-direct-chip-v1") or
                    (chip_v2 and (not isinstance(key.get("manifest_precommitment_sha256"), str) or
                                  key["manifest_precommitment_sha256"] != expected_digest or
                                  report.get("manifest_precommitment_sha256") != key["manifest_precommitment_sha256"])) or
                    (not chip_v2 and (key.get("manifest_precommitment_sha256") is not None or
                                      report.get("manifest_precommitment_sha256") is not None)) or
                    declared.get("profile") != key["profile"] or
                    any(declared.get(field) != key.get(field) for field in (
                        "program_sha256", "canonical_ir_sha256", "preprocessed_root", "circuit_hash",
                        "air_bundle_sha256")) or
                    not isinstance(chip_call, dict) or chip_call.get("call_id") != 0 or
                    any(chip_call.get(field) != key["chip"].get(field) for field in
                        ("relation_id", "rounds", "constant")) or
                    chip_call.get("private_boundary") != key.get("private_boundary") or
                    declared.get("claimed_sums") != expected_components or
                    not isinstance(declared.get("components"), list) or
                    len(declared["components"]) != expected_components or
                    any(not isinstance(row, dict) for row in declared["components"]) or
                    [row.get("claimed_sum_index") for row in declared["components"]] !=
                    list(range(expected_components)) or
                    report.get("component_manifest") != declared or
                    json.loads((package / "component-manifest.json").read_text()) != declared):
                raise ValueError("S31 direct-chip component manifest does not match sealed key")
    elif ("component-manifest.json" in artifacts or key.get("component_manifest") is not None or
          report.get("component_manifest") is not None):
        raise ValueError("unexpected S31 component manifest")
    if key.get("profile") == "direct-m31-private-v5":
        boundary = key.get("private_boundary")
        if (manifest.get("lowering") != "direct-chip" or
                key.get("schema") not in {"s31-verification-key-v5p", "s31-verification-key-direct-chip-manifest-v1", "s31-verification-key-direct-chip-manifest-v2"} or
                not isinstance(boundary, dict) or
                set(boundary) != {"input", "output"} or
                any(not isinstance(boundary[name], list) or len(boundary[name]) != 4 or
                    any(type(address) is not int or address < 3 for address in boundary[name])
                    for name in ("input", "output")) or
                report.get("private_boundary") != boundary):
            raise ValueError("invalid direct M31 private boundary package key")
    elif "private_boundary" in key:
        raise ValueError("unexpected private boundary in S31 package key")
    if manifest.get("lowering") == "sha-joint":
        joint = key.get("sha_joint")
        if (key.get("schema") != "s31-verification-key-sha-joint-v1" or
                key.get("profile") != "sha-joint-v1" or key.get("chip") is not None or
                not isinstance(joint, dict) or report.get("sha_joint") != joint or
                joint.get("proof_envelope") != "S31NAT6S" or
                joint.get("sha_calls") != 3 or joint.get("claimed_sums") != 12 or
                len(joint.get("gate_addresses", [])) != 56):
            raise ValueError("invalid SHA joint package key")
    if manifest.get("lowering") == "sha-shift":
        shift = key.get("sha_shift")
        if (key.get("schema") != "s31-verification-key-sha-shift-v3" or
                key.get("profile") != "sha-shift-v3" or key.get("chip") is not None or
                not isinstance(shift, dict) or report.get("sha_shift") != shift or
                shift.get("proof_envelope") != "S31SCJ03" or
                shift.get("sha_calls") != 3 or shift.get("component_count") != 24 or
                shift.get("claimed_sums") != 15 or
                len(shift.get("gate_addresses", [])) != 56):
            raise ValueError("invalid SHA shift package key")
    if manifest.get("lowering") == "sha-fused":
        fused = key.get("sha_fused")
        if (key.get("schema") != "s31-verification-key-sha-fused-v4" or
                key.get("profile") != "sha-fused-v4" or key.get("chip") is not None or
                not isinstance(fused, dict) or report.get("sha_fused") != fused or
                fused.get("proof_envelope") != "S31FCJ04" or
                fused.get("sha_calls") != 3 or fused.get("component_count") != 14 or
                fused.get("claimed_sums") != 10 or
                len(fused.get("gate_addresses", [])) != 56):
            raise ValueError("invalid SHA fused package key")
    manifest_lock = manifest.get("stdlib_lock_sha256")
    key_lock = key.get("stdlib_lock_sha256")
    has_lock_artifact = "stdlib-lock.json" in manifest["artifacts"]
    if manifest_lock is not None or key_lock is not None or has_lock_artifact:
        if manifest_lock is None or key_lock != manifest_lock or not has_lock_artifact:
            raise ValueError("S31 package standard library lock is incomplete")
        if file_hash(package / "stdlib-lock.json") != manifest_lock:
            raise ValueError("S31 package standard library lock changed")
    if "source_text_sha256" in manifest:
        required = {"source.s31", "source-map.json"}
        if manifest.get("text_frontend_version") == 1:
            required.add("typed-interface.json")
        if not required.issubset(manifest["artifacts"]):
            raise ValueError("S31 text package is missing source artifacts")
        if file_hash(package / "source.s31") != manifest["source_text_sha256"]:
            raise ValueError("S31 package text source changed")
        source_map = json.loads((package / "source-map.json").read_text())
        if source_map.get("source_sha256") != manifest["source_text_sha256"]:
            raise ValueError("S31 package source map does not match text source")
        _, encoded, expected_locations = lower_text(package / "source.s31")
        if encoded != (package / "source.s31.json").read_bytes():
            raise ValueError("S31 text source does not lower to the sealed relation")
        if source_map != {"schema": "s31-text-source-map-v1",
                          "source_sha256": manifest["source_text_sha256"],
                          "nodes": expected_locations}:
            raise ValueError("S31 text source map does not match compiler output")
        if manifest.get("text_frontend_version") == 1:
            from text_frontend import Parser

            parser = Parser((package / "source.s31").read_text(), str(package / "source.s31"))
            _, circuit = parser.parse()
            expected_interface = text_interface(circuit, parser.stdlib_explicit)
            actual_interface = json.loads((package / "typed-interface.json").read_text())
            if manifest_lock is None:
                expected_interface.pop("stdlib")
            if actual_interface != expected_interface:
                raise ValueError("S31 typed interface does not match text source")
            if manifest_lock is not None:
                lock = json.loads((package / "stdlib-lock.json").read_text())
                sources = lock.get("sources", {})
                if (lock.get("schema") != "s31-stdlib-lock-v1" or
                        lock.get("package") != "std" or
                        lock.get("version") != expected_interface["stdlib"]["version"] or
                        lock.get("explicit_import") != parser.stdlib_explicit or
                        not isinstance(sources, dict) or
                        set(sources) != set(LIBRARY_SOURCE_FILES) or
                        any(not isinstance(value, str) or len(value) != 64 or
                                any(char not in "0123456789abcdef" for char in value)
                                for value in sources.values())):
                    raise ValueError("S31 standard library lock does not match text source")
    return manifest
