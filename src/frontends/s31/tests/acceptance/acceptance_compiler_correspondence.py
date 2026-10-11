#!/usr/bin/env python3
"""A real direct-gate proof and independently rejected resealed mutations."""

from __future__ import annotations

import copy
import difflib
import hashlib
import json
import shutil
import struct
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))
REPO = S31.parents[2]
sys.path.insert(0, str(REPO / "scripts"))

import s31
from package import verify as package_verify
from package.build import build_json
from package.context import file_hash, invoke, sha256, write_json
from package.correspondence import (DIRECT_COLUMN_IDS, KEY_FIELDS, canonical, check_package,
                                    digest, read_canonical_json)
from export_s31_direct_gate_bridge import render_bridge
from export_s31_direct_gate_bytecode_arithmetic import (
    render as render_bytecode_arithmetic, render_logup as render_bytecode_logup,
    render_composition as render_bytecode_composition,
    render_transcript_params as render_bytecode_transcript_params,
    render_oods_openings as render_bytecode_oods_openings,
)
from export_s31_direct_gate_evaluator_fixture import (
    render as render_evaluator_fixture, validate_component_geometry,
)


def reseal_emitted_columns(topology: dict, component: dict) -> None:
    """An adversary recomputes the complete value-free column plan and hashes."""
    uses = [0] * topology["n_vars"]
    for kind in ("add", "sub", "mul", "pointwise_mul"):
        for gate in topology[kind]:
            uses[gate["in0"]] += 1
            uses[gate["in1"]] += 1
    for address in (*topology["permutation_inputs"], *topology["output"]):
        uses[address] += 1
    uses[0] += 2 * len(topology["permutation_inputs"])
    rows = []
    for opcode, kind in enumerate(("add", "sub", "mul", "pointwise_mul")):
        for gate in topology[kind]:
            rows.append([*(int(index == opcode) for index in range(4)),
                         gate["in0"], gate["in1"], gate["out"], uses[gate["out"]]])
    begin = 0
    for index, end in enumerate(topology["permutation_ends"]):
        scratch = topology["n_vars"] + index
        for source, target in zip(topology["permutation_inputs"][begin:end],
                                  topology["permutation_outputs"][begin:end], strict=True):
            rows.extend(([1, 0, 0, 0, 0, source, scratch, 1],
                         [1, 0, 0, 0, 0, scratch, target, uses[target]]))
        begin = end
    assert len(rows) == len(topology["columns"][0]["values"])
    for index, column in enumerate(topology["columns"]):
        assert column["id"] == DIRECT_COLUMN_IDS[index]
        column["values"] = [row[index] for row in rows]
        component["preprocessed_columns"][index]["values_sha256"] = hashlib.sha256(
            b"".join(struct.pack("<I", word) for word in column["values"])).hexdigest()


def reject_resealed_topology(honest: Path, checked: dict, work: Path,
                             name: str, mutate, expected: tuple[str, ...]) -> None:
    """Let an adversary rewrite topology, columns, key, manifest and claim."""
    mutant = work / name
    shutil.copytree(honest, mutant)
    topology = json.loads((mutant / "gate-topology.json").read_text())
    component = json.loads((mutant / "component-manifest.json").read_text())
    mutate(topology, checked)
    reseal_emitted_columns(topology, component)
    write_json(mutant / "gate-topology.json", topology)
    write_json(mutant / "component-manifest.json", component)
    key = json.loads((mutant / "verification-key.json").read_text())
    report = json.loads((mutant / "cost-report.json").read_text())
    key["component_manifest"] = component
    report["component_manifest"] = component
    write_json(mutant / "verification-key.json", key)
    write_json(mutant / "cost-report.json", report)
    fake = copy.deepcopy(checked)
    fake["gate_topology_sha256"] = file_hash(mutant / "gate-topology.json")
    fake["air_profile"]["component_manifest_sha256"] = digest(canonical(component))
    fake["key_core"] = {field: key.get(field) for field in KEY_FIELDS}
    write_json(mutant / "correspondence-certificate.json", fake)
    manifest = json.loads((mutant / "manifest.json").read_text())
    for artifact in ("gate-topology.json", "component-manifest.json",
                     "verification-key.json", "cost-report.json",
                     "correspondence-certificate.json"):
        manifest["artifacts"][artifact] = file_hash(mutant / artifact)
    write_json(mutant / "manifest.json", manifest)
    try:
        check_package(mutant)
    except ValueError as exc:
        if not any(fragment in str(exc) for fragment in expected):
            raise AssertionError(f"{name} reached the wrong rejection boundary: {exc}") from exc
    else:
        raise AssertionError(f"resealed {name} was admitted")


def reject_resealed_component_map(honest: Path, checked: dict, work: Path,
                                  kind: str) -> None:
    """Reseal every package copy of a changed fixed/main/interaction map."""
    mutant = work / f"changed-{kind}-component-map"
    shutil.copytree(honest, mutant)
    component = json.loads((mutant / "component-manifest.json").read_text())
    entry = component["components"][0]
    if kind == "fixed":
        entry["preprocessed_indices"][1:3] = reversed(entry["preprocessed_indices"][1:3])
    elif kind == "main":
        entry["trace_spans"][1]["start"] = 1
    elif kind == "interaction":
        entry["trace_spans"][2]["start"] = 1
    else:
        raise AssertionError(f"unknown component map mutation: {kind}")
    write_json(mutant / "component-manifest.json", component)
    key = json.loads((mutant / "verification-key.json").read_text())
    report = json.loads((mutant / "cost-report.json").read_text())
    key["component_manifest"] = component
    report["component_manifest"] = component
    write_json(mutant / "verification-key.json", key)
    write_json(mutant / "cost-report.json", report)
    fake = copy.deepcopy(checked)
    fake["air_profile"]["component_manifest_sha256"] = digest(canonical(component))
    fake["key_core"] = {field: key.get(field) for field in KEY_FIELDS}
    write_json(mutant / "correspondence-certificate.json", fake)
    manifest = json.loads((mutant / "manifest.json").read_text())
    for name in ("component-manifest.json", "verification-key.json", "cost-report.json",
                 "correspondence-certificate.json"):
        manifest["artifacts"][name] = file_hash(mutant / name)
    write_json(mutant / "manifest.json", manifest)
    try:
        check_package(mutant)
    except ValueError as exc:
        if "direct-gate AIR profile or key core" not in str(exc):
            raise AssertionError(f"resealed {kind} map reached wrong rejection: {exc}") from exc
    else:
        raise AssertionError(f"resealed {kind} component map was admitted")


def reject_resealed_program_binding(honest: Path, checked: dict, work: Path) -> None:
    """A forged compiler cannot nominate a different Gate AIR program hash."""
    mutant = work / "changed-gate-program-binding"
    shutil.copytree(honest, mutant)
    component = json.loads((mutant / "component-manifest.json").read_text())
    entry = component["components"][0]
    original = entry["program_binding_sha256"]
    entry["program_binding_sha256"] = ("0" if original[0] != "0" else "1") + original[1:]
    write_json(mutant / "component-manifest.json", component)
    key = json.loads((mutant / "verification-key.json").read_text())
    report = json.loads((mutant / "cost-report.json").read_text())
    key["component_manifest"] = component
    report["component_manifest"] = component
    write_json(mutant / "verification-key.json", key)
    write_json(mutant / "cost-report.json", report)
    fake = copy.deepcopy(checked)
    fake["air_profile"]["component_manifest_sha256"] = digest(canonical(component))
    fake["key_core"] = {field: key.get(field) for field in KEY_FIELDS}
    write_json(mutant / "correspondence-certificate.json", fake)
    manifest = json.loads((mutant / "manifest.json").read_text())
    for name in ("component-manifest.json", "verification-key.json", "cost-report.json",
                 "correspondence-certificate.json"):
        manifest["artifacts"][name] = file_hash(mutant / name)
    write_json(mutant / "manifest.json", manifest)
    try:
        render_bytecode_arithmetic(mutant)
    except ValueError as exc:
        if "direct-gate AIR profile or key core" not in str(exc):
            raise AssertionError(f"resealed Gate program reached wrong rejection: {exc}") from exc
    else:
        raise AssertionError("resealed Gate program binding was admitted")


def wrong_opcode(topology: dict, _checked: dict) -> None:
    topology["add"].insert(3, topology["pointwise_mul"].pop(0))
    topology["pointwise_mul"].append(topology["add"].pop())


def wrong_source_operand(topology: dict, checked: dict) -> None:
    source = checked["source_gates"][0]
    kind = "pointwise_mul" if source["op"] == "mul" else "add"
    gate = next(gate for gate in topology[kind] if gate["out"] == source["out"])
    gate["in1"] = 11 if source["in1"] != 11 else 12


def wrong_constant(topology: dict, checked: dict) -> None:
    # Keep the pack/unpack address equality intact, but replace the second
    # extension-field basis element with the unit constant.
    first_result_mask = sum(gate["op"] == "mul" for gate in checked["source_gates"])
    topology["mul"][0]["in0"] = 1
    topology["pointwise_mul"][first_result_mask + 1]["in1"] = 1


def extra_gate(topology: dict, checked: dict) -> None:
    # The final add is a constant/padding gate in this packaged example. Make
    # it read the computed result, retaining all gate and row counts.
    topology["add"][-1]["in0"] = checked["source_gates"][-1]["out"]


def extra_constant_gate(topology: dict, _checked: dict) -> None:
    # A valid but noncanonical zero-only gate would pass a semantic island
    # check. The exact constant/padding schedule must still reject it.
    topology["add"][-1]["in0"] = 0
    topology["add"][-1]["in1"] = 0


def main() -> None:
    invoke("zig", "test", "--dep", "stwo_utils",
           "-Mroot=src/frontends/s31/tests/proofs/gate_mask_native_test.zig",
           "-Mstwo_utils=deps/stwo-zig/src/core/utils.zig")
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
        golden_bridge = (REPO / "formal/s31/S31/Gadgets/Functional/"
                         "GeneratedDirectGateBridge.lean")
        rendered_bridge = render_bridge(honest)
        if rendered_bridge != golden_bridge.read_text():
            difference = "".join(list(difflib.unified_diff(
                golden_bridge.read_text().splitlines(keepends=True),
                rendered_bridge.splitlines(keepends=True),
                fromfile="checked-in Lean", tofile="regenerated Lean"))[:40])
            raise AssertionError("source/native bridge differs from checked Lean instance:\n"
                                 + difference)
        evaluator_golden = (REPO / "formal/s31/S31/Gadgets/Air/"
                            "GeneratedDirectGateEvaluatorFixture.lean")
        evaluator_rendered = render_evaluator_fixture(honest, assignment)
        if evaluator_rendered != evaluator_golden.read_text():
            raise AssertionError("direct Gate evaluator fixture differs from checked Lean replay")
        bytecode_golden = (REPO / "formal/s31/S31/Gadgets/Air/"
                           "GeneratedDirectGateBytecodeArithmetic.lean")
        if render_bytecode_arithmetic(honest) != bytecode_golden.read_text():
            raise AssertionError("installed Gate bytecode differs from checked Lean arithmetic export")
        logup_golden = (REPO / "formal/s31/S31/Gadgets/Air/"
                        "GeneratedDirectGateBytecodeLogUp.lean")
        if render_bytecode_logup(honest) != logup_golden.read_text():
            raise AssertionError("installed Gate LogUp bytecode differs from checked Lean export")
        composition_golden = (REPO / "formal/s31/S31/Gadgets/Air/"
                              "GeneratedDirectGateComposition.lean")
        if render_bytecode_composition(honest) != composition_golden.read_text():
            raise AssertionError("installed Gate composition differs from checked Lean export")
        transcript_golden = (REPO / "formal/s31/S31/Gadgets/Air/"
                             "GeneratedDirectGateTranscriptParams.lean")
        if render_bytecode_transcript_params(honest) != transcript_golden.read_text():
            raise AssertionError("Gate transcript parameters differ from checked Lean export")
        openings_golden = (REPO / "formal/s31/S31/Gadgets/Air/"
                           "GeneratedDirectGateOodsOpenings.lean")
        if render_bytecode_oods_openings(honest) != openings_golden.read_text():
            raise AssertionError("Gate OODS sampled-value claim differs from checked Lean export")
        component = json.loads((honest / "component-manifest.json").read_text())["components"][0]
        for kind in ("fixed", "main", "interaction"):
            changed = copy.deepcopy(component)
            if kind == "fixed":
                changed["preprocessed_indices"][1:3] = reversed(
                    changed["preprocessed_indices"][1:3])
            elif kind == "main":
                changed["trace_spans"][1]["start"] = 1
            else:
                changed["trace_spans"][2]["start"] = 1
            try:
                validate_component_geometry(changed)
            except ValueError as exc:
                if "column geometry changed" not in str(exc):
                    raise AssertionError(f"{kind} map reached wrong rejection: {exc}") from exc
            else:
                raise AssertionError(f"changed {kind} AIR column map was admitted")
            reject_resealed_component_map(honest, checked, work, kind)
        reject_resealed_program_binding(honest, checked, work)
        if checked["status"]["source_to_normalized"] != "source-to-normalized-checked":
            raise AssertionError("honest package lacks the source correspondence status")
        if not s31.trial(honest, assignment, work / "honest-proof")["native_verifier_accepted"]:
            raise AssertionError("honest certified native proof was rejected")
        statement = json.loads((work / "honest-proof/statement.json").read_text())
        changed_input = copy.deepcopy(statement)
        changed_input["public_inputs"]["x"][0] = (
            changed_input["public_inputs"]["x"][0] + 1) % ((1 << 31) - 1)
        changed_input_path = work / "changed-public-input-statement.json"
        write_json(changed_input_path, changed_input)
        manifest = json.loads((honest / "manifest.json").read_text())
        native_verifier = honest / "bin" / f"s31-{manifest['name']}-native-verifier"
        proof_path = work / "honest-proof/proof.bin"
        statement_path = work / "honest-proof/statement.json"
        try:
            invoke(str(native_verifier), str(proof_path),
                   str(changed_input_path), str(honest / "verification-key.json"))
        except RuntimeError:
            pass
        else:
            raise AssertionError("native verifier accepted a changed public input word")
        changed_gate_claim = bytearray(proof_path.read_bytes())
        if changed_gate_claim[:8] != b"S31NAT4G" or len(changed_gate_claim) < 32:
            raise AssertionError("honest proof is not a direct-gate proof envelope")
        first_limb = struct.unpack_from("<I", changed_gate_claim, 16)[0]
        if first_limb >= (1 << 31) - 1:
            raise AssertionError("honest Gate claim is not canonical M31")
        struct.pack_into("<I", changed_gate_claim, 16,
                         (first_limb + 1) % ((1 << 31) - 1))
        changed_gate_claim_path = work / "changed-gate-claim.proof.bin"
        changed_gate_claim_path.write_bytes(changed_gate_claim)
        try:
            invoke(str(native_verifier), str(changed_gate_claim_path),
                   str(statement_path), str(honest / "verification-key.json"))
        except RuntimeError as exc:
            if "InvalidLookupSum" not in str(exc):
                raise AssertionError(f"Gate claim reached wrong rejection: {exc}") from exc
        else:
            raise AssertionError("native verifier accepted a changed Gate lookup claim")
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

        reject_resealed_topology(
            honest, checked, work, "wrong-opcode", wrong_opcode,
            ("source gates are missing", "unexpected pointwise gates",
             "native source gate selector or operands"))
        reject_resealed_topology(
            honest, checked, work, "wrong-source-operand", wrong_source_operand,
            ("native source gate selector or operands differ from checked SSA",))
        reject_resealed_topology(
            honest, checked, work, "wrong-constant", wrong_constant,
            ("native four-lane basis is not derived from fixed constants",))
        reject_resealed_topology(
            honest, checked, work, "extra-gate", extra_gate,
            ("extra native gate depends on source or public data",))
        reject_resealed_topology(
            honest, checked, work, "extra-constant-gate", extra_constant_gate,
            ("constant derivation or padding gate schedule differs",))

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
            "changed_public_input_native_statement_rejected": True,
            "changed_gate_claim_native_lookup_sum_rejected": True,
            "resealed_mutant_native_proof_accepted_under_mutant_relation": True,
            "resealed_mutant_package_admission_rejected": True,
            "duplicate_json_key_rejected": True,
            "missing_certificate_rejected": True,
            "resealed_wrong_opcode_rejected": True,
            "resealed_wrong_source_operand_rejected": True,
            "resealed_wrong_constant_rejected": True,
            "resealed_extra_gate_rejected": True,
            "resealed_extra_constant_gate_rejected": True,
            "native_gate_counts": checked["gate_counts"],
            "native_exact_constant_schedule_checked": True,
            "lean_bridge_instance_matches_native_package": True,
            "evaluator_fixture_matches_checked_package": True,
            "installed_gate_bytecode_arithmetic_matches_checked_package": True,
            "installed_gate_bytecode_logup_matches_checked_package": True,
            "installed_gate_composition_matches_checked_package": True,
            "installed_gate_transcript_params_match_checked_package": True,
            "installed_gate_oods_openings_match_checked_package": True,
            "native_gate_512_row_previous_mask_matches_lean_formula": True,
            "resealed_component_column_maps_rejected": True,
            "resealed_gate_program_binding_rejected": True,
            "certificate_status": checked["status"],
        }, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
