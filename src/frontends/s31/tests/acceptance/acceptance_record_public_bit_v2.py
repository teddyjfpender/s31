#!/usr/bin/env python3
"""Public bit leaves: native range checks, proof binding, and flat AIR parity."""

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
from abi.binding_v2 import binding_digest, flat_assignment_from_typed
from package.context import BUILD_FILE, file_hash, write_json
from package.verify import verify_package
from text_frontend import compile_text


SOURCE = """struct Request { flag: bit, value: [m31; 1] }
struct Response { flag: bit, chosen: [m31; 1] }
circuit bits(public request: Request, private other: [m31; 1]) -> public Response {
    Response { flag: std::field::is_zero(other),
               chosen: select(request.flag, request.value, other) }
}
"""


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def reject(verifier: Path, proof: Path, statement: Path, key: Path,
           encoded: bytes, label: str, expected: str | None = None) -> None:
    statement.write_bytes(encoded)
    result = subprocess.run((str(verifier), str(proof), str(statement), str(key)),
                            capture_output=True, text=True)
    if result.returncode != 1 or "error:" not in result.stderr or (
            expected is not None and f"error: {expected}" not in result.stderr):
        raise AssertionError(f"native verifier mishandled {label}: "
                             f"exit={result.returncode} {result.stderr}")


def reject_raw_prover_bit(package: Path, work: Path, flat: dict,
                          wire: str, section: str, label: str) -> None:
    """Both native prover entrypoints must reject before writing proof bytes."""
    changed = copy.deepcopy(flat)
    changed[section][wire] = [2]
    assignment = work / f"bad-{label}.json"
    write_json(assignment, changed)
    prover = package / "bin/s31-bits-prover"
    for command in ("prove", "prove-for-external-verification"):
        proof = work / f"bad-{label}-{command}.proof"
        result = subprocess.run((str(prover), command, str(assignment), str(proof)),
                                capture_output=True, text=True)
        if (result.returncode != 1 or "error: InvalidAssignedBit" not in result.stderr
                or proof.exists()):
            raise AssertionError(f"native {command} mishandled {label}: "
                                 f"exit={result.returncode} {result.stderr}")


def changed_public_tag(relation: dict, index: int, expected: str,
                       replacement: str) -> tuple[dict, str]:
    """Make a structurally valid but differently typed descriptor."""
    changed = copy.deepcopy(relation["public_abi"])
    field = changed["result"]["type"]["fields"][index]["type"]
    leaf = changed["result"]["leaves"][index]
    if (field != {"kind": expected, "length": 1} or
            leaf["kind"] != expected or replacement == expected):
        raise AssertionError("unexpected public field tag for forged ABI control")
    field["kind"] = leaf["kind"] = replacement
    base = {**relation, "version": 1}
    del base["public_abi"]
    return changed, binding_digest(base, changed)


def adversarial_package_controls(work: Path, package: Path, relation: dict,
                                 proof: Path, statement: Path) -> None:
    for label, index, expected, replacement in (
            ("bit-to-m31", 0, "bit", "m31"),
            ("m31-to-bit", 1, "m31", "bit")):
        changed, forged_digest = changed_public_tag(
            relation, index, expected, replacement)
        altered = work / f"altered-{label}-sidecar"
        shutil.copytree(package, altered)
        sidecar = json.loads((altered / "public-abi.json").read_text())
        sidecar["boundary"] = changed
        sidecar["boundary_sha256"] = forged_digest
        write_json(altered / "public-abi.json", sidecar)
        manifest = json.loads((altered / "manifest.json").read_text())
        manifest["artifacts"]["public-abi.json"] = file_hash(altered / "public-abi.json")
        write_json(altered / "manifest.json", manifest)
        try:
            verify_package(altered)
        except ValueError:
            pass
        else:
            raise AssertionError(f"package reader accepted a rehashed {label} ABI sidecar")

        key = json.loads((package / "verification-key.json").read_text())
        key["public_abi_sha256"] = forged_digest
        forged_key = work / f"resealed-{label}-key.json"
        write_json(forged_key, key)
        prefix = work / f"resealed-{label}"
        options = ([f"-Ds31-stdlib-sha256={key['stdlib_lock_sha256']}"]
                   if key.get("stdlib_lock_sha256") else [])
        s31.invoke("zig", "build", "--build-file", str(BUILD_FILE), "install",
                   "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-gate",
                   f"-Ds31-source={(package / 'source.s31.json').resolve()}",
                   "-Ds31-name=bits", f"-Ds31-key={forged_key}", *options,
                   "--prefix", str(prefix))
        verifier = prefix / "bin/s31-bits-native-verifier"
        result = subprocess.run((str(verifier), str(proof), str(statement), str(forged_key)),
                                capture_output=True, text=True)
        if result.returncode != 1 or "error: InvalidVerificationKey" not in result.stderr:
            raise AssertionError(f"resealed {label} key bypassed embedded-source ABI check: "
                                 f"exit={result.returncode} {result.stderr}")


def raw_relation_controls(work: Path, relation: dict) -> None:
    """Exercise valid descriptors the source compiler intentionally cannot emit."""
    alias = copy.deepcopy(relation)
    alias["name"] = "bits_mixed_alias"
    output = alias["public_abi"]["result"]
    flag_wire = output["leaves"][0]["wire"]
    output["type"]["fields"].append(
        {"name": "again_as_m31", "type": {"kind": "m31", "length": 1}})
    output["leaves"].append({"path": [{"root": "result"}, {"field": "again_as_m31"}],
                             "wire": flag_wire, "kind": "m31", "length": 1})
    alias_source = work / "bits_mixed_alias.s31.json"
    write_json(alias_source, alias)
    alias_package = s31.build(alias_source, work / "mixed-alias-package", "direct-gate")
    alias_assignment = {"version": 2,
                        "public_inputs": {"request": {"flag": [0], "value": [7]}},
                        "private_inputs": {"other": [0]},
                        "result": {"flag": [1], "chosen": [7], "again_as_m31": [1]}}
    alias_path = work / "mixed-alias-assignment.json"
    alias_path.write_bytes(canonical(alias_assignment))
    alias_trial = s31.trial(alias_package, alias_path, work / "mixed-alias-trial")
    if not alias_trial["native_verifier_accepted"]:
        raise AssertionError("valid bit/M31 alias proof failed")
    alias_statement = json.loads((work / "mixed-alias-trial/statement.json").read_text())
    if alias["public_outputs"].count(flag_wire) != 1 or len(alias_statement["leaves"]) != 5:
        raise AssertionError("mixed-kind alias unexpectedly added a proof word")
    alias_statement["leaves"][4]["words"][0] = 0
    reject(alias_package / "bin/s31-bits_mixed_alias-native-verifier",
           work / "mixed-alias-trial/proof.bin", work / "mixed-alias-mutation.json",
           alias_package / "verification-key.json", canonical(alias_statement),
           "mixed-kind alias disagreement", "InvalidRecordStatement")

    unused = copy.deepcopy(relation)
    unused["name"] = "bits_unused_public"
    unused["inputs"].append({"name": "spare", "kind": "m31", "length": 1,
                             "visibility": "public"})
    unused["public_abi"]["inputs"].append(
        {"name": "spare", "type": {"kind": "bit", "length": 1},
         "visibility": "public",
         "leaves": [{"path": [{"root": "spare"}], "wire": "spare",
                     "kind": "bit", "length": 1}]})
    unused_source = work / "bits_unused_public.s31.json"
    write_json(unused_source, unused)
    unused_package = s31.build(unused_source, work / "unused-bit-package", "direct-gate")
    for bit in (0, 1):
        typed = {"version": 2,
                 "public_inputs": {"request": {"flag": [0], "value": [7]},
                                   "spare": [bit]},
                 "private_inputs": {"other": [0]},
                 "result": {"flag": [1], "chosen": [7]}}
        assignment_path = work / f"unused-bit-{bit}.json"
        assignment_path.write_bytes(canonical(typed))
        trial_dir = work / f"unused-bit-trial-{bit}"
        trial = s31.trial(unused_package, assignment_path, trial_dir)
        if not trial["native_verifier_accepted"]:
            raise AssertionError(f"unused public bit {bit} was not bound to the proof")
        changed = json.loads((trial_dir / "statement.json").read_text())
        flipped = copy.deepcopy(changed)
        flipped["leaves"][2]["words"][0] ^= 1
        reject(unused_package / "bin/s31-bits_unused_public-native-verifier",
               trial_dir / "proof.bin", work / f"unused-bit-flipped-{bit}.json",
               unused_package / "verification-key.json", canonical(flipped),
               "valid but changed unused public bit")
        changed["leaves"][2]["words"][0] = 2
        reject(unused_package / "bin/s31-bits_unused_public-native-verifier",
               trial_dir / "proof.bin", work / f"unused-bit-mutation-{bit}.json",
               unused_package / "verification-key.json", canonical(changed),
               "unused public bit outside Boolean range", "InvalidRecordStatement")


def source_passthrough_controls(work: Path) -> None:
    """Prove the source-level zero-node case that relies only on the v2 claim."""
    source_text = """struct Request { flag: bit }
struct Response { flag: bit }
circuit echo(public request: Request) -> public Response {
    Response { flag: request.flag }
}
"""
    source = work / "echo.s31"
    source.write_text(source_text)
    relation, _ = compile_text(source_text)
    wire = relation["inputs"][0]["name"]
    if (relation["version"] != 2 or relation["nodes"] != [] or
            relation["public_outputs"] != [wire] or
            relation["public_abi"]["inputs"][0]["leaves"][0]["kind"] != "bit" or
            relation["public_abi"]["result"]["leaves"][0]["kind"] != "bit"):
        raise AssertionError("source bit passthrough did not erase to one shared wire")
    package = s31.build(source, work / "echo-package", "direct-gate")
    verifier = package / "bin/s31-echo-native-verifier"
    key = package / "verification-key.json"
    for bit in (0, 1):
        typed = {"version": 2, "public_inputs": {"request": {"flag": [bit]}},
                 "private_inputs": {}, "result": {"flag": [bit]}}
        assignment = work / f"echo-{bit}.json"
        assignment.write_bytes(canonical(typed))
        trial_dir = work / f"echo-trial-{bit}"
        trial = s31.trial(package, assignment, trial_dir)
        if not trial["native_verifier_accepted"]:
            raise AssertionError(f"native zero-node bit passthrough rejected {bit}")
        proof = trial_dir / "proof.bin"
        statement = json.loads((trial_dir / "statement.json").read_text())
        for index in (0, 1):
            altered = copy.deepcopy(statement)
            altered["leaves"][index]["words"][0] = 2
            reject(verifier, proof, work / "echo-mutated-statement.json", key,
                   canonical(altered), f"passthrough bit leaf {index} outside range",
                   "InvalidRecordStatement")
        mismatched = copy.deepcopy(statement)
        mismatched["leaves"][1]["words"][0] ^= 1
        reject(verifier, proof, work / "echo-mutated-statement.json", key,
               canonical(mismatched), "passthrough alias mismatch",
               "InvalidRecordStatement")
        changed = copy.deepcopy(statement)
        for leaf in changed["leaves"]:
            leaf["words"][0] ^= 1
        reject(verifier, proof, work / "echo-mutated-statement.json", key,
               canonical(changed), "valid but changed passthrough public bit")
        flat = flat_assignment_from_typed(relation, canonical(typed))
        reject(verifier, proof, work / "echo-mutated-statement.json", key,
               canonical({"public_inputs": flat["public_inputs"],
                          "public_outputs": flat["public_outputs"]}),
               "passthrough v1 statement replay")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-public-bit-v2-") as temporary:
        work = Path(temporary)
        source = work / "bits.s31"
        source.write_text(SOURCE)
        relation, _ = compile_text(SOURCE)
        if relation["version"] != 2 or [node["op"] for node in relation["nodes"]] != [
                "is_zero", "select"]:
            raise AssertionError("public bit record lowered to an unexpected graph")
        input_leaves = relation["public_abi"]["inputs"][0]["leaves"]
        output_leaves = relation["public_abi"]["result"]["leaves"]
        if ([leaf["kind"] for leaf in input_leaves] != ["bit", "m31"] or
                [leaf["kind"] for leaf in output_leaves] != ["bit", "m31"]):
            raise AssertionError("typed bit leaf tag was lost")
        manual = {**relation, "version": 1, "name": "bits_flat"}
        del manual["public_abi"]
        manual_path = work / "bits_flat.s31.json"
        manual_path.write_bytes(canonical(manual))

        package = s31.build(source, work / "record-package", "direct-gate")
        flat_package = s31.build(manual_path, work / "flat-package", "direct-gate")
        record_cost = json.loads((package / "cost-report.json").read_text())
        flat_cost = json.loads((flat_package / "cost-report.json").read_text())
        for field in ("raw", "padded", "preprocessed_cells", "preprocessed_columns"):
            if record_cost[field] != flat_cost[field]:
                raise AssertionError(f"record grouping changed {field}")

        verifier = package / "bin/s31-bits-native-verifier"
        key = package / "verification-key.json"
        checked = 0
        first_proof: Path | None = None
        first_statement: Path | None = None
        for flag, other, expected_flag, chosen in ((0, 0, 1, 7), (1, 5, 0, 5)):
            typed = {"version": 2,
                     "public_inputs": {"request": {"flag": [flag], "value": [7]}},
                     "private_inputs": {"other": [other]},
                     "result": {"flag": [expected_flag], "chosen": [chosen]}}
            typed_path = work / f"typed-{flag}.json"
            typed_path.write_bytes(canonical(typed))
            flat = flat_assignment_from_typed(relation, canonical(typed))
            flat_path = work / f"flat-{flag}.json"
            write_json(flat_path, flat)
            if flag == 0:
                reject_raw_prover_bit(package, work, flat, input_leaves[0]["wire"],
                                      "public_inputs", "input-bit")
                reject_raw_prover_bit(package, work, flat, output_leaves[0]["wire"],
                                      "public_outputs", "output-bit")
            trial_dir = work / f"record-trial-{flag}"
            flat_trial_dir = work / f"flat-trial-{flag}"
            trial = s31.trial(package, typed_path, trial_dir)
            flat_trial = s31.trial(flat_package, flat_path, flat_trial_dir)
            if (not trial["native_verifier_accepted"] or
                    not trial["changed_public_statement_rejected"] or
                    not flat_trial["native_verifier_accepted"]):
                raise AssertionError("honest typed or flat bit proof did not verify")
            proof = trial_dir / "proof.bin"
            if first_proof is None:
                first_proof = proof
                first_statement = trial_dir / "statement.json"
            statement = json.loads((trial_dir / "statement.json").read_text())
            for at in (0, 2):
                for bad in (2, (1 << 31) - 2):
                    altered = copy.deepcopy(statement)
                    altered["leaves"][at]["words"][0] = bad
                    reject(verifier, proof, work / "mutated-statement.json", key,
                           canonical(altered), f"bit leaf {at} value {bad}",
                           "InvalidRecordStatement")
                    checked += 1
            flipped = copy.deepcopy(statement)
            flipped["leaves"][0]["words"][0] ^= 1
            reject(verifier, proof, work / "mutated-statement.json", key,
                   canonical(flipped), "valid changed public bit")
            checked += 1
            reject(verifier, proof, work / "mutated-statement.json", key,
                   canonical({"public_inputs": flat["public_inputs"],
                              "public_outputs": flat["public_outputs"]}),
                   "flat v1 statement replay")
            checked += 1

        if first_proof is None or first_statement is None:
            raise AssertionError("no honest bit proof was produced")
        adversarial_package_controls(work, package, relation, first_proof, first_statement)
        raw_relation_controls(work, relation)
        source_passthrough_controls(work)

        print(json.dumps({"schema": "s31-record-public-bit-v2-acceptance",
                          "native_honest_proofs": 2, "flat_parity_proofs": 2,
                          "native_rejected_mutations": checked,
                          "rehashed_bit_m31_sidecars_rejected": 2,
                          "resealed_bit_m31_keys_rejected": 2,
                          "mixed_kind_alias_rejected": True,
                          "unused_public_bit_range_checked": True,
                          "source_zero_node_bit_passthrough_bound": True,
                          "zero_extra_grouping_rows": True,
                          "raw": record_cost["raw"],
                          "padded": record_cost["padded"]},
                         indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
