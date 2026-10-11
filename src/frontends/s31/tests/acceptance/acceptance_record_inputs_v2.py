#!/usr/bin/env python3
"""Native v2 record inputs, strict typed assignments, and flat AIR parity."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from abi.binding_v2 import flat_assignment_from_typed
from abi.record_v2 import AbiError
from package.context import BUILD_FILE, write_json
from text_frontend import compile_text

SOURCE = """struct Pair { left: [m31; 1], right: [m31; 1] }
struct Request { pair: Pair, tail: ([m31; 1], [m31; 1]) }
circuit sum(public request: Request, private mask: Pair) -> public [m31; 1] {
    request.pair.left + request.pair.right + request.tail.0 +
    request.tail.1 + mask.left + mask.right
}
"""

TYPED = {"version": 2,
         "public_inputs": {"request": {"pair": {"left": [2], "right": [3]},
                                       "tail": [[4], [5]]}},
         "private_inputs": {"mask": {"left": [6], "right": [7]}},
         "result": [27]}


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def reject(verifier: Path, proof: Path, key: Path, scratch: Path,
           statement: bytes, label: str) -> None:
    scratch.write_bytes(statement)
    result = subprocess.run((str(verifier), str(proof), str(scratch), str(key)),
                            capture_output=True, text=True)
    expected = ("error:" if label in {"public_input_word", "public_result_word"}
                else "InvalidRecordStatement")
    if result.returncode != 1 or expected not in result.stderr:
        raise AssertionError(f"native verifier did not reject {label} cleanly: "
                             f"exit={result.returncode} {result.stderr}")


def reject_resealed_visibility_key(work: Path, package: Path, relation: dict,
                                   proof: Path, statement: Path) -> None:
    """A key digest for a publicized private root must fail native resealing."""
    boundary = copy.deepcopy(relation["public_abi"])
    private_roots = [root for root in boundary["inputs"] if root["visibility"] == "private"]
    if len(private_roots) != 1 or private_roots[0]["name"] != "mask":
        raise AssertionError("visibility control requires the private mask input")
    private_roots[0]["visibility"] = "public"
    forged_digest = hashlib.sha256(
        b"s31-public-record-boundary-v2\0" + canonical(boundary)).hexdigest()
    forged = copy.deepcopy(json.loads((package / "verification-key.json").read_text()))
    if forged_digest == forged["public_abi_sha256"]:
        raise AssertionError("visibility mutation left the ABI digest unchanged")
    forged["public_abi_sha256"] = forged_digest
    forged_path = work / "forged-visibility-key.json"
    write_json(forged_path, forged)
    prefix = work / "forged-visibility-sealed"
    s31.invoke(
        "zig", "build", "--build-file", str(BUILD_FILE), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=1", "-Ds31-lowering=direct-gate",
        f"-Ds31-source={(package / 'source.s31.json').resolve()}", "-Ds31-name=sum",
        f"-Ds31-key={forged_path}",
        f"-Ds31-stdlib-sha256={forged['stdlib_lock_sha256']}",
        "--prefix", str(prefix),
    )
    verifier = prefix / "bin/s31-sum-native-verifier"
    result = subprocess.run((str(verifier), str(proof), str(statement), str(forged_path)),
                            capture_output=True, text=True)
    if result.returncode != 1 or "error: InvalidVerificationKey" not in result.stderr:
        raise AssertionError("native verifier accepted or mishandled a re-sealed key "
                             f"with forged input visibility: exit={result.returncode} {result.stderr}")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-input-v2-") as temporary:
        work = Path(temporary)
        source = work / "sum.s31"
        source.write_text(SOURCE)
        relation, _ = compile_text(SOURCE)
        if relation["version"] != 2 or len(relation["inputs"]) != 6:
            raise AssertionError("record input did not flatten into six first-order wires")
        flat = flat_assignment_from_typed(relation, canonical(TYPED))
        if len(flat["public_inputs"]) != 4 or len(flat["private_inputs"]) != 2:
            raise AssertionError("record input visibility or field order was lost")
        typed_path = work / "typed-assignment.json"
        typed_path.write_bytes(canonical(TYPED))
        flat_path = work / "flat-assignment.json"
        flat_path.write_bytes(canonical(flat))
        manual = {**relation, "version": 1, "name": "sum_flat"}
        del manual["public_abi"]
        manual_path = work / "sum_flat.s31.json"
        manual_path.write_text(json.dumps(manual, sort_keys=True, indent=2) + "\n")
        package = s31.build(source, work / "record-package", "direct-gate")
        flat_package = s31.build(manual_path, work / "flat-package", "direct-gate")
        cost = json.loads((package / "cost-report.json").read_text())
        flat_cost = json.loads((flat_package / "cost-report.json").read_text())
        for field in ("raw", "padded", "preprocessed_cells", "preprocessed_columns"):
            if cost[field] != flat_cost[field]:
                raise AssertionError(f"record input changed {field} AIR cost")
        trial = s31.trial(package, typed_path, work / "typed-trial")
        if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
            raise AssertionError("typed record input proof or changed claim control failed")
        inspected = subprocess.run((sys.executable, str(S31 / "python/s31.py"),
                                    "inspect-record-proof", str(package),
                                    str(work / "typed-trial/proof.bin"), "--statement",
                                    str(work / "typed-trial/statement.json")),
                                   capture_output=True, text=True, check=True)
        verified_claim = json.loads(inspected.stdout)
        if (verified_claim["proof_verified"] is not True or
                verified_claim["claim"]["public_inputs"] != TYPED["public_inputs"] or
                verified_claim["claim"]["result"] != TYPED["result"] or
                "mask" in verified_claim["claim"]["public_inputs"]):
            raise AssertionError("verified record claim did not reconstruct the named public values")
        flat_trial = s31.trial(flat_package, flat_path, work / "flat-trial")
        if not flat_trial["native_verifier_accepted"]:
            raise AssertionError("manual flat v1 proof failed")
        proof = work / "typed-trial/proof.bin"
        key = package / "verification-key.json"
        verifier = package / "bin/s31-sum-native-verifier"
        honest = json.loads((work / "typed-trial/statement.json").read_text())
        mutations: dict[str, bytes] = {}
        changed = copy.deepcopy(honest)
        changed["leaves"][0]["words"][0] += 1
        mutations["public_input_word"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][-1]["words"][0] += 1
        mutations["public_result_word"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][0], changed["leaves"][1] = changed["leaves"][1], changed["leaves"][0]
        mutations["same_type_field_order"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"].append({"path": [{"root": "mask"}, {"field": "left"}], "words": [6]})
        mutations["private_leaf_in_statement"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["leaves"][-1]["path"][0]["root"] = "request"
        mutations["result_root"] = canonical(changed)
        changed = copy.deepcopy(honest)
        changed["abi_sha256"] = "0" * 64
        mutations["abi_digest"] = canonical(changed)
        for label, payload in mutations.items():
            reject(verifier, proof, key, work / "mutated-statement.json", payload, label)
        reject_resealed_visibility_key(work, package, relation, proof,
                                       work / "typed-trial/statement.json")
        invalid: dict[str, dict] = {}
        wrong = copy.deepcopy(TYPED)
        del wrong["public_inputs"]["request"]["pair"]["right"]
        invalid["missing_nested_field"] = wrong
        wrong = copy.deepcopy(TYPED)
        wrong["private_inputs"]["mask"]["left"] = [2**31 - 1]
        invalid["noncanonical_private_word"] = wrong
        wrong = copy.deepcopy(TYPED)
        wrong["public_inputs"]["mask"] = wrong["private_inputs"]["mask"]
        invalid["private_root_in_public_inputs"] = wrong
        wrong = copy.deepcopy(TYPED)
        wrong["public_inputs"]["request"]["tail"].append([8])
        invalid["wrong_tuple_arity"] = wrong
        for label, value in invalid.items():
            try:
                flat_assignment_from_typed(relation, canonical(value))
            except AbiError:
                pass
            else:
                raise AssertionError(f"typed assignment accepted {label}")
        duplicate = canonical(TYPED).replace(b'"version":2', b'"version":2,"version":2')
        try:
            flat_assignment_from_typed(relation, duplicate)
        except AbiError:
            pass
        else:
            raise AssertionError("typed assignment accepted a duplicate JSON key")
        print(json.dumps({
            "schema": "s31-record-input-v2-acceptance",
            "native_typed_proof_accepted": True,
            "verified_named_claim_inspected": True,
            "manual_flat_v1_proof_accepted": True,
            "rejected_statement_mutations": list(mutations),
            "resealed_input_visibility_key_rejected": True,
            "rejected_typed_assignments": list(invalid) + ["duplicate_json_key"],
            "zero_extra_arithmetic_rows": True,
            "raw": cost["raw"], "padded": cost["padded"],
            "public_abi_sha256": cost["public_abi_sha256"],
        }, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
