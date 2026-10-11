#!/usr/bin/env python3
"""Nested record/tuple ABI v2: Python/native statement and alias controls."""

from __future__ import annotations

import argparse
import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from abi.binding_v2 import (binding_digest, decode_public_statement,
                            decode_typed_public_statement,
                            encode_typed_public_statement,
                            flat_assignment_from_typed,
                            statement_from_assignment)  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from text_frontend import compile_text  # noqa: E402

P = (1 << 31) - 1
EXPECTED_ABI_SHA256 = "15ca13f49eb16bde098aa42b8066325d1ab8f3ce4bdae386f03d2f297770a728"
SOURCE = """struct Inner { seed: [m31; 1] }
struct Request { pair: ([m31; 1], [m31; 1]), extra: Inner }
struct Mask { delta: [m31; 1] }
struct Result { nested: (Inner, [m31; 1]), copy: Inner }
circuit nested_alias(public req: Request, private mask: Mask) -> public Result {
    let y = req.pair.0 + req.pair.1 + req.extra.seed + mask.delta;
    Result { nested: (Inner { seed: y }, req.pair.0), copy: Inner { seed: y } }
}
"""


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def typed_case(a: int, b: int, c: int, secret: int) -> dict:
    result = (a + b + c + secret) % P
    return {"version": 2,
            "public_inputs": {"req": {"pair": [[a], [b]],
                                      "extra": {"seed": [c]}}},
            "private_inputs": {"mask": {"delta": [secret]}},
            "result": {"nested": [{"seed": [result]}, [a]],
                       "copy": {"seed": [result]}}}


def statement_mutations(honest: bytes) -> dict[str, bytes]:
    original = json.loads(honest)
    result: dict[str, bytes] = {}
    changed = copy.deepcopy(original)
    changed["leaves"][5]["words"] = [18]
    result["nested_output_alias"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"][4]["words"] = [3]
    result["input_output_alias"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"][4]["path"][2] = {"tuple": 0}
    result["tuple_index"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"][5]["path"][2] = {"field": "other"}
    result["field_name"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"][0], changed["leaves"][1] = changed["leaves"][1], changed["leaves"][0]
    result["same_shape_input_order"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"].append({"path": [{"root": "mask"}, {"field": "delta"}], "words": [7]})
    result["private_leaf"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"].pop()
    result["missing_leaf"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"][3]["words"] = [P]
    result["noncanonical_m31"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"][3]["words"] = [True]
    result["boolean_instead_of_word"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["abi_sha256"] = "0" * 64
    result["wrong_abi_digest"] = canonical(changed)
    changed = copy.deepcopy(original)
    nested: object = "req"
    for _ in range(256):
        nested = [nested]
    changed["leaves"][0]["path"][0]["root"] = nested
    result["deep_path"] = canonical(changed)
    result["duplicate_envelope_key"] = honest.replace(b'"version":2', b'"version":2,"version":2')
    result["duplicate_nested_path_key"] = honest.replace(
        b'{"tuple":0}', b'{"tuple":0,"tuple":0}', 1)
    result["noncanonical_spacing"] = (json.dumps(original, indent=2) + "\n").encode()
    result["missing_final_newline"] = honest[:-1]
    result["oversized_statement"] = honest + b" " * (1_000_001 - len(honest))
    return result


def canonical_wrong_claims(source: dict, honest: bytes) -> dict[str, bytes]:
    """Keep the record ABI valid while changing one bound public proof word."""
    base = {**source, "version": 1}
    boundary = base.pop("public_abi")
    original = json.loads(honest)
    original_words = decode_public_statement(base, boundary, honest)
    result: dict[str, bytes] = {}
    changed = copy.deepcopy(original)
    changed["leaves"][0]["words"] = [4]
    changed["leaves"][4]["words"] = [4]
    result["input_and_result_alias"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"][1]["words"] = [4]
    result["second_tuple_input"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"][2]["words"] = [6]
    result["nested_record_input"] = canonical(changed)
    changed = copy.deepcopy(original)
    changed["leaves"][3]["words"] = [18]
    changed["leaves"][5]["words"] = [18]
    result["both_result_aliases"] = canonical(changed)
    for label, encoded in result.items():
        words = decode_public_statement(base, boundary, encoded)
        if words == original_words:
            raise AssertionError(f"canonical wrong claim {label} did not change proof words")
    return result


def invalid_typed_assignments(honest: dict) -> dict[str, bytes]:
    result: dict[str, bytes] = {}
    changed = copy.deepcopy(honest)
    changed["result"]["copy"]["seed"] = [18]
    result["nested_result_alias"] = canonical(changed)
    changed = copy.deepcopy(honest)
    changed["result"]["nested"][1] = [3]
    result["input_result_alias"] = canonical(changed)
    changed = copy.deepcopy(honest)
    del changed["public_inputs"]["req"]["extra"]
    result["missing_nested_field"] = canonical(changed)
    changed = copy.deepcopy(honest)
    changed["public_inputs"]["req"]["pair"].append([9])
    result["wrong_tuple_arity"] = canonical(changed)
    changed = copy.deepcopy(honest)
    changed["public_inputs"]["mask"] = changed["private_inputs"]["mask"]
    result["private_root_as_public"] = canonical(changed)
    changed = copy.deepcopy(honest)
    changed["private_inputs"]["mask"]["delta"] = [P]
    result["noncanonical_private_word"] = canonical(changed)
    result["duplicate_nested_field"] = canonical(honest).replace(
        b'"seed":[5]', b'"seed":[5],"seed":[5]', 1)
    result["duplicate_envelope_key"] = canonical(honest).replace(
        b'"version":2', b'"version":2,"version":2', 1)
    changed = copy.deepcopy(honest)
    nested: object = [2]
    for _ in range(256):
        nested = [nested]
    changed["public_inputs"]["req"]["pair"][0] = nested
    result["deeply_nested_value"] = canonical(changed)
    return result


def static_checks() -> tuple[dict, dict, bytes, list[str], list[str], list[str]]:
    source, _ = compile_text(SOURCE)
    flat_source = {**source, "version": 1}
    boundary = flat_source.pop("public_abi")
    if (source["version"] != 2 or
            [node["op"] for node in source["nodes"]] != ["add"] * 3 or
            [leaf["wire"] for leaf in boundary["result"]["leaves"]] !=
            ["y", "_s31_abi_input_0", "y"] or
            source["public_outputs"] != ["y", "_s31_abi_input_0"] or
            binding_digest(flat_source, boundary) != EXPECTED_ABI_SHA256):
        raise AssertionError("nested alias source or declared ABI changed")
    typed = typed_case(2, 3, 5, 7)
    flat = flat_assignment_from_typed(source, canonical(typed))
    if flat != {"public_inputs": {"_s31_abi_input_0": [2],
                                  "_s31_abi_input_1": [3],
                                  "_s31_abi_input_2": [5]},
                "private_inputs": {"_s31_abi_input_3": [7]},
                "public_outputs": {"y": [17], "_s31_abi_input_0": [2]}}:
        raise AssertionError("typed nested assignment did not flatten to declared wires")
    statement = statement_from_assignment(source, flat)
    claim = decode_typed_public_statement(source, statement)
    expected_claim = {"version": 2, "abi_sha256": EXPECTED_ABI_SHA256,
                      "public_inputs": typed["public_inputs"], "result": typed["result"]}
    if (claim != expected_claim or
            encode_typed_public_statement(source, claim) != statement or
            decode_public_statement(flat_source, boundary, statement) !=
            [2, 3, 5, 17, 2, 0, 0, 0]):
        raise AssertionError("typed and flat canonical statement bytes or proof words disagree")
    statement_cases = statement_mutations(statement)
    for label, payload in statement_cases.items():
        try:
            decode_public_statement(flat_source, boundary, payload)
        except AbiError:
            pass
        else:
            raise AssertionError(f"Python statement parser accepted {label}")
    wrong_claims = canonical_wrong_claims(source, statement)
    typed_cases = invalid_typed_assignments(typed)
    for label, payload in typed_cases.items():
        try:
            flat_assignment_from_typed(source, payload)
        except AbiError:
            pass
        else:
            raise AssertionError(f"typed assignment adapter accepted {label}")
    return source, flat, statement, list(statement_cases), list(wrong_claims), list(typed_cases)


def native_reject(verifier: Path, proof: Path, key: Path, scratch: Path,
                  payload: bytes, label: str) -> None:
    scratch.write_bytes(payload)
    result = subprocess.run((str(verifier), str(proof), str(scratch), str(key)),
                            capture_output=True, text=True)
    if (result.returncode != 1 or "error:" not in result.stderr or
            "panic:" in result.stderr):
        raise AssertionError(f"native verifier did not reject {label} cleanly: "
                             f"exit={result.returncode}, stderr={result.stderr}")


def native_checks() -> dict:
    source, _, honest_statement, statement_labels, wrong_claim_labels, typed_labels = static_checks()
    with tempfile.TemporaryDirectory(prefix="s31-nested-record-abi-v2-") as temporary:
        work = Path(temporary)
        source_path = work / "nested_alias.s31"
        source_path.write_text(SOURCE)
        package = s31.build(source_path, work / "package", "direct-gate")
        key_path = package / "verification-key.json"
        key = json.loads(key_path.read_bytes())
        if (key.get("schema") != "s31-verification-key-direct-record-v2" or
                key.get("public_abi_sha256") != EXPECTED_ABI_SHA256 or
                json.loads((package / "source.s31.json").read_bytes()) != source):
            raise AssertionError("native package or sealed record ABI differs from Python source")
        verifier = package / "bin/s31-nested_alias-native-verifier"
        trials = []
        for index, typed in enumerate((typed_case(2, 3, 5, 7),
                                       typed_case(P - 2, P - 1, 1, 3))):
            assignment = work / f"assignment-{index}.json"
            assignment.write_bytes(canonical(typed))
            report = s31.trial(package, assignment, work / f"trial-{index}")
            if (report["native_verifier_accepted"] is not True or
                    not report["changed_public_statement_rejected"] or
                    report["independent_value_oracle"]["status"] != "passed"):
                raise AssertionError(f"nested alias native trial {index} lacked proof or value controls")
            encoded = (work / f"trial-{index}/statement.json").read_bytes()
            flat = flat_assignment_from_typed(source, canonical(typed))
            if (encoded != statement_from_assignment(source, flat) or
                    encoded != encode_typed_public_statement(
                        source, {"version": 2, "abi_sha256": EXPECTED_ABI_SHA256,
                                 "public_inputs": typed["public_inputs"],
                                 "result": typed["result"]})):
                raise AssertionError("native-accepted statement differs from both Python encoders")
            trials.append({"public_inputs": typed["public_inputs"],
                           "result": typed["result"], "proof_bytes": report["proof_bytes"]})
        proof = work / "trial-0/proof.bin"
        s31.invoke(str(verifier), str(proof), str(work / "trial-0/statement.json"),
                   str(key_path))
        for label, payload in statement_mutations(honest_statement).items():
            native_reject(verifier, proof, key_path, work / "mutated-statement.json",
                          payload, label)
        for label, payload in canonical_wrong_claims(source, honest_statement).items():
            scratch = work / "canonical-wrong-claim.json"
            scratch.write_bytes(payload)
            result = subprocess.run((str(verifier), str(proof), str(scratch), str(key_path)),
                                    capture_output=True, text=True)
            if (result.returncode != 1 or "error:" not in result.stderr or
                    "InvalidRecordStatement" in result.stderr or
                    "InvalidRecordAbi" in result.stderr or "panic:" in result.stderr):
                raise AssertionError(f"native verifier did not reject canonical wrong "
                                     f"claim {label} at proof binding: "
                                     f"exit={result.returncode}, stderr={result.stderr}")
        return {"schema": "s31-nested-record-alias-v2-acceptance-v1",
                "native_proofs_accepted": len(trials),
                "native_statement_mutations_rejected": statement_labels,
                "native_canonical_wrong_claims_rejected": wrong_claim_labels,
                "typed_assignments_rejected": typed_labels,
                "python_native_canonical_statement_bytes_agree": True,
                "public_abi_sha256": EXPECTED_ABI_SHA256,
                "trials": trials}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static", action="store_true",
                        help="run source, codec, and adversarial controls without a native build")
    args = parser.parse_args()
    if args.static:
        _, _, _, statements, wrong_claims, assignments = static_checks()
        result = {"schema": "s31-nested-record-alias-v2-static-v1",
                  "python_statement_mutations_rejected": statements,
                  "python_canonical_wrong_claims_accepted": wrong_claims,
                  "typed_assignments_rejected": assignments,
                  "public_abi_sha256": EXPECTED_ABI_SHA256}
    else:
        result = native_checks()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
