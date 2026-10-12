#!/usr/bin/env python3
"""Source-to-native ABI seal for nested public u8/u16 fields.

Two valid source programs have the same flat arithmetic relation and public
words, but different named field paths. A proof for either ABI must not replay
under the other's independently generated verifier and key.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from abi.binding_v2 import (binding_digest, decode_public_statement,
                            flat_assignment_from_typed, statement_from_assignment)  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from text_frontend import compile_text  # noqa: E402

P = (1 << 31) - 1
EXPECTED_SOURCE_SHA256 = (
    "bd98e9d3259c14f3213f69fe582d205bb928b2a22a7057ca466ba71f8d8c606f",
    "8d5987691283a5747adbc963b4b426bb3e6bd2aa2b421f8c9295cb08c030c8cb",
)
EXPECTED_ABI_SHA256 = (
    "2e19e07033e29108695e4357ca12c30074b2b401f5f5ef1fa167b12fdbfa9c3c",
    "85300e78538a2fc8336e095333f9ee6279db8b8b0b821b0781e27385375b6387",
)
SOURCE = """struct Inner { byte: u8, digit: [u16; 1] }
struct Request { pair: (Inner, [m31; 1]) }
struct Copy { byte: u8, digit: [u16; 1] }
struct Result { copy: Copy, again: [u16; 1], sum: [m31; 1] }
circuit nested_narrow(public req: Request) -> public Result {
 let byte_limb = std::int::limbs(req.pair.0.byte);
 let byte_field = std::field::from_u16(byte_limb);
 let digit_field = std::field::from_u16(req.pair.0.digit);
 let sum = byte_field + digit_field + req.pair.1;
 Result { copy: Copy { byte: req.pair.0.byte, digit: req.pair.0.digit }, again: req.pair.0.digit, sum: sum }
}
"""


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")


def renamed_source() -> str:
    # Alter the input's named field and its two uses. Result paths, relation
    # wire names, operations, values, and number of public words stay fixed.
    return (SOURCE.replace("struct Inner { byte: u8, digit:",
                           "struct Inner { byte: u8, value:")
            .replace("req.pair.0.digit", "req.pair.0.value"))


def assignment(byte: int, digit: int, salt: int, *, renamed: bool) -> dict:
    inner = {"byte": [byte], "value" if renamed else "digit": [digit]}
    return {"version": 2, "public_inputs": {"req": {"pair": [inner, [salt]]}},
            "private_inputs": {},
            "result": {"copy": {"byte": [byte], "digit": [digit]},
                       "again": [digit], "sum": [(byte + digit + salt) % P]}}


def relation_and_abi(source: dict) -> tuple[dict, dict]:
    relation = {**source, "version": 1}
    abi = relation.pop("public_abi")
    return relation, abi


def path(leaf: dict) -> tuple[tuple[str, object], ...]:
    return tuple((key, value) for part in leaf["path"] for key, value in part.items())


def reject_python(relation: dict, abi: dict, payload: bytes, label: str) -> None:
    try:
        decode_public_statement(relation, abi, payload)
    except AbiError:
        return
    raise AssertionError(f"Python statement decoder accepted {label}")


def static_checks() -> tuple[dict, dict, bytes, bytes]:
    a, _ = compile_text(SOURCE)
    b, _ = compile_text(renamed_source())
    flat_a, abi_a = relation_and_abi(a)
    flat_b, abi_b = relation_and_abi(b)
    if flat_a != flat_b:
        raise AssertionError("renaming a source field changed the flat arithmetic relation")
    if ([node["op"] for node in a["nodes"]] !=
            ["cast_m31", "cast_m31", "add", "add"] or
            [(item["kind"], item["length"], item["visibility"]) for item in a["inputs"]] !=
            [("u16", 1, "public"), ("u16", 1, "public"), ("m31", 1, "public")]):
        raise AssertionError("nested narrow source lowered to an unexpected relation")
    roots_a = abi_a["inputs"][0]["leaves"]
    roots_b = abi_b["inputs"][0]["leaves"]
    outputs = abi_a["result"]["leaves"]
    expected_input_paths = (
        (("root", "req"), ("field", "pair"), ("tuple", 0), ("field", "byte")),
        (("root", "req"), ("field", "pair"), ("tuple", 0), ("field", "digit")),
        (("root", "req"), ("field", "pair"), ("tuple", 1)),
    )
    expected_output_paths = (
        (("root", "result"), ("field", "copy"), ("field", "byte")),
        (("root", "result"), ("field", "copy"), ("field", "digit")),
        (("root", "result"), ("field", "again")),
        (("root", "result"), ("field", "sum")),
    )
    if (tuple(map(path, roots_a)) != expected_input_paths or
            path(roots_b[1]) != expected_input_paths[1][:-1] + (("field", "value"),) or
            tuple(map(path, outputs)) != expected_output_paths or
            tuple(map(path, abi_b["result"]["leaves"])) != expected_output_paths or
            [leaf["kind"] for leaf in roots_a] != ["u8", "u16", "m31"] or
            [leaf["kind"] for leaf in outputs] != ["u8", "u16", "u16", "m31"] or
            [leaf["wire"] for leaf in outputs] !=
            [a["inputs"][0]["name"], a["inputs"][1]["name"],
             a["inputs"][1]["name"], "sum"]):
        raise AssertionError("nested paths, tags, or alias wires differ from handwritten layout")
    digest_a = binding_digest(flat_a, abi_a)
    digest_b = binding_digest(flat_b, abi_b)
    source_hashes = tuple(hashlib.sha256(text.encode()).hexdigest()
                          for text in (SOURCE, renamed_source()))
    if ((digest_a, digest_b) != EXPECTED_ABI_SHA256 or
            source_hashes != EXPECTED_SOURCE_SHA256 or
            hashlib.sha256(canonical(a)).digest() == hashlib.sha256(canonical(b)).digest()):
        raise AssertionError("different named ABIs have identical descriptor/source identities")
    case_a = assignment(255, 65535, P - 2, renamed=False)
    case_b = assignment(255, 65535, P - 2, renamed=True)
    assigned_a = flat_assignment_from_typed(a, canonical(case_a))
    assigned_b = flat_assignment_from_typed(b, canonical(case_b))
    if assigned_a != assigned_b:
        raise AssertionError("renamed field changed the flat assignment")
    if evaluate_relation(flat_a, assigned_a) != assigned_a["public_outputs"]:
        raise AssertionError("independent relation oracle differs from handwritten modular sum")
    statement_a = statement_from_assignment(a, assigned_a)
    statement_b = statement_from_assignment(b, assigned_b)
    expected_padded_words = [255, 65535, P - 2, 255, 65535, 65788, 0, 0]
    if (decode_public_statement(flat_a, abi_a, statement_a) != expected_padded_words or
            decode_public_statement(flat_b, abi_b, statement_b) != expected_padded_words):
        raise AssertionError("different named statements did not project to the same six live plus two padding words")
    reject_python(flat_a, abi_a, statement_b, "renamed input field")
    reject_python(flat_b, abi_b, statement_a, "old input field")
    mutated = json.loads(statement_a)
    mutated["version"] = 1
    reject_python(flat_a, abi_a, canonical(mutated), "wrong version")
    mutated = json.loads(statement_a)
    mutated["leaves"][5]["words"] = [65534]
    reject_python(flat_a, abi_a, canonical(mutated), "split u16 result alias")
    mutated = json.loads(statement_a)
    mutated["leaves"][0]["words"] = [256]
    mutated["leaves"][3]["words"] = [256]
    reject_python(flat_a, abi_a, canonical(mutated), "out-of-range public u8")
    mutated = json.loads(statement_a)
    mutated["leaves"][1]["words"] = [65536]
    mutated["leaves"][4]["words"] = [65536]
    mutated["leaves"][5]["words"] = [65536]
    reject_python(flat_a, abi_a, canonical(mutated), "out-of-range public u16")
    return a, b, statement_a, statement_b


def verifier_run(verifier: Path, proof: Path, statement: Path, key: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run((str(verifier), str(proof), str(statement), str(key)),
                          capture_output=True, text=True, check=False)


def native_checks(a: dict, b: dict, statement_a: bytes, statement_b: bytes) -> dict:
    with tempfile.TemporaryDirectory(prefix="s31-nested-narrow-seal-v2-") as temporary:
        work = Path(temporary)
        source_a = work / "a.s31"
        source_b = work / "b.s31"
        source_a.write_text(SOURCE)
        source_b.write_text(renamed_source())
        package_a = s31.build(source_a, work / "package-a", "direct-gate")
        package_b = s31.build(source_b, work / "package-b", "direct-gate")
        key_a_path = package_a / "verification-key.json"
        key_b_path = package_b / "verification-key.json"
        key_a = json.loads(key_a_path.read_bytes())
        key_b = json.loads(key_b_path.read_bytes())
        if (json.loads((package_a / "source.s31.json").read_bytes()) != a or
                json.loads((package_b / "source.s31.json").read_bytes()) != b or
                key_a["schema"] != "s31-verification-key-direct-record-v2" or
                key_b["schema"] != "s31-verification-key-direct-record-v2"):
            raise AssertionError("native packages differ from source-derived v2 programs")
        for field in ("public_abi_sha256", "canonical_ir_sha256", "program_sha256"):
            if key_a[field] == key_b[field]:
                raise AssertionError(f"valid named field rename kept {field}")
        if (key_a["padded"] != key_b["padded"] or
                key_a["trace_log_size"] != key_b["trace_log_size"]):
            raise AssertionError("field rename unexpectedly changed direct-gate AIR geometry")
        claim_a = work / "claim-a.json"
        claim_b = work / "claim-b.json"
        claim_a.write_bytes(canonical(assignment(255, 65535, P - 2, renamed=False)))
        claim_b.write_bytes(canonical(assignment(255, 65535, P - 2, renamed=True)))
        trial_a = s31.trial(package_a, claim_a, work / "trial-a")
        trial_b = s31.trial(package_b, claim_b, work / "trial-b")
        if (not trial_a["native_verifier_accepted"] or
                not trial_b["native_verifier_accepted"] or
                not trial_a["changed_public_statement_rejected"] or
                not trial_b["changed_public_statement_rejected"] or
                trial_a["independent_value_oracle"]["status"] != "passed" or
                trial_b["independent_value_oracle"]["status"] != "passed"):
            raise AssertionError("honest native proof or value oracle failed")
        proof_a = work / "trial-a/proof.bin"
        proof_b = work / "trial-b/proof.bin"
        verifier_a = package_a / "bin/s31-nested_narrow-native-verifier"
        verifier_b = package_b / "bin/s31-nested_narrow-native-verifier"
        path_a = work / "trial-a/statement.json"
        path_b = work / "trial-b/statement.json"
        if path_a.read_bytes() != statement_a or path_b.read_bytes() != statement_b:
            raise AssertionError("native trial statement differs from independent ABI projection")
        # Both (statement, key) pairs are independently valid and accepted
        # with their own proofs. Cross-verification therefore tests proof
        # binding beyond parser rejection, with identical public words.
        cross_errors = []
        for verifier, proof, statement, key in (
                (verifier_b, proof_a, path_b, key_b_path),
                (verifier_a, proof_b, path_a, key_a_path)):
            result = verifier_run(verifier, proof, statement, key)
            if (result.returncode != 1 or
                    "error: InvalidInteractionNonce" not in result.stderr or
                    "panic:" in result.stderr):
                raise AssertionError("cross-ABI proof replay did not fail inside native proof verification: "
                                     f"exit={result.returncode}, stderr={result.stderr}")
            cross_errors.append(result.stderr.strip().splitlines()[-1])
        # A key with the alternate ABI digest cannot authorize the original
        # embedded source, even though arithmetic and padded AIR match.
        forged_key = copy.deepcopy(key_a)
        forged_key["public_abi_sha256"] = key_b["public_abi_sha256"]
        forged_path = work / "forged-key.json"
        forged_path.write_bytes(canonical(forged_key))
        invalid_key = verifier_run(verifier_a, proof_a, path_a, forged_path)
        if (invalid_key.returncode != 1 or
                "error: InvalidVerificationKey" not in invalid_key.stderr):
            raise AssertionError("native verifier accepted a resealed ABI digest over old source")
        mutated = json.loads(statement_a)
        cases = {}
        mutated["version"] = 1
        cases["wrong_statement_version"] = canonical(mutated)
        mutated = json.loads(statement_a)
        mutated["leaves"][1]["path"][-1]["field"] = "value"
        cases["wrong_nested_field_path"] = canonical(mutated)
        mutated = json.loads(statement_a)
        mutated["leaves"][1], mutated["leaves"][2] = mutated["leaves"][2], mutated["leaves"][1]
        cases["wrong_leaf_order"] = canonical(mutated)
        mutated = json.loads(statement_a)
        mutated["leaves"][0]["words"] = [256]
        mutated["leaves"][3]["words"] = [256]
        cases["out_of_range_u8"] = canonical(mutated)
        mutated = json.loads(statement_a)
        mutated["leaves"][1]["words"] = [65536]
        mutated["leaves"][4]["words"] = [65536]
        mutated["leaves"][5]["words"] = [65536]
        cases["out_of_range_u16"] = canonical(mutated)
        for label, payload in cases.items():
            bad_path = work / f"{label}.json"
            bad_path.write_bytes(payload)
            result = verifier_run(verifier_a, proof_a, bad_path, key_a_path)
            if result.returncode != 1 or "error: InvalidRecordStatement" not in result.stderr:
                raise AssertionError(f"native parser admitted {label}: {result.stderr}")
        return {"native_honest_proofs": 2,
                "native_cross_abi_replays_rejected_after_statement_validation": 2,
                "native_forged_abi_key_rejected": True,
                "native_malformed_statement_rejections": len(cases),
                "cross_replay_errors": cross_errors,
                "proof_bytes": [trial_a["proof_bytes"], trial_b["proof_bytes"]],
                "same_padded_air_geometry": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="build two packages, prove, verify, and cross-replay")
    args = parser.parse_args()
    a, b, statement_a, statement_b = static_checks()
    report = {"schema": "s31-nested-narrow-record-seal-v2",
              "source_programs": 2, "same_flat_relation": True,
              "same_six_live_public_words_plus_two_padding_words": True,
              "different_public_abi_digests": True,
              "source_sha256": list(EXPECTED_SOURCE_SHA256),
              "public_abi_sha256": list(EXPECTED_ABI_SHA256)}
    if args.native:
        report.update(native_checks(a, b, statement_a, statement_b))
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
