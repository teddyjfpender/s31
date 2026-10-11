#!/usr/bin/env python3
"""Public u8 record words: arithmetic AIR range proof and native controls."""

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
                            encode_typed_public_statement,
                            flat_assignment_from_typed,
                            statement_from_assignment,
                            validate_binding)  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from package.context import BUILD_FILE, abi as package_abi  # noqa: E402
from text_frontend import compile_file  # noqa: E402

P = (1 << 31) - 1
EXAMPLE = S31 / "examples/arithmetic/record_public_u8.s31"
MIXED_REJECTED = S31 / "tests/acceptance/record_abi/public_u8_mixed_rejected.s31"


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def claim(byte: int, salt: int = 3) -> dict:
    return {"version": 2, "public_inputs": {"req": {"byte": [byte], "salt": [salt]}},
            "private_inputs": {},
            "result": {"byte": [byte], "square": [(byte * byte + salt) % P]}}


def derived_u8_result(source: dict) -> dict:
    """Construct a well-typed relation whose u8 output has a new producer."""
    changed = copy.deepcopy(source)
    input_wire = changed["inputs"][0]["name"]
    changed["nodes"].extend((
        {"name": "zero_selector", "op": "constant", "length": 1, "constant": 0},
        {"name": "selected_byte", "op": "select", "selector": "zero_selector",
         "lhs": input_wire, "rhs": input_wire},
    ))
    changed["public_outputs"][0] = "selected_byte"
    changed["public_abi"]["result"]["leaves"][0]["wire"] = "selected_byte"
    return changed


def mismatched_result_tag(source: dict) -> dict:
    changed = copy.deepcopy(source)
    changed["public_abi"]["result"]["type"]["fields"][0]["type"]["kind"] = "u16"
    changed["public_abi"]["result"]["leaves"][0]["kind"] = "u16"
    return changed


def widened_boundary_tag(source: dict) -> dict:
    changed = mismatched_result_tag(source)
    changed["public_abi"]["inputs"][0]["type"]["fields"][0]["type"]["kind"] = "u16"
    changed["public_abi"]["inputs"][0]["leaves"][0]["kind"] = "u16"
    return changed


def private_byte_input(source: dict) -> dict:
    changed = copy.deepcopy(source)
    changed["inputs"][0]["visibility"] = "private"
    changed["public_abi"]["inputs"][0]["visibility"] = "private"
    return changed


def static_checks() -> tuple[dict, dict, dict]:
    source, _ = compile_file(EXAMPLE)
    mixed_source, _ = compile_file(MIXED_REJECTED)
    if (mixed_source["version"] != 2 or
            [node["op"] for node in mixed_source["nodes"]] !=
            ["cast_m31", "array_concat", "array_concat", "repeat"] or
            mixed_source["inputs"][0]["kind"] != "u16" or
            mixed_source["public_abi"]["inputs"][0]["leaves"][0]["kind"] != "u8"):
        raise AssertionError("u8 chip admission fixture changed shape")
    if json.loads(MIXED_REJECTED.with_suffix(".s31.json").read_bytes()) != mixed_source:
        raise AssertionError("native mixed-admission fixture differs from text frontend")
    for candidate in (source, mixed_source):
        try:
            package_abi(candidate, "direct-chip")
        except ValueError:
            pass
        else:
            raise AssertionError("direct-chip accepted public u8 record input without range gates")
    if (source["version"] != 2 or
            [item["kind"] for item in source["inputs"]] != ["u16", "m31"] or
            [item["op"] for item in source["nodes"]] != ["cast_m31", "mul", "add"] or
            source["public_outputs"] != [source["inputs"][0]["name"], "square"]):
        raise AssertionError("u8 record lowered to an unexpected first-order relation")
    abi = source["public_abi"]
    changed = derived_u8_result(source)
    changed_base = {**changed, "version": 1}
    changed_abi = changed_base.pop("public_abi")
    try:
        validate_binding(changed_base, changed_abi)
    except AbiError as exc:
        if "u8 result must alias" not in str(exc):
            raise AssertionError("derived u8 result rejected at wrong boundary") from exc
    else:
        raise AssertionError("derived u8 result escaped input-alias restriction")
    tag_changed = mismatched_result_tag(source)
    tag_base = {**tag_changed, "version": 1}
    tag_abi = tag_base.pop("public_abi")
    try:
        validate_binding(tag_base, tag_abi)
    except AbiError as exc:
        if "u16 result must alias" not in str(exc):
            raise AssertionError("mismatched result tag rejected at wrong boundary") from exc
    else:
        raise AssertionError("u8 input was relabeled as a u16 result")
    widened = widened_boundary_tag(source)
    widened_base = {**widened, "version": 1}
    widened_abi = widened_base.pop("public_abi")
    validate_binding(widened_base, widened_abi)
    source_base = {**source, "version": 1}
    source_abi = source_base.pop("public_abi")
    if binding_digest(source_base, source_abi) == binding_digest(widened_base, widened_abi):
        raise AssertionError("u8 and u16 ABI tags have the same key digest")
    private = private_byte_input(source)
    private_base = {**private, "version": 1}
    private_abi = private_base.pop("public_abi")
    try:
        validate_binding(private_base, private_abi)
    except AbiError as exc:
        if "private bit, u8, and u16" not in str(exc):
            raise AssertionError("private byte rejected at wrong boundary") from exc
    else:
        raise AssertionError("private u8 record leaf was admitted")
    if ([leaf["kind"] for leaf in abi["inputs"][0]["leaves"]] != ["u8", "m31"] or
            [leaf["kind"] for leaf in abi["result"]["leaves"]] != ["u8", "m31"] or
            abi["result"]["leaves"][0]["wire"] != abi["inputs"][0]["leaves"][0]["wire"]):
        raise AssertionError("u8 output does not alias the public range-checked input")
    original = json.loads((EXAMPLE.with_suffix(".valid.json")).read_bytes())
    if original != claim(255):
        raise AssertionError("example boundary assignment differs from the independent arithmetic")
    base = {**source, "version": 1}
    boundary = base.pop("public_abi")
    for byte in (0, 255):
        typed = claim(byte)
        flat = flat_assignment_from_typed(source, canonical(typed))
        if evaluate_relation(base, flat) != flat["public_outputs"]:
            raise AssertionError("independent relation evaluator disagrees with handwritten square")
        statement = statement_from_assignment(source, flat)
        if (decode_public_statement(base, boundary, statement) !=
                [byte, 3, byte, (byte * byte + 3) % P, 0, 0, 0, 0]):
            raise AssertionError("ordered typed public words differ from the independent claim")
    for byte in (256, P - 1):
        try:
            flat_assignment_from_typed(source, canonical(claim(byte)))
        except AbiError:
            pass
        else:
            raise AssertionError(f"typed assignment admitted out-of-range u8 {byte}")
    # The typed statement builder rejects the same boundary even when its
    # separate public input/result aliases agree.
    honest = claim(255)
    flat = flat_assignment_from_typed(source, canonical(honest))
    statement = json.loads(statement_from_assignment(source, flat))
    for byte in (256, P - 1):
        invalid = copy.deepcopy(statement)
        invalid["leaves"][0]["words"] = [byte]
        invalid["leaves"][2]["words"] = [byte]
        try:
            decode_public_statement(base, boundary, canonical(invalid))
        except AbiError:
            pass
        else:
            raise AssertionError(f"Python statement decoder admitted out-of-range u8 {byte}")
    typed_claim = {k: v for k, v in honest.items() if k != "private_inputs"}
    typed_claim["abi_sha256"] = statement["abi_sha256"]
    if encode_typed_public_statement(source, typed_claim) != canonical(statement):
        raise AssertionError("typed claim encoding differs from flat statement encoding")
    return source, flat, statement


def rejected_native(verifier: Path, proof: Path, key: Path, path: Path,
                    value: bytes, expected: str) -> None:
    path.write_bytes(value)
    result = subprocess.run((str(verifier), str(proof), str(path), str(key)),
                            capture_output=True, text=True)
    if result.returncode != 1 or expected not in result.stderr:
        raise AssertionError(f"native verifier failed expected {expected}: {result.stderr}")


def native_checks(source: dict, flat: dict, statement: dict) -> None:
    with tempfile.TemporaryDirectory(prefix="s31-public-u8-v2-") as directory:
        work = Path(directory)
        package = s31.build(EXAMPLE, work / "package", "direct-gate")
        descriptor_corpus = {"schema": "s31-record-descriptor-native-corpus-v2",
                             "cases": [
                                 {"label": "public_u8_alias", "source": canonical(source).decode(),
                                  "expected_valid": True},
                                 {"label": "derived_u8_result", "source": canonical(derived_u8_result(source)).decode(),
                                  "expected_valid": False},
                                 {"label": "mismatched_u8_result_tag", "source": canonical(mismatched_result_tag(source)).decode(),
                                  "expected_valid": False},
                                 {"label": "widened_u16_boundary", "source": canonical(widened_boundary_tag(source)).decode(),
                                  "expected_valid": True},
                                 {"label": "private_byte_input", "source": canonical(private_byte_input(source)).decode(),
                                  "expected_valid": False},
                             ]}
        corpus_path = work / "descriptor-corpus.json"
        corpus_path.write_bytes(canonical(descriptor_corpus))
        corpus = subprocess.run(("zig", "build", "--build-file", str(BUILD_FILE),
                                 "record-descriptor-parser-corpus", "-Doptimize=ReleaseFast", "-j1",
                                 "--", str(corpus_path)), capture_output=True, text=True)
        if corpus.returncode != 0 or json.loads(corpus.stdout) != {"accepted": 2, "rejected": 3}:
            raise AssertionError(f"native descriptor parser disagrees on u8 output alias: {corpus.stderr}")
        verifier = package / "bin/s31-record_public_u8-native-verifier"
        prover = package / "bin/s31-record_public_u8-prover"
        key = package / "verification-key.json"
        if (json.loads(key.read_text())["schema"] != "s31-verification-key-direct-record-v2"):
            raise AssertionError("u8 record built under a different proof profile")
        for byte in (0, 255):
            assignment = work / f"assignment-{byte}.json"
            typed = claim(byte)
            assignment.write_bytes(canonical(flat_assignment_from_typed(source, canonical(typed))))
            trial = s31.trial(package, assignment, work / f"trial-{byte}")
            if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
                raise AssertionError(f"native direct-gate u8 proof failed at {byte}")
        proof = work / "trial-255/proof.bin"
        invalid_path = work / "mutated-statement.json"
        changed = copy.deepcopy(statement)
        changed["leaves"][0]["words"] = [254]
        changed["leaves"][2]["words"] = [254]
        base = {**source, "version": 1}
        abi = base.pop("public_abi")
        decode_public_statement(base, abi, canonical(changed))
        rejected_native(verifier, proof, key, invalid_path, canonical(changed), "error:")
        for byte in (256, P - 1):
            changed = copy.deepcopy(statement)
            changed["leaves"][0]["words"] = [byte]
            changed["leaves"][2]["words"] = [byte]
            rejected_native(verifier, proof, key, invalid_path, canonical(changed),
                            "error: InvalidRecordStatement")
        # A malicious flat prover assignment with an ABI-valid claimed output
        # cannot supply an out-of-range u8 witness to the native compiler.
        bad = copy.deepcopy(flat)
        bad["public_inputs"][source["inputs"][0]["name"]] = [256]
        bad_path = work / "bad-witness.json"
        bad_path.write_bytes(canonical(bad))
        result = subprocess.run((str(prover), "prove", str(bad_path), str(work / "bad-proof.bin")),
                                capture_output=True, text=True)
        if result.returncode != 1 or "error: InvalidAssignedBit" not in result.stderr:
            raise AssertionError("native prover admitted an out-of-range u8 witness")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--native", action="store_true", help="build, prove, and verify two boundary cases")
    args = parser.parse_args()
    source, flat, statement = static_checks()
    if args.native:
        native_checks(source, flat, statement)
    print(json.dumps({"schema": "s31-public-u8-record-v2",
                      "native": args.native,
                      "honest_boundary_values": [0, 255],
                      "rejected_u8_values": [256, P - 1],
                      "result_u8_aliases_input": True,
                      "range_gates_per_input_word": 8}, sort_keys=True))


if __name__ == "__main__":
    main()
