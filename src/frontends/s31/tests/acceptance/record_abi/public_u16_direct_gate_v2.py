#!/usr/bin/env python3
"""Public u16 record words: arithmetic AIR range proof and native controls."""

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
from abi.binding_v2 import (decode_public_statement,
                            encode_typed_public_statement,
                            flat_assignment_from_typed,
                            statement_from_assignment,
                            validate_binding)  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from package.context import BUILD_FILE, abi as package_abi  # noqa: E402
from text_frontend import compile_file  # noqa: E402

P = (1 << 31) - 1
EXAMPLE = S31 / "examples/arithmetic/record_public_u16.s31"
MIXED_REJECTED = S31 / "tests/acceptance/record_abi/public_u16_mixed_rejected.s31"


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def claim(digit: int, salt: int = 3) -> dict:
    return {"version": 2, "public_inputs": {"req": {"digit": [digit], "salt": [salt]}},
            "private_inputs": {},
            "result": {"digit": [digit], "square": [(digit * digit + salt) % P]}}


def derived_u16_result(source: dict) -> dict:
    """Construct a well-typed relation whose u16 output has a new producer."""
    changed = copy.deepcopy(source)
    input_wire = changed["inputs"][0]["name"]
    changed["nodes"].extend((
        {"name": "zero_selector", "op": "constant", "length": 1, "constant": 0},
        {"name": "selected_digit", "op": "select", "selector": "zero_selector",
         "lhs": input_wire, "rhs": input_wire},
    ))
    changed["public_outputs"][0] = "selected_digit"
    changed["public_abi"]["result"]["leaves"][0]["wire"] = "selected_digit"
    return changed


def static_checks() -> tuple[dict, dict, dict]:
    source, _ = compile_file(EXAMPLE)
    mixed_source, _ = compile_file(MIXED_REJECTED)
    if (mixed_source["version"] != 2 or
            [node["op"] for node in mixed_source["nodes"]] != ["cast_m31", "repeat"] or
            mixed_source["inputs"][0]["kind"] != "u16"):
        raise AssertionError("u16 chip admission fixture changed shape")
    if json.loads(MIXED_REJECTED.with_suffix(".s31.json").read_bytes()) != mixed_source:
        raise AssertionError("native mixed-admission fixture differs from text frontend")
    for candidate in (source, mixed_source):
        try:
            package_abi(candidate, "direct-chip")
        except ValueError:
            pass
        else:
            raise AssertionError("direct-chip accepted public u16 record input without range gates")
    if (source["version"] != 2 or
            [item["kind"] for item in source["inputs"]] != ["u16", "m31"] or
            [item["op"] for item in source["nodes"]] != ["cast_m31", "mul", "add"] or
            source["public_outputs"] != [source["inputs"][0]["name"], "square"]):
        raise AssertionError("u16 record lowered to an unexpected first-order relation")
    abi = source["public_abi"]
    changed = derived_u16_result(source)
    changed_base = {**changed, "version": 1}
    changed_abi = changed_base.pop("public_abi")
    try:
        validate_binding(changed_base, changed_abi)
    except AbiError as exc:
        if "u16 result must alias" not in str(exc):
            raise AssertionError("derived u16 result rejected at wrong boundary") from exc
    else:
        raise AssertionError("derived u16 result escaped input-alias restriction")
    if ([leaf["kind"] for leaf in abi["inputs"][0]["leaves"]] != ["u16", "m31"] or
            [leaf["kind"] for leaf in abi["result"]["leaves"]] != ["u16", "m31"] or
            abi["result"]["leaves"][0]["wire"] != abi["inputs"][0]["leaves"][0]["wire"]):
        raise AssertionError("u16 output does not alias the public range-checked input")
    original = json.loads((EXAMPLE.with_suffix(".valid.json")).read_bytes())
    if original != claim(65535):
        raise AssertionError("example boundary assignment differs from the independent arithmetic")
    base = {**source, "version": 1}
    boundary = base.pop("public_abi")
    for digit in (0, 65535):
        typed = claim(digit)
        flat = flat_assignment_from_typed(source, canonical(typed))
        if evaluate_relation(base, flat) != flat["public_outputs"]:
            raise AssertionError("independent relation evaluator disagrees with handwritten square")
        statement = statement_from_assignment(source, flat)
        if (decode_public_statement(base, boundary, statement) !=
                [digit, 3, digit, (digit * digit + 3) % P, 0, 0, 0, 0]):
            raise AssertionError("ordered typed public words differ from the independent claim")
    for digit in (65536, P - 1):
        try:
            flat_assignment_from_typed(source, canonical(claim(digit)))
        except AbiError:
            pass
        else:
            raise AssertionError(f"typed assignment admitted out-of-range u16 {digit}")
    # The typed statement builder rejects the same boundary even when its
    # separate public input/result aliases agree.
    honest = claim(65535)
    flat = flat_assignment_from_typed(source, canonical(honest))
    statement = json.loads(statement_from_assignment(source, flat))
    for digit in (65536, P - 1):
        invalid = copy.deepcopy(statement)
        invalid["leaves"][0]["words"] = [digit]
        invalid["leaves"][2]["words"] = [digit]
        try:
            decode_public_statement(base, boundary, canonical(invalid))
        except AbiError:
            pass
        else:
            raise AssertionError(f"Python statement decoder admitted out-of-range u16 {digit}")
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
    with tempfile.TemporaryDirectory(prefix="s31-public-u16-v2-") as directory:
        work = Path(directory)
        package = s31.build(EXAMPLE, work / "package", "direct-gate")
        descriptor_corpus = {"schema": "s31-record-descriptor-native-corpus-v2",
                             "cases": [
                                 {"label": "public_u16_alias", "source": canonical(source).decode(),
                                  "expected_valid": True},
                                 {"label": "derived_u16_result", "source": canonical(derived_u16_result(source)).decode(),
                                  "expected_valid": False},
                             ]}
        corpus_path = work / "descriptor-corpus.json"
        corpus_path.write_bytes(canonical(descriptor_corpus))
        corpus = subprocess.run(("zig", "build", "--build-file", str(BUILD_FILE),
                                 "record-descriptor-parser-corpus", "-Doptimize=ReleaseFast", "-j1",
                                 "--", str(corpus_path)), capture_output=True, text=True)
        if corpus.returncode != 0 or json.loads(corpus.stdout) != {"accepted": 1, "rejected": 1}:
            raise AssertionError(f"native descriptor parser disagrees on u16 output alias: {corpus.stderr}")
        verifier = package / "bin/s31-record_public_u16-native-verifier"
        prover = package / "bin/s31-record_public_u16-prover"
        key = package / "verification-key.json"
        if (json.loads(key.read_text())["schema"] != "s31-verification-key-direct-record-v2"):
            raise AssertionError("u16 record built under a different proof profile")
        for digit in (0, 65535):
            assignment = work / f"assignment-{digit}.json"
            typed = claim(digit)
            assignment.write_bytes(canonical(flat_assignment_from_typed(source, canonical(typed))))
            trial = s31.trial(package, assignment, work / f"trial-{digit}")
            if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
                raise AssertionError(f"native direct-gate u16 proof failed at {digit}")
        proof = work / "trial-65535/proof.bin"
        invalid_path = work / "mutated-statement.json"
        changed = copy.deepcopy(statement)
        changed["leaves"][0]["words"] = [65534]
        changed["leaves"][2]["words"] = [65534]
        base = {**source, "version": 1}
        abi = base.pop("public_abi")
        decode_public_statement(base, abi, canonical(changed))
        rejected_native(verifier, proof, key, invalid_path, canonical(changed), "error:")
        for digit in (65536, P - 1):
            changed = copy.deepcopy(statement)
            changed["leaves"][0]["words"] = [digit]
            changed["leaves"][2]["words"] = [digit]
            rejected_native(verifier, proof, key, invalid_path, canonical(changed),
                            "error: InvalidRecordStatement")
        # A malicious flat prover assignment with an ABI-valid claimed output
        # cannot supply an out-of-range u16 witness to the native compiler.
        bad = copy.deepcopy(flat)
        bad["public_inputs"][source["inputs"][0]["name"]] = [65536]
        bad_path = work / "bad-witness.json"
        bad_path.write_bytes(canonical(bad))
        result = subprocess.run((str(prover), "prove", str(bad_path), str(work / "bad-proof.bin")),
                                capture_output=True, text=True)
        if result.returncode != 1 or "error: InvalidAssignedValue" not in result.stderr:
            raise AssertionError("native prover admitted an out-of-range u16 witness")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--native", action="store_true", help="build, prove, and verify two boundary cases")
    args = parser.parse_args()
    source, flat, statement = static_checks()
    if args.native:
        native_checks(source, flat, statement)
    print(json.dumps({"schema": "s31-public-u16-record-v2",
                      "native": args.native,
                      "honest_boundary_values": [0, 65535],
                      "rejected_u16_values": [65536, P - 1],
                      "result_u16_aliases_input": True,
                      "range_gates_per_input_word": 16}, sort_keys=True))


if __name__ == "__main__":
    main()
