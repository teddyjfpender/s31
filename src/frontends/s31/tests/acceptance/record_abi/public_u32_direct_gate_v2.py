#!/usr/bin/env python3
"""Two little-endian u16 limbs for one alias-only public u32 record leaf."""

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
                            flat_assignment_from_typed, statement_from_assignment,
                            validate_binding)  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from package.context import BUILD_FILE, abi as package_abi  # noqa: E402
from text_frontend import compile_file  # noqa: E402

EXAMPLE = S31 / "examples/arithmetic/record_public_u32.s31"
MAX = 65535


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def claim(low: int, high: int) -> dict:
    words = [low, high]
    return {"version": 2, "public_inputs": {"req": {"word": words}},
            "private_inputs": {}, "result": {"word": words}}


def split(source: dict) -> tuple[dict, dict]:
    base = {**source, "version": 1}
    binding = base.pop("public_abi")
    return base, binding


def retype_as_u16_words(source: dict) -> dict:
    """Same relation wires, different nominal type and therefore a different key."""
    changed = copy.deepcopy(source)
    for root in (*changed["public_abi"]["inputs"], changed["public_abi"]["result"]):
        root["type"]["fields"][0]["type"]["kind"] = "u16"
        root["leaves"][0]["kind"] = "u16"
    return changed


def invalid_descriptors(source: dict) -> list[tuple[str, dict]]:
    cases = []

    def add(label: str, change) -> None:
        candidate = copy.deepcopy(source)
        change(candidate)
        cases.append((label, candidate))

    def change_length(candidate: dict, length: int) -> None:
        candidate["public_abi"]["inputs"][0]["type"]["fields"][0]["type"]["length"] = length
        candidate["public_abi"]["inputs"][0]["leaves"][0]["length"] = length

    add("one_limb_u32", lambda c: change_length(c, 1))
    add("three_limb_u32", lambda c: change_length(c, 3))
    add("leaf_kind_disagrees", lambda c: c["public_abi"]["result"]["leaves"][0].__setitem__("kind", "u16"))
    add("private_u32", lambda c: (c["inputs"][0].__setitem__("visibility", "private"),
                                   c["public_abi"]["inputs"][0].__setitem__("visibility", "private")))

    def derived(candidate: dict) -> None:
        wire = candidate["inputs"][0]["name"]
        candidate["nodes"].extend((
            {"name": "zero_selector", "op": "constant", "length": 1, "constant": 0},
            {"name": "copied_word", "op": "select", "selector": "zero_selector",
             "lhs": wire, "rhs": wire},
        ))
        candidate["public_outputs"][0] = "copied_word"
        candidate["public_abi"]["result"]["leaves"][0]["wire"] = "copied_word"

    add("derived_u32_result", derived)
    return cases


def static_checks() -> tuple[dict, dict, bytes]:
    source, _ = compile_file(EXAMPLE)
    base, binding = split(source)
    wire = source["inputs"][0]["name"]
    if (source["version"] != 2 or source["nodes"] != [] or source["assertions"] != [] or
            source["inputs"] != [{"name": wire, "kind": "u16", "length": 2,
                                  "visibility": "public"}] or
            source["public_outputs"] != [wire] or
            binding["inputs"][0]["leaves"] != [
                {"path": [{"root": "req"}, {"field": "word"}], "kind": "u32",
                 "length": 2, "wire": wire}] or
            binding["result"]["leaves"] != [
                {"path": [{"root": "result"}, {"field": "word"}], "kind": "u32",
                 "length": 2, "wire": wire}]):
        raise AssertionError("u32 source did not lower to one two-limb alias")
    if not binding_digest(base, binding):
        raise AssertionError("u32 descriptor has no digest")
    retyped_base, retyped_binding = split(retype_as_u16_words(source))
    validate_binding(retyped_base, retyped_binding)
    if binding_digest(retyped_base, retyped_binding) == binding_digest(base, binding):
        raise AssertionError("u32/u16 nominal ABI tags share a digest")
    if package_abi(source, "direct-gate")["boundary"] != binding:
        raise AssertionError("direct-gate package changed the u32 descriptor")
    try:
        package_abi(source, "direct-chip")
    except ValueError:
        pass
    else:
        raise AssertionError("u32 record must not enter the one-call chip profile")
    for label, candidate in invalid_descriptors(source):
        candidate_base, candidate_abi = split(candidate)
        try:
            validate_binding(candidate_base, candidate_abi)
        except AbiError:
            pass
        else:
            raise AssertionError(f"malformed {label} descriptor was admitted")

    original = json.loads(EXAMPLE.with_suffix(".valid.json").read_bytes())
    if original != claim(MAX, MAX):
        raise AssertionError("u32 example does not encode 0xffffffff little-endian")
    statement: bytes | None = None
    flat: dict | None = None
    for low, high in ((0, 0), (MAX, MAX), (MAX, 0), (0, MAX)):
        flat = flat_assignment_from_typed(source, canonical(claim(low, high)))
        if evaluate_relation(base, flat) != flat["public_outputs"]:
            raise AssertionError("u32 source relation disagrees with alias semantics")
        statement = statement_from_assignment(source, flat)
        if decode_public_statement(base, binding, statement) != [low, high, low, high, 0, 0, 0, 0]:
            raise AssertionError("u32 statement projected wrong little-endian limbs")
    assert flat is not None and statement is not None
    for bad in ([-1, 0], [0, -1], [65536, 0], [0, 65536], [0], [0, 0, 0], [False, 0]):
        candidate = claim(0, 0)
        candidate["public_inputs"]["req"]["word"] = bad
        candidate["result"]["word"] = bad
        try:
            flat_assignment_from_typed(source, canonical(candidate))
        except AbiError:
            pass
        else:
            raise AssertionError(f"noncanonical u32 limbs accepted: {bad!r}")
    parsed = json.loads(statement)
    retyped_claim = copy.deepcopy(parsed)
    retyped_claim["abi_sha256"] = binding_digest(retyped_base, retyped_binding)
    try:
        decode_public_statement(base, binding, canonical(retyped_claim))
    except AbiError:
        pass
    else:
        raise AssertionError("coherently relabeled u16 claim passed u32 ABI seal")
    for bad in ([65536, 0], [0, 65536], [0], [0, 0, 0]):
        candidate = copy.deepcopy(parsed)
        candidate["leaves"][0]["words"] = bad
        candidate["leaves"][1]["words"] = bad
        try:
            decode_public_statement(base, binding, canonical(candidate))
        except AbiError:
            pass
        else:
            raise AssertionError(f"invalid statement u32 limbs accepted: {bad!r}")
    swapped = copy.deepcopy(parsed)
    swapped["leaves"][1]["words"] = [MAX, 0]
    try:
        decode_public_statement(base, binding, canonical(swapped))
    except AbiError:
        pass
    else:
        raise AssertionError("u32 input/result alias mismatch was accepted")
    return source, flat, statement


def native_checks(source: dict, flat: dict, statement: bytes) -> None:
    base, binding = split(source)
    with tempfile.TemporaryDirectory(prefix="s31-public-u32-v2-") as directory:
        work = Path(directory)
        descriptor = {"schema": "s31-record-descriptor-native-corpus-v2", "cases": [
            {"label": "public_u32_alias", "source": canonical(source).decode(),
             "expected_valid": True, "expected_digest": binding_digest(base, binding),
             "statement": statement.decode(), "expected_words": [0, MAX, 0, MAX, 0, 0, 0, 0]},
            *({"label": label, "source": canonical(candidate).decode(),
               "expected_valid": False} for label, candidate in invalid_descriptors(source)),
        ]}
        path = work / "descriptors.json"
        path.write_bytes(canonical(descriptor))
        run = subprocess.run(("zig", "build", "--build-file", str(BUILD_FILE),
                              "record-descriptor-parser-corpus", "-Doptimize=ReleaseFast", "-j1",
                              "--", str(path)), capture_output=True, text=True)
        if run.returncode != 0 or json.loads(run.stdout) != {"accepted": 1, "rejected": 5}:
            raise AssertionError(f"native descriptor corpus failed: {run.stderr}")

        malformed_statements = []
        for label, words in (("large_low", [65536, 0]), ("large_high", [0, 65536]),
                             ("one_limb", [0]), ("three_limbs", [0, 0, 0])):
            changed = json.loads(statement)
            for leaf in changed["leaves"]:
                leaf["words"] = words
            malformed_statements.append((label, canonical(changed)))
        changed = json.loads(statement)
        changed["leaves"][1]["words"] = [MAX, 0]
        malformed_statements.append(("alias_mismatch", canonical(changed)))
        changed = json.loads(statement)
        retyped_base, retyped_binding = split(retype_as_u16_words(source))
        changed["abi_sha256"] = binding_digest(retyped_base, retyped_binding)
        malformed_statements.append(("wrong_nominal_type", canonical(changed)))
        parser_corpus = {"schema": "s31-record-statement-native-corpus-v2", "cases": [
            {"label": "valid_u32", "source": canonical(source).decode(),
             "statement": statement.decode(), "expected_words": [0, MAX, 0, MAX, 0, 0, 0, 0],
             "assignment": canonical(flat).decode()},
            *({"label": label, "source": canonical(source).decode(),
               "statement": encoded.decode(), "expected_words": None}
              for label, encoded in malformed_statements),
        ]}
        parser_path = work / "statements.json"
        parser_path.write_bytes(canonical(parser_corpus))
        run = subprocess.run(("zig", "build", "--build-file", str(BUILD_FILE),
                              "record-statement-parser-corpus", "-Doptimize=ReleaseFast", "-j1",
                              "--", str(parser_path)), capture_output=True, text=True)
        if run.returncode != 0 or json.loads(run.stdout) != {"accepted": 1, "rejected": 6}:
            raise AssertionError(f"native statement corpus failed: {run.stderr}")

        package = s31.build(EXAMPLE, work / "package", "direct-gate")
        if json.loads((package / "verification-key.json").read_text())["schema"] != "s31-verification-key-direct-record-v2":
            raise AssertionError("u32 record built under unexpected key profile")
        # The u16[2] descriptor proves the same two limb ranges. The distinct
        # type tag changes key/statement identity without changing AIR rows.
        retyped_path = work / "retyped-u16.s31.json"
        retyped_path.write_bytes(canonical(retype_as_u16_words(source)))
        retyped_package = s31.build(retyped_path, work / "retyped-u16-package", "direct-gate")
        cost = json.loads((package / "cost-report.json").read_text())
        retyped_cost = json.loads((retyped_package / "cost-report.json").read_text())
        for field in ("raw", "padded", "preprocessed_cells", "preprocessed_columns"):
            if cost[field] != retyped_cost[field]:
                raise AssertionError(f"u32 typed ABI changed {field} relative to two u16 limbs")
        if (json.loads((package / "verification-key.json").read_text())["public_abi_sha256"] ==
                json.loads((retyped_package / "verification-key.json").read_text())["public_abi_sha256"]):
            raise AssertionError("u32 and u16[2] packages reused the same ABI identity")
        for low, high in ((0, 0), (MAX, MAX), (MAX, 0)):
            assignment = work / f"assignment-{low}-{high}.json"
            assignment.write_bytes(canonical(flat_assignment_from_typed(source, canonical(claim(low, high)))))
            trial = s31.trial(package, assignment, work / f"trial-{low}-{high}")
            if not trial["native_verifier_accepted"] or not trial["changed_public_statement_rejected"]:
                raise AssertionError(f"native u32 proof failed at {low}, {high}")

        verifier = package / "bin/s31-record_public_u32-native-verifier"
        key = package / "verification-key.json"
        proof = work / f"trial-{MAX}-0/proof.bin"
        honest = json.loads(statement_from_assignment(
            source, flat_assignment_from_typed(source, canonical(claim(MAX, 0)))))
        for label, mutate, error in (
            ("changed_claim", lambda s: [s["leaves"][i].__setitem__("words", [MAX, MAX]) for i in (0, 1)], "error:"),
            ("large_low_limb", lambda s: [s["leaves"][i].__setitem__("words", [65536, 0]) for i in (0, 1)], "InvalidRecordStatement"),
            ("large_high_limb", lambda s: [s["leaves"][i].__setitem__("words", [MAX, 65536]) for i in (0, 1)], "InvalidRecordStatement"),
            ("wrong_nominal_type", lambda s: s.__setitem__("abi_sha256", json.loads(
                (retyped_package / "verification-key.json").read_text())["public_abi_sha256"]), "InvalidRecordStatement"),
        ):
            changed = copy.deepcopy(honest)
            mutate(changed)
            claim_path = work / f"{label}.json"
            claim_path.write_bytes(canonical(changed))
            result = subprocess.run((str(verifier), str(proof), str(claim_path), str(key)),
                                    capture_output=True, text=True)
            if result.returncode != 1 or error not in result.stderr:
                raise AssertionError(f"native {label} not rejected: {result.stderr}")

        # Native relation witness admission independently checks both u16
        # limbs even when the flat prover bypasses the typed JSON adapter.
        prover = package / "bin/s31-record_public_u32-prover"
        for label, words in (("bad_low", [65536, 0]), ("bad_high", [MAX, 65536])):
            bad = flat_assignment_from_typed(source, canonical(claim(MAX, 0)))
            bad["public_inputs"][source["inputs"][0]["name"]] = words
            assignment_path = work / f"{label}.json"
            assignment_path.write_bytes(canonical(bad))
            result = subprocess.run((str(prover), "prove", str(assignment_path),
                                     str(work / f"{label}.bin")), capture_output=True, text=True)
            if result.returncode != 1 or "InvalidAssignedValue" not in result.stderr:
                raise AssertionError(f"native prover admitted {label}: {result.stderr}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--native", action="store_true")
    args = parser.parse_args()
    source, flat, statement = static_checks()
    if args.native:
        native_checks(source, flat, statement)
    print(json.dumps({"schema": "s31-public-u32-record-v2", "native": args.native,
                      "limb_order": "little-endian", "honest": [0, 0xffffffff],
                      "input_range_bits": 32, "result_aliases_public_input": True}, sort_keys=True))


if __name__ == "__main__":
    main()
