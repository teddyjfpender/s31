#!/usr/bin/env python3
"""Independent, coherent u32 descriptor and canonical-statement attacks.

The malformed relation/descriptor pairs remain otherwise well shaped. This
checks that the public u32 ABI rule itself rejects them, in Python and Zig.
"""

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

from abi.binding_v2 import (binding_digest, decode_public_statement,
                            statement_from_assignment, validate_binding)  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from package.context import BUILD_FILE  # noqa: E402
from text_frontend import compile_file  # noqa: E402

SOURCE = S31 / "examples/arithmetic/record_public_u32.s31"


def encoded(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def split(program: dict) -> tuple[dict, dict]:
    relation = {**program, "version": 1}
    binding = relation.pop("public_abi")
    return relation, binding


def descriptor_attacks(program: dict) -> list[tuple[str, dict]]:
    cases: list[tuple[str, dict]] = []

    for length in (1, 3):
        changed = copy.deepcopy(program)
        changed["inputs"][0]["length"] = length
        for root in (*changed["public_abi"]["inputs"], changed["public_abi"]["result"]):
            root["type"]["fields"][0]["type"]["length"] = length
            root["leaves"][0]["length"] = length
        cases.append((f"coherent_u32_{length}_limbs", changed))

    changed = copy.deepcopy(program)
    changed["inputs"][0]["visibility"] = "private"
    changed["inputs"].append({"name": "visible", "kind": "m31", "length": 1,
                              "visibility": "public"})
    changed["public_outputs"] = ["visible"]
    changed["public_abi"]["inputs"][0]["visibility"] = "private"
    changed["public_abi"]["inputs"].append({
        "name": "visible", "type": {"kind": "m31", "length": 1},
        "visibility": "public", "leaves": [{
            "path": [{"root": "visible"}], "kind": "m31", "length": 1,
            "wire": "visible"}]})
    changed["public_abi"]["result"] = {
        "name": "result", "type": {"kind": "m31", "length": 1},
        "leaves": [{"path": [{"root": "result"}], "kind": "m31",
                    "length": 1, "wire": "visible"}]}
    cases.append(("private_u32_with_separate_public_claim", changed))

    for side in ("inputs", "result"):
        changed = copy.deepcopy(program)
        root = changed["public_abi"][side][0] if side == "inputs" else changed["public_abi"][side]
        root["type"]["fields"][0]["type"]["kind"] = "u16"
        root["leaves"][0]["kind"] = "u16"
        cases.append((f"alias_retyped_only_{side}", changed))

    return cases


def statement_attacks(program: dict) -> tuple[bytes, list[tuple[str, bytes]]]:
    relation, binding = split(program)
    wire = program["inputs"][0]["name"]
    honest = statement_from_assignment(program, {
        "public_inputs": {wire: [65535, 32768]}, "private_inputs": {},
        "public_outputs": {wire: [65535, 32768]}})
    if decode_public_statement(relation, binding, honest) != [65535, 32768, 65535, 32768, 0, 0, 0, 0]:
        raise AssertionError("little-endian u32 boundary projected incorrectly")
    cases: list[tuple[str, bytes]] = []
    for label, word in (("high_limb_65536", 65536), ("high_limb_field_modulus", 2147483647),
                        ("high_limb_negative", -1), ("high_limb_boolean", True),
                        ("high_limb_float", 32768.0)):
        changed = json.loads(honest)
        changed["leaves"][0]["words"][1] = word
        changed["leaves"][1]["words"][1] = word
        cases.append((label, encoded(changed)))
    changed = json.loads(honest)
    changed["leaves"][1]["words"][1] = 32767
    cases.append(("high_limb_alias_mismatch", encoded(changed)))
    duplicate = honest.replace(b'"words":[65535,32768]',
                               b'"words":[65535,32768],"words":[65535,32768]', 1)
    cases.append(("duplicate_nested_words_key", duplicate))
    cases.append(("noncanonical_leading_space", b" " + honest))
    cases.append(("noncanonical_no_final_newline", honest.rstrip(b"\n")))
    return honest, cases


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--native", action="store_true")
    args = parser.parse_args()
    program, _ = compile_file(SOURCE)
    relation, binding = split(program)
    validate_binding(relation, binding)
    attacks = descriptor_attacks(program)
    for label, changed in attacks:
        changed_relation, changed_binding = split(changed)
        try:
            validate_binding(changed_relation, changed_binding)
        except AbiError:
            pass
        else:
            raise AssertionError(f"Python admitted malformed descriptor {label}")
    honest, bad_statements = statement_attacks(program)
    for label, statement in bad_statements:
        try:
            decode_public_statement(relation, binding, statement)
        except AbiError:
            pass
        else:
            raise AssertionError(f"Python admitted malformed statement {label}")

    if args.native:
        with tempfile.TemporaryDirectory(prefix="s31-u32-adversarial-") as temporary:
            root = Path(temporary)
            digest = binding_digest(relation, binding)
            descriptors = {"schema": "s31-record-descriptor-native-corpus-v2", "cases": [
                {"label": "honest", "source": encoded(program).decode(),
                 "expected_valid": True, "expected_digest": digest,
                 "statement": honest.decode(),
                 "expected_words": [65535, 32768, 65535, 32768, 0, 0, 0, 0]},
                *({"label": label, "source": encoded(changed).decode(),
                   "expected_valid": False} for label, changed in attacks),
            ]}
            descriptor_path = root / "descriptors.json"
            descriptor_path.write_bytes(encoded(descriptors))
            run = subprocess.run(("zig", "build", "--build-file", str(BUILD_FILE),
                                  "record-descriptor-parser-corpus", "-Doptimize=ReleaseFast",
                                  "-j1", "--", str(descriptor_path)),
                                 capture_output=True, text=True)
            if run.returncode or json.loads(run.stdout) != {"accepted": 1, "rejected": len(attacks)}:
                raise AssertionError(f"native descriptor rejection failed: {run.stderr}")
            statements = {"schema": "s31-record-statement-native-corpus-v2", "cases": [
                {"label": "honest", "source": encoded(program).decode(),
                 "statement": honest.decode(),
                 "expected_words": [65535, 32768, 65535, 32768, 0, 0, 0, 0]},
                *({"label": label, "source": encoded(program).decode(),
                   "statement": statement.decode(), "expected_words": None}
                  for label, statement in bad_statements),
            ]}
            statement_path = root / "statements.json"
            statement_path.write_bytes(encoded(statements))
            run = subprocess.run(("zig", "build", "--build-file", str(BUILD_FILE),
                                  "record-statement-parser-corpus", "-Doptimize=ReleaseFast",
                                  "-j1", "--", str(statement_path)),
                                 capture_output=True, text=True)
            if run.returncode or json.loads(run.stdout) != {"accepted": 1, "rejected": len(bad_statements)}:
                raise AssertionError(f"native statement rejection failed: {run.stderr}")

    print(json.dumps({"schema": "s31-u32-record-adversarial-v2", "native": args.native,
                      "coherent_descriptor_rejections": len(attacks),
                      "canonical_statement_rejections": len(bad_statements)}, sort_keys=True))


if __name__ == "__main__":
    main()
