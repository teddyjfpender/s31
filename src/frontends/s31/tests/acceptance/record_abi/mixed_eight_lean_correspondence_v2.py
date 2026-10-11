#!/usr/bin/env python3
"""Finite exact-byte native/Python/Lean corpus for an eight-word record ABI v2.

The Lean file checks small structured facts. The full source descriptor and
statement bytes are pinned as separate JSON artifacts and checked byte for
byte here, then passed unchanged to the native statement parser corpus.
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

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[2]
REPO = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))
from abi.binding_v2 import (  # noqa: E402
    binding_digest, decode_public_statement, encode_typed_public_statement,
)
from abi.record_v2 import AbiError  # noqa: E402
from text_frontend import compile_text  # noqa: E402
from lean_native_bridge_v2 import ContractError, projection  # noqa: E402

P = 2**31 - 1
TEXT = HERE / "mixed_eight_alias_bit.s31"
SOURCE = HERE / "mixed_eight_alias_bit.s31.json"
DESCRIPTOR = HERE / "mixed_eight_alias_bit.abi.json"
STATEMENT = HERE / "mixed_eight_alias_bit.statement.json"
LEAN = REPO / "formal/s31/S31/Gadgets/Records/GeneratedMixedEightV2.lean"


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def wire_relation(source: dict) -> dict:
    return {key: value for key, value in {**source, "version": 1}.items()
            if key != "public_abi"}


def valid_case() -> tuple[dict, bytes, bytes, bytes, dict, list[int]]:
    source, _ = compile_text(TEXT.read_text())
    source_bytes = canonical(source)
    descriptor_bytes = canonical(source["public_abi"])
    relation = wire_relation(source)
    digest = binding_digest(relation, source["public_abi"])
    y = [1, 2, 3, 4]
    for _ in range(16):
        y = [(word * word + 13) % P for word in y]
    claim = {
        "version": 2,
        "abi_sha256": digest,
        "public_inputs": {"request": {"flag": [1], "salt": [5, 6]}},
        "result": {"flag": [1], "y": y, "again": y},
    }
    statement_bytes = encode_typed_public_statement(source, claim)
    statement = json.loads(statement_bytes)
    independent = projection(source, statement)[3]
    python_words = decode_public_statement(relation, source["public_abi"],
                                          statement_bytes)
    expected = [1, 5, 6, 1, *y]
    if independent != expected or python_words != expected or len(expected) != 8:
        raise AssertionError("source/Python/independent eight-word projection diverges")
    if [item["name"] for item in source["inputs"]] != [
            "_s31_abi_input_0", "_s31_abi_input_1", "x"]:
        raise AssertionError("compiled input order changed")
    if source["public_outputs"] != ["_s31_abi_input_0", "y"]:
        raise AssertionError("distinct result wire order changed")
    return source, source_bytes, descriptor_bytes, statement_bytes, claim, expected


def lean_string(value: str) -> str:
    return json.dumps(value, ensure_ascii=True)


def lean_layout(tree: dict) -> str:
    if "kind" in tree:
        return f"(.leaf .{tree['kind']} {tree['length']})"

    def branch(items: list[str]) -> str:
        result = items[-1]
        for index in reversed(range(len(items) - 1)):
            result = f"if i.val = {index} then {items[index]} else {result}"
        return f"(fun i => {result})"

    if "record" in tree:
        fields = tree["fields"]
        names = branch([lean_string(item["name"]) for item in fields])
        children = branch([lean_layout(item["type"]) for item in fields])
        return f"(.record {len(fields)} {names} {children})"
    children = branch([lean_layout(item) for item in tree["tuple"]])
    return f"(.tuple {len(tree['tuple'])} {children})"


def lean_path(path: list[dict]) -> str:
    return "[" + ", ".join(
        f".{tag} {lean_string(item) if isinstance(item, str) else item}"
        for segment in path for tag, item in segment.items()) + "]"


def lean_words(words: list[int]) -> str:
    return "[" + ", ".join(str(word) for word in words) + "]"


def lean_claims(claims: list[dict]) -> str:
    return "[" + ", ".join(
        f"⟨{lean_path(item['path'])}, {lean_words(item['words'])}⟩"
        for item in claims) + "]"


def render_lean(source: dict, source_bytes: bytes, descriptor_bytes: bytes,
                statement_bytes: bytes, words: list[int]) -> str:
    abi = source["public_abi"]
    statement = json.loads(statement_bytes)
    roots = abi["inputs"]
    result = abi["result"]
    all_wires = [item["name"] for item in source["inputs"] + source["nodes"]]
    if len(set(all_wires)) != len(all_wires):
        raise AssertionError("fixture wire names are not unique")
    ids = {wire: index for index, wire in enumerate(all_wires)}
    visible = [root for root in roots if root["visibility"] == "public"]
    leaves = [leaf for root in visible for leaf in root["leaves"]] + result["leaves"]
    if len(leaves) != len(statement["leaves"]):
        raise AssertionError("descriptor/statement leaf count mismatch")
    n = len(all_wires)
    descriptors = ", ".join(
        f"⟨{lean_path(leaf['path'])}, .{leaf['kind']}, {leaf['length']}, {ids[leaf['wire']]}⟩"
        for leaf in leaves)
    input_refs = [ids[item["name"]] for item in source["inputs"]
                  if item["visibility"] == "public"]
    output_refs = [ids[name] for name in source["public_outputs"]]
    source_input_names = [item["name"] for item in source["inputs"]]
    descriptor_input_names = [leaf["wire"] for root in roots for leaf in root["leaves"]]
    result_distinct = list(dict.fromkeys(leaf["wire"] for leaf in result["leaves"]))
    root_sections = []
    at = 0
    for index, root in enumerate(roots + [result]):
        name = f"root{index}Layout"
        root_sections.append(f"def {name} : RawLayout := {lean_layout(root['type'])}")
        root_sections.append(f"theorem {name}_checked : checkNativeRoot {name} = true := by decide")
        if root is not result and root["visibility"] == "private":
            root_sections.append(
                f"theorem {name}_is_private : "
                f"encodeInput .priv {lean_string(root['name'])} {name} "
                f"(fun _ => block [1, 2, 3, 4]) = [] := by decide")
            continue
        count = len(root["leaves"])
        claims = statement["leaves"][at:at + count]
        at += count
        paths = "[" + ", ".join(lean_path(leaf["path"]) for leaf in root["leaves"]) + "]"
        blocks = "[" + ", ".join(lean_words(claim["words"]) for claim in claims) + "]"
        root_sections.extend((
            f"theorem {name}_paths : paths {lean_string(root['name'])} {name} = {paths} := by decide",
            f"theorem {name}_decode : decode {lean_string(root['name'])} {name} "
            f"{lean_claims(claims)} = some {blocks} := by decide",
        ))
    if at != len(statement["leaves"]):
        raise AssertionError("unconsumed statement claims")
    split_bit = copy.deepcopy(statement["leaves"])
    split_bit[2]["words"] = [0]
    split_y = copy.deepcopy(statement["leaves"])
    split_y[4]["words"][2] = (split_y[4]["words"][2] + 1) % P
    bad_bit = copy.deepcopy(statement["leaves"])
    bad_bit[0]["words"] = [2]
    changed_bit = copy.deepcopy(statement["leaves"])
    changed_bit[0]["words"] = [0]
    changed_bit[2]["words"] = [0]
    changed_words = [0, *words[1:3], 0, *words[4:]]
    full_claims = lean_claims(statement["leaves"])
    sections = [
        "import S31.Gadgets.Records.NamedCodecV2",
        "",
        "/-! Source-pinned, finite eight-word mixed record ABI v2 corpus.",
        "The Python generator checks exact compiled source, descriptor and",
        "statement bytes; the native parser checks the same unchanged bytes.",
        "Lean checks only the small structured layout/claim projection. -/",
        f"-- Compiled source bytes SHA-256: {sha256(source_bytes)}",
        f"-- Canonical descriptor bytes SHA-256: {sha256(descriptor_bytes)}",
        f"-- Canonical statement bytes SHA-256: {sha256(statement_bytes)}",
        "namespace S31.Records.GeneratedMixedEightV2",
        "open S31.Records.NamedCodecV2",
        "open S31.Functional.RecordAbiV2",
        "open S31.Functional.RecordLayoutValidationV2",
        "open S31.Functional.RecordWordBoundaryV2",
        "open S31.Functional.RecordStatementV2",
        "",
        *root_sections,
        "",
        f"def sourceInputWires : List String := {json.dumps(source_input_names)}",
        f"def descriptorInputWires : List String := {json.dumps(descriptor_input_names)}",
        "theorem exact_input_wire_order : descriptorInputWires = sourceInputWires := by decide",
        f"def sourceOutputWires : List String := {json.dumps(source['public_outputs'])}",
        f"def distinctResultWires : List String := {json.dumps(result_distinct)}",
        "theorem exact_distinct_result_order : distinctResultWires = sourceOutputWires := by decide",
        "",
        f"def leafDescriptors : List (Descriptor {n}) := [{descriptors}]",
        f"def honestClaims : List Claim := {full_claims}",
        f"def publicInputRefs : List (Fin {n}) := {lean_words(input_refs)}",
        f"def distinctOutputRefs : List (Fin {n}) := {lean_words(output_refs)}",
        "theorem honest_eight_words :",
        "    admitStatement leafDescriptors honestClaims publicInputRefs distinctOutputRefs =",
        f"      some {lean_words(words)} := by decide",
        "theorem checked_bit_alias_split_rejected :",
        f"    admitStatement leafDescriptors {lean_claims(split_bit)}",
        "      publicInputRefs distinctOutputRefs = none := by decide",
        "theorem checked_multilane_result_alias_split_rejected :",
        f"    admitStatement leafDescriptors {lean_claims(split_y)}",
        "      publicInputRefs distinctOutputRefs = none := by decide",
        "theorem out_of_range_bit_rejected :",
        f"    admitStatement leafDescriptors {lean_claims(bad_bit)}",
        "      publicInputRefs distinctOutputRefs = none := by decide",
        "theorem consistent_bit_change_is_new_statement :",
        f"    admitStatement leafDescriptors {lean_claims(changed_bit)}",
        f"      publicInputRefs distinctOutputRefs = some {lean_words(changed_words)} := by decide",
        "end S31.Records.GeneratedMixedEightV2",
        "",
    ]
    return "\n".join(sections)


def mutations(source: dict, statement: dict, words: list[int]) -> list[dict]:
    cases = []

    def add(label: str, candidate: dict, expected: list[int] | None,
            candidate_source: dict = source, assignment: str | None = None) -> None:
        encoded = canonical(candidate)
        relation = wire_relation(candidate_source)
        try:
            actual = decode_public_statement(relation, candidate_source["public_abi"], encoded)
        except AbiError:
            actual = None
        if actual != expected:
            raise AssertionError(f"Python parser disagrees for {label}: {actual} != {expected}")
        try:
            independent = projection(candidate_source, candidate)[3]
        except ContractError:
            independent = None
        if independent != expected:
            raise AssertionError(f"independent projection disagrees for {label}")
        case = {"label": label, "source": canonical(candidate_source).decode("ascii"),
                "statement": encoded.decode("ascii"), "expected_words": expected}
        if assignment is not None:
            case["assignment"] = assignment
        cases.append(case)

    y = words[4:]
    assignment = canonical({
        "public_inputs": {"_s31_abi_input_0": [1], "_s31_abi_input_1": [5, 6]},
        "private_inputs": {"x": [1, 2, 3, 4]},
        "public_outputs": {"_s31_abi_input_0": [1], "y": y},
    }).decode("ascii")
    add("honest_with_relation_evaluation", statement, words, assignment=assignment)
    changed = copy.deepcopy(statement)
    changed["leaves"][0]["words"] = [0]
    changed["leaves"][2]["words"] = [0]
    add("consistent_changed_bit_alias", changed,
        [0, *words[1:3], 0, *words[4:]])
    changed = copy.deepcopy(statement)
    changed["leaves"][2]["words"] = [0]
    add("bit_result_alias_split", changed, None)
    changed = copy.deepcopy(statement)
    changed["leaves"][4]["words"][2] = (changed["leaves"][4]["words"][2] + 1) % P
    add("multilane_result_alias_split", changed, None)
    changed = copy.deepcopy(statement)
    changed["leaves"][0]["words"] = [2]
    add("public_bit_out_of_range", changed, None)
    changed = copy.deepcopy(statement)
    changed["leaves"][3], changed["leaves"][4] = (
        changed["leaves"][4], changed["leaves"][3])
    add("equal_width_result_field_swap", changed, None)
    changed = copy.deepcopy(statement)
    changed["leaves"].insert(2, {"path": [{"root": "x"}], "words": [1, 2, 3, 4]})
    add("private_root_claim_leak", changed, None)
    changed_source = copy.deepcopy(source)
    result = changed_source["public_abi"]["result"]
    result["type"]["fields"][1], result["type"]["fields"][2] = (
        result["type"]["fields"][2], result["type"]["fields"][1])
    result["leaves"][1], result["leaves"][2] = (
        result["leaves"][2], result["leaves"][1])
    if binding_digest(wire_relation(changed_source), changed_source["public_abi"]) == statement["abi_sha256"]:
        raise AssertionError("reordered descriptor did not change ABI digest")
    add("reordered_descriptor_old_statement", statement, None, changed_source)
    return cases


def verify_native(cases: list[dict]) -> dict:
    corpus = {"schema": "s31-record-statement-native-corpus-v2", "cases": cases}
    with tempfile.TemporaryDirectory(prefix="s31-mixed-eight-record-corpus-") as temporary:
        path = Path(temporary) / "corpus.json"
        path.write_bytes(canonical(corpus))
        result = subprocess.run(
            ["zig", "build", "--build-file", str(S31 / "build.zig"),
             "record-statement-parser-corpus", "-j1", "--", str(path)],
            cwd=REPO, capture_output=True, text=True, check=False,
        )
    if result.returncode:
        raise AssertionError("native parser corpus failed:\n" + result.stderr[-6000:])
    observed = json.loads(result.stdout)
    expected = {"accepted": 2, "rejected": len(cases) - 2}
    if observed != expected:
        raise AssertionError(f"native parser counts differ: {observed} != {expected}")
    return {**observed, "corpus_sha256": sha256(canonical(corpus))}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate pinned source, descriptor, statement, and Lean corpus")
    parser.add_argument("--native", action="store_true", help="run the unchanged bytes through native Zig parser")
    args = parser.parse_args()
    source, source_bytes, descriptor_bytes, statement_bytes, _, words = valid_case()
    generated = {
        SOURCE: source_bytes,
        DESCRIPTOR: descriptor_bytes,
        STATEMENT: statement_bytes,
        LEAN: render_lean(source, source_bytes, descriptor_bytes, statement_bytes, words).encode("utf-8"),
    }
    if args.write:
        for path, payload in generated.items():
            path.write_bytes(payload)
    else:
        for path, payload in generated.items():
            if not path.is_file() or path.read_bytes() != payload:
                raise AssertionError(f"generated exact-byte artifact diverges: {path}")
    cases = mutations(source, json.loads(statement_bytes), words)
    report = {
        "schema": "s31-mixed-eight-record-lean-correspondence-v2",
        "source_sha256": sha256(source_bytes),
        "descriptor_sha256": sha256(descriptor_bytes),
        "statement_sha256": sha256(statement_bytes),
        "abi_sha256": json.loads(statement_bytes)["abi_sha256"],
        "public_words": words,
        "cases": len(cases),
        "byte_artifacts_match": True,
    }
    if args.native:
        report["native_parser"] = verify_native(cases)
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
