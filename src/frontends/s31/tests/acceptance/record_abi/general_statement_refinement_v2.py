#!/usr/bin/env python3
"""Compile varied record layouts and check their public-claim semantics in Lean.

The corpus reaches the source compiler and Python ABI parser. The independent
projection follows the native descriptor walk and first-wire lookup without
calling the Python statement decoder. Generated Lean declarations are then
kernel checked. This is a bounded differential bridge, not a proof of Zig JSON
parsing or of proof authentication.
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

from lean_native_bridge_v2 import ContractError, lean_list, lean_path, path_parts, projection
from nested_alias_v2 import S31, canonical

sys.path.insert(0, str(S31 / "python"))
from abi.binding_v2 import decode_public_statement, encode_public_statement  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from text_frontend import compile_text  # noqa: E402

LEAN = S31.parents[2] / "formal/s31/S31/Gadgets/Functional/GeneratedRecordStatementCorpusV2.lean"
P = 2**31 - 1
NATIVE_CORPUS_SHA256 = "1c653b515475bc8e90a4ccff13faf2fe6373d74d31f2a0b9ab6679c0eab270c8"


def sources() -> list[tuple[str, str]]:
    result = []
    for width in range(1, 5):
        result.append((f"pair_{width}", f"""struct Pair {{ a: [m31; {width}], b: [m31; {width}] }}
circuit pair(public x: [m31; {width}]) -> public Pair {{
    Pair {{ a: x, b: x }}
}}
"""))
    for left, right in ((1, 1), (2, 1), (1, 2), (2, 2)):
        result.append((f"tuple_{left}_{right}", f"""struct Request {{ pair: ([m31; {left}], [m31; {right}]) }}
struct Result {{ copy: [m31; {left}], tail: [m31; {right}] }}
circuit nested(public req: Request) -> public Result {{
    Result {{ copy: req.pair.0, tail: req.pair.1 }}
}}
"""))
    for width in range(1, 4):
        result.append((f"bit_{width}", f"""struct Request {{ flag: bit, x: [m31; {width}] }}
struct Result {{ y: [m31; {width}] }}
circuit with_bit(public req: Request) -> public Result {{
    Result {{ y: req.x }}
}}
"""))
    for width in range(1, 3):
        result.append((f"private_{width}", f"""struct Request {{ left: [m31; {width}], right: [m31; {width}] }}
struct Secret {{ mask: [m31; {width}] }}
struct Result {{ out: [m31; {width}], alias: [m31; {width}] }}
circuit private_alias(public req: Request, private hidden: Secret) -> public Result {{
    let sum = req.left + hidden.mask;
    Result {{ out: sum, alias: sum }}
}}
"""))
    return result


def relation_and_binding(source: dict) -> tuple[dict, dict]:
    relation = {**source, "version": 1}
    binding = relation.pop("public_abi")
    return relation, binding


def descriptors(binding: dict) -> list[dict]:
    return [leaf for root in binding["inputs"] if root["visibility"] == "public"
            for leaf in root["leaves"]] + binding["result"]["leaves"]


def encoded_claims(relation: dict, binding: dict, seed: int) -> tuple[dict, list[int]]:
    leaves = descriptors(binding)
    values: dict[str, list[int]] = {}
    for leaf in leaves:
        wire = leaf["wire"]
        if wire not in values:
            if leaf["kind"] == "bit":
                values[wire] = [seed % 2]
            else:
                values[wire] = [seed * 29 + len(values) * 13 + index + 1
                                for index in range(leaf["length"])]
    encoded = encode_public_statement(relation, binding,
                                      [values[leaf["wire"]] for leaf in leaves])
    statement = json.loads(encoded)
    native_words = decode_public_statement(relation, binding, encoded)
    independent_words = projection({**relation, "public_abi": binding}, statement)[3]
    if native_words != independent_words:
        raise AssertionError("independent wire projection differs from Python ABI")
    return statement, native_words


def reject(relation: dict, binding: dict, statement: dict, label: str) -> None:
    encoded = canonical(statement)
    try:
        decode_public_statement(relation, binding, encoded)
    except AbiError:
        pass
    else:
        raise AssertionError(f"Python accepted {label}")
    try:
        projection({**relation, "public_abi": binding}, statement)
    except (ContractError, KeyError, IndexError, TypeError):
        pass
    else:
        raise AssertionError(f"independent projection accepted {label}")


def mutations(relation: dict, binding: dict, statement: dict) -> dict[str, dict]:
    leaves = descriptors(binding)
    result: dict[str, dict] = {}
    changed = copy.deepcopy(statement)
    changed["leaves"][0]["path"][0] = {"root": "wrong_root"}
    result["path"] = changed
    changed = copy.deepcopy(statement)
    changed["leaves"][0]["words"].append(1)
    result["width"] = changed
    changed = copy.deepcopy(statement)
    changed["leaves"][0]["words"][0] = 2 if leaves[0]["kind"] == "bit" else P
    result["range"] = changed
    changed = copy.deepcopy(statement)
    changed["leaves"].pop()
    result["missing_leaf"] = changed
    first_for_wire: dict[str, int] = {}
    repeated = None
    for index, leaf in enumerate(leaves):
        if leaf["wire"] in first_for_wire:
            repeated = index
            break
        first_for_wire[leaf["wire"]] = index
    if repeated is None:
        raise AssertionError("generated case lacks an aliased public claim")
    changed = copy.deepcopy(statement)
    old = changed["leaves"][repeated]["words"][0]
    limit = 2 if leaves[repeated]["kind"] == "bit" else P
    changed["leaves"][repeated]["words"][0] = (old + 1) % limit
    result["split_alias"] = changed
    for label, variant in result.items():
        reject(relation, binding, variant, label)
    return result


def consistent_change(relation: dict, binding: dict, statement: dict,
                      baseline: list[int]) -> tuple[dict, list[int]]:
    leaves = descriptors(binding)
    wire = leaves[0]["wire"]
    changed = copy.deepcopy(statement)
    limit = 2 if leaves[0]["kind"] == "bit" else P
    for index, leaf in enumerate(leaves):
        if leaf["wire"] == wire:
            changed["leaves"][index]["words"][0] = (
                changed["leaves"][index]["words"][0] + 1) % limit
    encoded = canonical(changed)
    decoded = decode_public_statement(relation, binding, encoded)
    independent = projection({**relation, "public_abi": binding}, changed)[3]
    if decoded != independent or decoded == baseline:
        raise AssertionError("consistent alias change did not update proof words")
    return changed, decoded


def lean_descriptor(leaf: dict, wire_index: dict[str, int]) -> str:
    return (f"⟨{lean_path(path_parts(leaf['path']))}, .{leaf['kind']}, "
            f"{leaf['length']}, {wire_index[leaf['wire']]}⟩")


def lean_claim(claim: dict) -> str:
    return f"⟨{lean_path(path_parts(claim['path']))}, {lean_list(claim['words'])}⟩"


def lean_claims(claims: list[dict]) -> str:
    return "[" + ", ".join(map(lean_claim, claims)) + "]"


def render() -> tuple[str, dict]:
    cases = sources()
    source_hash = hashlib.sha256("".join(text for _, text in cases).encode()).hexdigest()
    lines = [
        "import S31.Gadgets.Functional.RecordStatementV2",
        "",
        "/-! Generated, source-pinned ABI statement corpus. Regenerate with",
        "`general_statement_refinement_v2.py --write`; default mode checks exact bytes.",
        "The general theorem lives in RecordStatementV2.lean. Each example here",
        "kernel-checks one independently compiled source/statement pair. -/",
        f"-- Source corpus SHA-256: {source_hash}",
        "namespace S31.Functional.GeneratedRecordStatementCorpusV2",
        "open RecordAbiV2 RecordStatementV2",
        "",
    ]
    mutation_count = 0
    for case_index, (label, source_text) in enumerate(cases):
        source, _ = compile_text(source_text)
        relation, binding = relation_and_binding(source)
        statement, proof_words = encoded_claims(relation, binding, case_index + 1)
        variants = mutations(relation, binding, statement)
        changed, changed_words = consistent_change(relation, binding, statement,
                                                   proof_words)
        public_leaves = descriptors(binding)
        wires = list(dict.fromkeys([leaf["wire"] for leaf in public_leaves]))
        wire_index = {wire: index for index, wire in enumerate(wires)}
        n = len(wires)
        input_refs = [wire_index[item["name"]] for item in relation["inputs"]
                      if item["visibility"] == "public"]
        output_refs = [wire_index[wire] for wire in relation["public_outputs"]]
        name = f"case{case_index}_{label}"
        lines += [
            f"-- {label}: {len(public_leaves)} named public leaves, {n} distinct wires.",
            f"def {name}Descriptors : List (Descriptor {n}) :=",
            "  [" + ", ".join(lean_descriptor(leaf, wire_index)
                               for leaf in public_leaves) + "]",
            f"def {name}Claims : List Claim :=",
            "  " + lean_claims(statement["leaves"]),
            f"def {name}Inputs : List (Fin {n}) := {lean_list(input_refs)}",
            f"def {name}Outputs : List (Fin {n}) := {lean_list(output_refs)}",
            f"theorem {name}_accepted :",
            f"    admitStatement {name}Descriptors {name}Claims",
            f"      {name}Inputs {name}Outputs = some {lean_list(proof_words)} := by decide",
            f"theorem {name}_consistent_change :",
            f"    admitStatement {name}Descriptors {lean_claims(changed['leaves'])}",
            f"      {name}Inputs {name}Outputs = some {lean_list(changed_words)} := by decide",
        ]
        for variant_label, variant in variants.items():
            lines += [
                f"theorem {name}_{variant_label}_rejected :",
                f"    admitStatement {name}Descriptors {lean_claims(variant['leaves'])}",
                f"      {name}Inputs {name}Outputs = none := by decide",
            ]
        lines.append("")
        mutation_count += len(variants)
    lines += ["end S31.Functional.GeneratedRecordStatementCorpusV2", ""]
    return "\n".join(lines), {
        "schema": "s31-generated-record-statement-refinement-v2",
        "source_sha256": source_hash,
        "compiled_layouts": len(cases),
        "rejected_malformed_claims": mutation_count,
        "accepted_consistent_changed_claims": len(cases),
        "lean_path": str(LEAN.relative_to(S31.parents[2])),
    }


def check_native_parser() -> dict:
    """Compare the 13 source-derived cases with Zig's real statement parser.

    This invokes relation.parseProgram and record_abi.claimedWords directly. It
    does not create a proof or treat a changed but well-formed claim as valid
    for an existing proof.
    """
    cases: list[dict] = []
    for index, (label, source_text) in enumerate(sources()):
        source, _ = compile_text(source_text)
        relation, binding = relation_and_binding(source)
        statement, expected = encoded_claims(relation, binding, index + 1)
        variants = mutations(relation, binding, statement)
        changed, changed_words = consistent_change(relation, binding, statement,
                                                   expected)
        source_json = canonical(source).decode("ascii")
        for suffix, claim, words in (("accepted", statement, expected),
                                     ("consistent_change", changed, changed_words)):
            cases.append({"label": f"{label}/{suffix}", "source": source_json,
                          "statement": canonical(claim).decode("ascii"),
                          "expected_words": words})
        for suffix, claim in variants.items():
            cases.append({"label": f"{label}/{suffix}", "source": source_json,
                          "statement": canonical(claim).decode("ascii"),
                          "expected_words": None})
    if len(cases) != 91:
        raise AssertionError("native parser corpus must contain 13 * 7 cases")
    with tempfile.TemporaryDirectory(prefix="s31-record-parser-corpus-") as temporary:
        path = Path(temporary) / "corpus.json"
        corpus_bytes = canonical({"schema": "s31-record-statement-native-corpus-v2",
                                  "cases": cases})
        corpus_sha256 = hashlib.sha256(corpus_bytes).hexdigest()
        if corpus_sha256 != NATIVE_CORPUS_SHA256:
            raise AssertionError("native statement corpus bytes differ from pinned SHA-256")
        path.write_bytes(corpus_bytes)
        command = ["zig", "build", "--build-file", str(S31 / "build.zig"),
                   "record-statement-parser-corpus", "-j1", "--", str(path)]
        completed = subprocess.run(command, cwd=S31.parents[2], capture_output=True,
                                   text=True, check=False)
        if completed.returncode:
            raise AssertionError("native statement parser corpus failed:\n"
                                 + completed.stderr[-6000:])
    result = json.loads(completed.stdout)
    if result != {"accepted": 26, "rejected": 65}:
        raise AssertionError(f"native parser corpus counts differ: {result}")
    return {**result, "corpus_sha256": corpus_sha256}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate checked-in Lean corpus")
    parser.add_argument("--native", action="store_true",
                        help="run all generated claims through Zig's native statement parser")
    args = parser.parse_args()
    rendered, report = render()
    if args.write:
        LEAN.write_text(rendered)
    elif not LEAN.is_file() or LEAN.read_text() != rendered:
        raise AssertionError("compiled record corpus diverges from checked-in Lean; use --write")
    if args.native:
        report["native_parser"] = check_native_parser()
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
