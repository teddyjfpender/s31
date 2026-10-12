#!/usr/bin/env python3
"""Source-derived ABI v2 digest and public-word correspondence corpus.

Every accepted case reaches the production Zig relation parser, canonical
descriptor serializer, SHA-256 digest, and statement projection. The Python
side computes a second digest directly from the specified canonical JSON bytes
and independently walks the descriptor to check the final eight words.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

from general_statement_refinement_v2 import encoded_claims, relation_and_binding, sources
from lean_native_bridge_v2 import projection
from nested_alias_v2 import S31, SOURCE

import sys
sys.path.insert(0, str(S31 / "python"))
from abi.binding_v2 import DOMAIN, binding_digest, decode_public_statement  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from text_frontend import compile_text  # noqa: E402

SCHEMA = "s31-record-descriptor-native-corpus-v2"
CORPUS_SHA256 = "cb863031d541c594a24feb41aab146344759b3239049e475dce4bcf0be256af9"


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")


def reverse_keys(value: object) -> object:
    """Reverse insertion order at every JSON object without changing values."""
    if type(value) is dict:
        return {key: reverse_keys(value[key]) for key in reversed(value)}
    if type(value) is list:
        return [reverse_keys(item) for item in value]
    return value


def type_code(tree: dict) -> tuple:
    """Arity-delimited preorder tokens matching Lean's `typeCode` schema."""
    if "kind" in tree:
        return (("leaf", tree["kind"], tree["length"]),)
    if "tuple" in tree:
        return (("tuple", len(tree["tuple"])),) + tuple(
            token for child in tree["tuple"] for token in type_code(child))
    return (("record", tree["record"], len(tree["fields"])),) + tuple(
        token for field in tree["fields"]
        for token in (("field", field["name"]),) + type_code(field["type"]))


def descriptor_code(binding: dict) -> tuple:
    return tuple(type_code(root["type"]) for root in binding["inputs"]) + (
        type_code(binding["result"]["type"]),)


def all_type_trees(binding: dict):
    def descend(tree: dict):
        yield tree
        if "tuple" in tree:
            for child in tree["tuple"]:
                yield from descend(child)
        if "record" in tree:
            for field in tree["fields"]:
                yield from descend(field["type"])
    for root in binding["inputs"] + [binding["result"]]:
        yield from descend(root["type"])


def rename_path_part(binding: dict, tag: str, old: str, new: str) -> None:
    for root in binding["inputs"] + [binding["result"]]:
        for leaf in root["leaves"]:
            for part in leaf["path"]:
                if part.get(tag) == old:
                    part[tag] = new


def variants(base: dict) -> list[tuple[str, dict, bool]]:
    """Return changed source, and whether its type token stream must change."""
    result: list[tuple[str, dict, bool]] = []

    def add(label: str, source: dict, changed_type: bool) -> None:
        result.append((label, source, changed_type))

    source = copy.deepcopy(base)
    binding = source["public_abi"]
    binding["inputs"][0]["name"] = "request_new"
    rename_path_part(binding, "root", "req", "request_new")
    add("rename_public_root", source, False)

    source = copy.deepcopy(base)
    binding = source["public_abi"]
    binding["inputs"][1]["name"] = "secret_new"
    rename_path_part(binding, "root", "mask", "secret_new")
    add("rename_private_root", source, False)

    source = copy.deepcopy(base)
    binding = source["public_abi"]
    for tree in all_type_trees(binding):
        if tree.get("record") == "Inner":
            tree["record"] = "Inner_new"
    add("rename_repeated_nominal", source, True)

    source = copy.deepcopy(base)
    binding = source["public_abi"]
    for tree in all_type_trees(binding):
        if tree.get("record") == "Inner":
            tree["fields"][0]["name"] = "seed_new"
    rename_path_part(binding, "field", "seed", "seed_new")
    add("rename_repeated_field", source, True)

    source = copy.deepcopy(base)
    binding = source["public_abi"]
    binding["result"]["type"]["fields"].reverse()
    binding["result"]["leaves"] = ([binding["result"]["leaves"][2]] +
                                     binding["result"]["leaves"][:2])
    add("reorder_result_fields", source, True)

    source = copy.deepcopy(base)
    binding = source["public_abi"]
    binding["result"]["leaves"][1]["wire"] = "_s31_abi_input_1"
    source["public_outputs"] = ["y", "_s31_abi_input_1"]
    add("rebind_result_alias", source, False)

    source = copy.deepcopy(base)
    binding = source["public_abi"]
    binding["inputs"][0]["type"]["fields"][0]["type"]["tuple"][0]["kind"] = "bit"
    binding["inputs"][0]["leaves"][0]["kind"] = "bit"
    add("recode_public_m31_as_bit", source, True)

    return result


def invalid_variants(base: dict) -> list[tuple[str, dict]]:
    result = []
    source = copy.deepcopy(base)
    source["public_abi"]["inputs"][0]["leaves"][0]["wire"] = "y"
    result.append(("wrong_input_relation_wire", source))
    source = copy.deepcopy(base)
    source["public_abi"]["result"]["leaves"][0]["path"][-1] = {"field": "wrong"}
    result.append(("wrong_result_path", source))
    source = copy.deepcopy(base)
    source["public_abi"]["inputs"][1]["type"]["fields"][0]["type"]["kind"] = "bit"
    source["public_abi"]["inputs"][1]["leaves"][0]["kind"] = "bit"
    result.append(("private_bit_type", source))
    source = copy.deepcopy(base)
    source["public_abi"]["result"]["type"]["fields"][0]["type"]["tuple"][0]["fields"][0]["name"] = "other"
    result.append(("same_nominal_different_type_code", source))
    source = copy.deepcopy(base)
    source["public_abi"]["result"]["leaves"][0]["wire"] = "unknown_wire"
    result.append(("unknown_result_relation_wire", source))
    return result


def make_positive(label: str, source: dict, seed: int, *, source_bytes: bytes | None = None,
                  baseline_digest: str | None = None,
                  baseline_code: tuple | None = None,
                  changed_type: bool | None = None) -> dict:
    relation, binding = relation_and_binding(source)
    digest = binding_digest(relation, binding)
    direct_digest = hashlib.sha256(DOMAIN + canonical(binding)).hexdigest()
    if digest != direct_digest:
        raise AssertionError(f"independent canonical digest differs: {label}")
    if baseline_digest is not None and digest == baseline_digest:
        raise AssertionError(f"semantic descriptor mutation left digest unchanged: {label}")
    if baseline_code is not None and (descriptor_code(binding) != baseline_code) != changed_type:
        raise AssertionError(f"type-code sensitivity differs: {label}")
    statement, expected = encoded_claims(relation, binding, seed)
    encoded = canonical(statement)
    if (decode_public_statement(relation, binding, encoded) != expected or
            projection(source, statement)[3] != expected):
        raise AssertionError(f"statement projection differs: {label}")
    return {"label": label, "source": (source_bytes or canonical(source)).decode("ascii"),
            "expected_valid": True, "expected_digest": digest,
            "statement": encoded.decode("ascii"), "expected_words": expected}


def make_corpus() -> tuple[dict, dict]:
    cases: list[dict] = []
    for index, (label, text) in enumerate(sources()):
        source, _ = compile_text(text)
        cases.append(make_positive("compiled_" + label, source, index + 1))
    base, _ = compile_text(SOURCE)
    baseline = make_positive("compiled_nested_alias", base, 17)
    cases.append(baseline)
    relation, binding = relation_and_binding(base)
    baseline_code = descriptor_code(binding)
    reversed_source = (json.dumps(reverse_keys(base), separators=(",", ":")) + "\n").encode()
    if reversed_source == canonical(base) or json.loads(reversed_source) != base:
        raise AssertionError("reversed-key control did not preserve the parsed source")
    cases.append(make_positive("equivalent_reversed_json_keys", base, 17,
                               source_bytes=reversed_source))
    cases.append(make_positive("equivalent_pretty_json", base, 17,
                               source_bytes=(json.dumps(base, indent=2) + "\n").encode()))
    for label, changed, changed_type in variants(base):
        cases.append(make_positive(label, changed, 17,
                                   baseline_digest=baseline["expected_digest"],
                                   baseline_code=baseline_code,
                                   changed_type=changed_type))
    for label, changed in invalid_variants(base):
        relation, binding = relation_and_binding(changed)
        try:
            binding_digest(relation, binding)
        except AbiError:
            pass
        else:
            raise AssertionError(f"Python accepted invalid descriptor: {label}")
        cases.append({"label": label, "source": canonical(changed).decode("ascii"),
                      "expected_valid": False})
    corpus = {"schema": SCHEMA, "cases": cases}
    corpus_bytes = canonical(corpus)
    digest = hashlib.sha256(corpus_bytes).hexdigest()
    if CORPUS_SHA256 and digest != CORPUS_SHA256:
        raise AssertionError(f"descriptor corpus changed: {digest}; review and repin")
    report = {"schema": "s31-record-abi-digest-correspondence-v2",
              "corpus_sha256": digest,
              "accepted": sum(case["expected_valid"] for case in cases),
              "rejected": sum(not case["expected_valid"] for case in cases),
              "semantic_digest_changes": len(variants(base)),
              "compiled_source_layouts": len(sources()) + 1,
              "checked_native_outputs": sum(case["expected_valid"] for case in cases)}
    return corpus, report


def native(corpus: dict, report: dict) -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-digest-corpus-") as temporary:
        path = Path(temporary) / "corpus.json"
        def run(payload: dict) -> subprocess.CompletedProcess[str]:
            path.write_bytes(canonical(payload))
            command = ["zig", "build", "--build-file", str(S31 / "build.zig"),
                       "record-descriptor-parser-corpus", "-Doptimize=ReleaseFast", "-j1",
                       "--", str(path)]
            return subprocess.run(command, cwd=S31.parents[2], capture_output=True,
                                  text=True, check=False)

        result = run(corpus)
        if result.returncode:
            raise AssertionError("native digest/projection corpus failed:\n" +
                                 result.stdout[-4000:] + "\n" + result.stderr[-6000:])
        observed = json.loads(result.stdout)
        if observed != {"accepted": report["accepted"], "rejected": report["rejected"]}:
            raise AssertionError(f"native corpus counts differ: {observed}")
        report["native_parser"] = observed
        for label in ("wrong_expected_digest", "wrong_expected_words"):
            tampered = copy.deepcopy(corpus)
            first = tampered["cases"][0]
            if label == "wrong_expected_digest":
                first["expected_digest"] = "0" * 64
                expected_error = "canonical ABI digest differs"
            else:
                first["expected_words"][0] ^= 1
                expected_error = "projected public words differ"
            rejected = run(tampered)
            if (rejected.returncode == 0 or expected_error not in rejected.stderr or
                    "error: CorpusMismatch" not in rejected.stderr):
                raise AssertionError(f"native oracle failed {label} control: " +
                                     rejected.stderr[-2000:])
        report["native_oracle_negative_controls"] = 2


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="run production Zig parser, digest, and projection")
    args = parser.parse_args()
    corpus, report = make_corpus()
    if args.native:
        native(corpus, report)
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
