#!/usr/bin/env python3
"""Pinned source-text to normalized relation and native record ABI audit.

The positive cases are written as S31 source variants, then compiled by the
production text frontend. Handwritten path/shape/wire expectations catch a
bad lowering even when Python and Zig agree on the same bad JSON. The native
corpus subsequently checks the digest and final public words independently.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json

from descriptor_digest_correspondence_v2 import (
    SCHEMA, canonical, descriptor_code, make_positive, native,
)
from nested_alias_v2 import S31

import sys
sys.path.insert(0, str(S31 / "python"))
from abi.binding_v2 import binding_digest  # noqa: E402
from abi.record_v2 import AbiError  # noqa: E402
from language.syntax import SourceError  # noqa: E402
from text_frontend import compile_text  # noqa: E402

CORPUS_SHA256 = "b43e2f3003d77fbfe90c220d0de63270952e43e4f276e25ab9da072d551bc04e"
SOURCE_SHA256 = "c43501bb95e8892d23aa17a428fd4b8e8744b9608e59cc31388f9f966a530218"

BASE = """struct Inner { a: [m31; 1], b: [m31; 1] }
struct Request { inner: Inner, flag: bit }
struct Secret { delta: [m31; 1] }
struct Result { first: [m31; 1], second: [m31; 1] }
circuit map(public req: Request, private secret: Secret) -> public Result {
 let x = req.inner.a + secret.delta;
 Result { first: x, second: req.inner.b }
}
"""


def replace(source: str, old: str, new: str, *, occurrences: int = 1) -> str:
    if source.count(old) != occurrences:
        raise AssertionError(f"source edit expected {occurrences} occurrence(s) of {old!r}")
    return source.replace(old, new)


def texts() -> list[tuple[str, str]]:
    result = [("baseline", BASE)]
    changed = replace(BASE, "struct Inner { a:", "struct Inner { alpha:")
    result.append(("rename_field", replace(changed, "req.inner.a", "req.inner.alpha")))
    result.append(("reorder_fields", replace(BASE,
        "struct Inner { a: [m31; 1], b: [m31; 1] }",
        "struct Inner { b: [m31; 1], a: [m31; 1] }")))
    changed = replace(BASE, "inner: Inner", "inner: (Inner, [m31; 1])")
    changed = replace(changed, "req.inner.a", "req.inner.0.a")
    result.append(("nested_tuple", replace(changed, "req.inner.b", "req.inner.0.b")))
    changed = replace(BASE, "struct Inner { a: [m31; 1]", "struct Inner { a: [m31; 2]")
    changed = replace(changed, "delta: [m31; 1]", "delta: [m31; 2]")
    result.append(("width_two", replace(changed, "first: [m31; 1]", "first: [m31; 2]")))
    result.append(("result_alias_a", replace(BASE, "second: req.inner.b", "second: req.inner.a")))
    changed = replace(BASE,
        "struct Result { first: [m31; 1], second: [m31; 1] }",
        "struct Result { second: [m31; 1], first: [m31; 1] }")
    result.append(("result_order", replace(changed,
        "Result { first: x, second: req.inner.b }",
        "Result { second: req.inner.b, first: x }")))
    result.append(("public_secret", replace(BASE, "private secret: Secret", "public secret: Secret")))
    changed = replace(BASE, "secret: Secret", "mask: Secret")
    result.append(("rename_private_root", replace(changed, "secret.delta", "mask.delta")))
    changed = replace(BASE,
        "struct Result { first: [m31; 1], second: [m31; 1] }",
        "struct Result { inner: Inner }")
    result.append(("nested_result", replace(changed,
        "Result { first: x, second: req.inner.b }",
        "Result { inner: Inner { a: x, b: req.inner.b } }")))
    changed = replace(BASE, "req: Request", "request: Request")
    result.append(("rename_public_root", replace(changed, "req.inner", "request.inner", occurrences=2)))
    result.append(("m31_flag", replace(BASE, "flag: bit", "flag: [m31; 1]")))
    return result


def leaf(path: str, kind: str, width: int, wire: str, visibility: str) -> tuple:
    return (path, kind, width, wire, visibility)


def expected_summaries() -> dict[str, list[tuple]]:
    """Handwritten named paths, ABI types, wire indices, and visibility."""
    base = [
        leaf("req.inner.a", "m31", 1, "_s31_abi_input_0", "public"),
        leaf("req.inner.b", "m31", 1, "_s31_abi_input_1", "public"),
        leaf("req.flag", "bit", 1, "_s31_abi_input_2", "public"),
        leaf("secret.delta", "m31", 1, "_s31_abi_input_3", "private"),
        leaf("result.first", "m31", 1, "x", "result"),
        leaf("result.second", "m31", 1, "_s31_abi_input_1", "result"),
    ]
    result = {"baseline": base}
    changed = base.copy()
    changed[0] = leaf("req.inner.alpha", "m31", 1, "_s31_abi_input_0", "public")
    result["rename_field"] = changed
    changed = base.copy()
    changed[0] = leaf("req.inner.b", "m31", 1, "_s31_abi_input_0", "public")
    changed[1] = leaf("req.inner.a", "m31", 1, "_s31_abi_input_1", "public")
    changed[5] = leaf("result.second", "m31", 1, "_s31_abi_input_0", "result")
    result["reorder_fields"] = changed
    changed = base.copy()
    changed[0] = leaf("req.inner.0.a", "m31", 1, "_s31_abi_input_0", "public")
    changed[1] = leaf("req.inner.0.b", "m31", 1, "_s31_abi_input_1", "public")
    changed.insert(2, leaf("req.inner.1", "m31", 1, "_s31_abi_input_2", "public"))
    changed[3] = leaf("req.flag", "bit", 1, "_s31_abi_input_3", "public")
    changed[4] = leaf("secret.delta", "m31", 1, "_s31_abi_input_4", "private")
    result["nested_tuple"] = changed
    changed = base.copy()
    changed[0] = leaf("req.inner.a", "m31", 2, "_s31_abi_input_0", "public")
    changed[3] = leaf("secret.delta", "m31", 2, "_s31_abi_input_3", "private")
    changed[4] = leaf("result.first", "m31", 2, "x", "result")
    result["width_two"] = changed
    changed = base.copy()
    changed[5] = leaf("result.second", "m31", 1, "_s31_abi_input_0", "result")
    result["result_alias_a"] = changed
    changed = base.copy()
    changed[4:] = [base[5], base[4]]
    result["result_order"] = changed
    changed = base.copy()
    changed[3] = leaf("secret.delta", "m31", 1, "_s31_abi_input_3", "public")
    result["public_secret"] = changed
    changed = base.copy()
    changed[3] = leaf("mask.delta", "m31", 1, "_s31_abi_input_3", "private")
    result["rename_private_root"] = changed
    changed = base.copy()
    changed[4] = leaf("result.inner.a", "m31", 1, "x", "result")
    changed[5] = leaf("result.inner.b", "m31", 1, "_s31_abi_input_1", "result")
    result["nested_result"] = changed
    changed = base.copy()
    for at in range(3):
        changed[at] = (changed[at][0].replace("req.", "request."),) + changed[at][1:]
    result["rename_public_root"] = changed
    changed = base.copy()
    changed[2] = leaf("req.flag", "m31", 1, "_s31_abi_input_2", "public")
    result["m31_flag"] = changed
    return result


def summary(source: dict) -> list[tuple]:
    roots = source["public_abi"]["inputs"] + [source["public_abi"]["result"]]
    return [
        (".".join(str(next(iter(part.values()))) for part in item["path"]),
         item["kind"], item["length"], item["wire"], root.get("visibility", "result"))
        for root in roots for item in root["leaves"]
    ]


def wrong_descriptors(source: dict) -> list[tuple[str, dict]]:
    """Keep the normalized relation fixed while corrupting ABI declarations."""
    changed: list[tuple[str, dict]] = []

    candidate = copy.deepcopy(source)
    leaves = candidate["public_abi"]["inputs"][0]["leaves"]
    leaves[0], leaves[1] = leaves[1], leaves[0]
    changed.append(("swap_input_leaves", candidate))

    candidate = copy.deepcopy(source)
    leaf = candidate["public_abi"]["inputs"][0]["leaves"][0]
    leaf["length"] += 1
    changed.append(("wrong_input_width", candidate))

    candidate = copy.deepcopy(source)
    candidate["public_abi"]["inputs"][0]["visibility"] = "private"
    changed.append(("flip_root_visibility", candidate))

    candidate = copy.deepcopy(source)
    candidate["public_abi"]["inputs"][0]["leaves"][0]["path"].append(
        {"field": "phantom"})
    changed.append(("wrong_field_path", candidate))

    candidate = copy.deepcopy(source)
    candidate["public_abi"]["result"]["leaves"][-1]["wire"] = "unknown_wire"
    changed.append(("wrong_result_wire", candidate))

    candidate = copy.deepcopy(source)
    candidate["public_abi"]["result"]["leaves"][0]["kind"] = "bit"
    changed.append(("wrong_result_kind", candidate))
    return changed


def make_corpus() -> tuple[dict, dict]:
    fixtures = texts()
    expected = expected_summaries()
    if set(expected) != {label for label, _ in fixtures}:
        raise AssertionError("source fixtures and handwritten expectations differ")
    source_hash = hashlib.sha256("".join(label + "\0" + text for label, text in fixtures).encode()).hexdigest()
    if SOURCE_SHA256 and source_hash != SOURCE_SHA256:
        raise AssertionError(f"source text corpus changed: {source_hash}; review and repin")
    cases = []
    base_digest = None
    base_code = None
    code_change_expected = {"rename_field", "reorder_fields", "nested_tuple",
                            "width_two", "result_order", "nested_result", "m31_flag"}
    for label, text in fixtures:
        source, _ = compile_text(text)
        observed = summary(source)
        if observed != expected[label]:
            raise AssertionError(f"source lowering changed {label}:\n{observed}\nexpected {expected[label]}")
        if label == "baseline":
            base_code = descriptor_code(source["public_abi"])
        elif (descriptor_code(source["public_abi"]) != base_code) != (label in code_change_expected):
            raise AssertionError(f"source variant changed unexpected type-code part: {label}")
        case = make_positive("text_" + label, source, 17)
        if label == "baseline":
            base_digest = case["expected_digest"]
        elif case["expected_digest"] == base_digest:
            raise AssertionError(f"changed text kept baseline ABI digest: {label}")
        cases.append(case)
        for mutation, broken in wrong_descriptors(source):
            relation = {**broken, "version": 1}
            binding = relation.pop("public_abi")
            try:
                binding_digest(relation, binding)
            except AbiError:
                pass
            else:
                raise AssertionError(f"Python ABI accepted {label}/{mutation}")
            cases.append({"label": f"text_{label}/{mutation}",
                          "source": canonical(broken).decode("ascii"),
                          "expected_valid": False})
    if base_code is None:
        raise AssertionError("baseline type code missing")
    # The source type checker must reject a private bit-bearing root before a
    # normalized relation reaches native validation.
    private_bit = replace(BASE, "public req: Request", "private req: Request")
    try:
        compile_text(private_bit)
    except SourceError as exc:
        if "private bit leaves" not in str(exc):
            raise
        pass
    else:
        raise AssertionError("text frontend admitted a private bit-bearing record")
    corpus = {"schema": SCHEMA, "cases": cases}
    corpus_hash = hashlib.sha256(canonical(corpus)).hexdigest()
    if CORPUS_SHA256 and corpus_hash != CORPUS_SHA256:
        raise AssertionError(f"text lowering corpus changed: {corpus_hash}; review and repin")
    report = {"schema": "s31-record-abi-text-lowering-correspondence-v2",
              "source_sha256": source_hash, "corpus_sha256": corpus_hash,
              "compiled_source_variants": len(fixtures),
              "accepted": len(fixtures), "rejected": len(cases) - len(fixtures),
              "adversarial_descriptor_mutations_per_source": 6,
              "text_private_bit_rejected": True}
    return corpus, report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true", help="check production Zig descriptor digest and word projection")
    args = parser.parse_args()
    corpus, report = make_corpus()
    if args.native:
        native(corpus, report)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
