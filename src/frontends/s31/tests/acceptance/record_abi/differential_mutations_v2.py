#!/usr/bin/env python3
"""Deterministic Python/native verifier differential corpus for record ABI v2.

One real nested-record proof is held fixed. Malformed statements must fail in
both parsers; well-formed changed public claims must pass the Python ABI codec
and fail native proof verification. The corpus is generated, not sampled.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import re
import subprocess
import tempfile
from collections import Counter
from pathlib import Path

import nested_alias_v2 as fixture
from abi.binding_v2 import decode_public_statement
from abi.record_v2 import AbiError


# The first group fails before proof decoding. These errors arise in JSON
# parsing, canonical-byte checking, or the record statement validator.
PARSER_ERRORS = frozenset({"DuplicateField", "InvalidRecordAbi",
                           "InvalidRecordStatement", "SyntaxError",
                           "UnexpectedEndOfInput"})
# A shape-correct changed claim reaches proof verification. Keep this list
# specific so a parser rejection cannot masquerade as proof binding.
PROOF_ERRORS = frozenset({"InvalidInteractionNonce"})


def _error_name(stderr: str) -> str:
    match = re.search(r"(?m)^error: ([A-Za-z][A-Za-z0-9_]*)$", stderr)
    if match is None:
        raise AssertionError(f"native verifier returned no named error: {stderr[:1000]}")
    return match.group(1)


def _put(cases: dict[str, bytes], label: str, value: object) -> None:
    if label in cases:
        raise AssertionError(f"duplicate mutation label: {label}")
    cases[label] = fixture.canonical(value)


def _edited(base: dict, leaf: int, key: str, value: object) -> dict:
    changed = copy.deepcopy(base)
    changed["leaves"][leaf][key] = value
    return changed


def corpus(honest: bytes) -> tuple[dict[str, bytes], dict[str, bytes]]:
    """Return malformed statements and ABI-valid changed claims, in that order."""
    base = json.loads(honest)
    malformed: dict[str, bytes] = {}
    changed_claims: dict[str, bytes] = {}
    p = fixture.P

    # Every public leaf is checked independently, including both directions
    # of each alias. These are lexical/type/range cases, never arithmetic.
    bad_words = {"negative": -1, "modulus": p, "boolean": True,
                 "float": 1.0, "string": "1", "null": None}
    for index in range(len(base["leaves"])):
        for kind, bad in bad_words.items():
            _put(malformed, f"leaf_{index:02d}_word_{kind}",
                 _edited(base, index, "words", [bad]))
        for kind, words in {"empty": [], "two": [0, 1], "object": {"0": 1}}.items():
            _put(malformed, f"leaf_{index:02d}_shape_{kind}",
                 _edited(base, index, "words", words))

    # A path has a root, named fields, and possibly a tuple index. Mutate each
    # coordinate in each leaf while retaining canonical JSON framing.
    for leaf_index, leaf in enumerate(base["leaves"]):
        for segment_index, segment in enumerate(leaf["path"]):
            key = next(iter(segment))
            changes = ({"other": "changed", "wrong_type": 0, "extra_key": None}
                       if key != "tuple" else
                       {"other": 7, "negative": -1, "boolean": True,
                        "wrong_type": "0", "extra_key": None})
            for kind, replacement in changes.items():
                changed = copy.deepcopy(base)
                changed_segment = ({key: segment[key], "unused": 0}
                                   if kind == "extra_key" else {key: replacement})
                changed["leaves"][leaf_index]["path"][segment_index] = changed_segment
                _put(malformed, f"leaf_{leaf_index:02d}_path_{segment_index}_{kind}",
                     changed)

    # A single changed occurrence of either aliased wire is ill-formed even
    # when the word itself lies in M31.
    for index in (0, 3, 4, 5):
        original = base["leaves"][index]["words"][0]
        for word in (0, 1, p - 1):
            if word != original:
                _put(malformed, f"leaf_{index:02d}_alias_split_{word}",
                     _edited(base, index, "words", [word]))

    envelope = {
        "missing_version": lambda value: value.pop("version"),
        "wrong_version": lambda value: value.__setitem__("version", 1),
        "boolean_version": lambda value: value.__setitem__("version", True),
        "extra_field": lambda value: value.__setitem__("extra", 0),
        "missing_digest": lambda value: value.pop("abi_sha256"),
        "uppercase_digest": lambda value: value.__setitem__(
            "abi_sha256", value["abi_sha256"].upper()),
        "missing_leaf": lambda value: value["leaves"].pop(),
        "extra_leaf": lambda value: value["leaves"].append(
            copy.deepcopy(value["leaves"][-1])),
        "reordered_same_shape_inputs": lambda value: value["leaves"].__setitem__(
            slice(0, 2), list(reversed(value["leaves"][:2]))),
        "null_leaves": lambda value: value.__setitem__("leaves", None),
    }
    for label, mutate in envelope.items():
        changed = copy.deepcopy(base)
        mutate(changed)
        _put(malformed, f"envelope_{label}", changed)

    lexical = {
        "missing_final_newline": honest[:-1],
        "double_final_newline": honest + b"\n",
        "leading_space": b" " + honest,
        "noncanonical_indent": (json.dumps(base, indent=2) + "\n").encode(),
        "duplicate_version_key": honest.replace(
            b'"version":2', b'"version":2,"version":2', 1),
        "duplicate_leaf_words_key": honest.replace(
            b'"words":[2]', b'"words":[2],"words":[2]', 1),
        "duplicate_path_segment_key": honest.replace(
            b'{"tuple":0}', b'{"tuple":0,"tuple":0}', 1),
        "invalid_json": honest[:-2],
        "nan_word": honest.replace(b'"words":[2]', b'"words":[NaN]', 1),
        "escaped_root": honest.replace(b'"root":"req"', b'"root":"r\\u0065q"', 1),
        "too_large": honest + b" " * (1_000_001 - len(honest)),
    }
    for label, payload in lexical.items():
        if payload == honest or label in malformed:
            raise AssertionError(f"ineffective lexical mutation: {label}")
        malformed[f"lexical_{label}"] = payload

    # These claims are legal ABI objects: changing one source wire updates
    # every alias of that wire. The existing proof must reject each claim.
    for label, indices in (("first_input_and_result", (0, 4)),
                           ("second_tuple_input", (1,)),
                           ("nested_record_input", (2,)),
                           ("both_result_aliases", (3, 5))):
        for word in (0, 1, p - 2, p - 1):
            changed = copy.deepcopy(base)
            for index in indices:
                changed["leaves"][index]["words"] = [word]
            _put(changed_claims, f"{label}_{word}", changed)

    if len(malformed) != len(set(malformed.values())):
        raise AssertionError("malformed corpus contains duplicate statement bytes")
    if len(changed_claims) != len(set(changed_claims.values())):
        raise AssertionError("changed-claim corpus contains duplicate statement bytes")
    return malformed, changed_claims


def checked_corpus() -> tuple[dict, bytes, dict[str, bytes], dict[str, bytes], str]:
    source, _, honest, _, _, _ = fixture.static_checks()
    base = {**source, "version": 1}
    binding = base.pop("public_abi")
    expected = decode_public_statement(base, binding, honest)
    malformed, changed = corpus(honest)
    for label, payload in malformed.items():
        try:
            decode_public_statement(base, binding, payload)
        except AbiError:
            pass
        else:
            raise AssertionError(f"Python accepted malformed {label}")
    for label, payload in changed.items():
        words = decode_public_statement(base, binding, payload)
        if words == expected:
            raise AssertionError(f"ABI-valid {label} did not change public proof words")
    hasher = hashlib.sha256()
    for group, cases in ((b"malformed", malformed), (b"changed", changed)):
        for label, payload in cases.items():
            hasher.update(group + b"\0" + label.encode() + b"\0" + payload + b"\0")
    return source, honest, malformed, changed, hasher.hexdigest()


def native_checks() -> dict:
    _, honest, malformed, changed, corpus_sha256 = checked_corpus()
    with tempfile.TemporaryDirectory(prefix="s31-record-abi-differential-") as temporary:
        work = Path(temporary)
        source_path = work / "nested_alias.s31"
        source_path.write_text(fixture.SOURCE)
        package = fixture.s31.build(source_path, work / "package", "direct-gate")
        verifier = package / "bin/s31-nested_alias-native-verifier"
        key = package / "verification-key.json"
        assignment = work / "assignment.json"
        assignment.write_bytes(fixture.canonical(fixture.typed_case(2, 3, 5, 7)))
        report = fixture.s31.trial(package, assignment, work / "trial")
        proof = work / "trial/proof.bin"
        if (report["native_verifier_accepted"] is not True or
                (work / "trial/statement.json").read_bytes() != honest):
            raise AssertionError("native baseline proof/statement differs from Python fixture")
        scratch = work / "mutation.json"
        error_classes: dict[str, Counter[str]] = {
            "malformed": Counter(), "changed public claim": Counter()}
        unexpected: list[str] = []
        for classification, cases in (("malformed", malformed),
                                      ("changed public claim", changed)):
            for label, payload in cases.items():
                scratch.write_bytes(payload)
                result = subprocess.run((str(verifier), str(proof), str(scratch),
                                         str(key)), capture_output=True, text=True,
                                        timeout=60)
                if (result.returncode != 1 or "error:" not in result.stderr or
                        "panic:" in result.stderr):
                    raise AssertionError(f"native verifier failed {classification} "
                                         f"{label}: exit={result.returncode}, "
                                         f"stderr={result.stderr[:1000]}")
                error_name = _error_name(result.stderr)
                error_classes[classification][error_name] += 1
                allowed = (PARSER_ERRORS if classification == "malformed"
                           else PROOF_ERRORS)
                if error_name not in allowed:
                    unexpected.append(f"{classification}/{label}: {error_name}")
        if unexpected:
            raise AssertionError("native error-layer mismatch: " +
                                 ", ".join(unexpected) +
                                 f"; observed classes={error_classes}")
    return {"schema": "s31-record-abi-v2-differential-mutations-v1",
            "corpus_sha256": corpus_sha256,
            "malformed_rejected_by_python_and_native": len(malformed),
            "well_formed_changed_claims_rejected_at_native_proof": len(changed),
            "native_error_classes": {group: dict(counts)
                                     for group, counts in error_classes.items()},
            "baseline_native_proofs_accepted": 1}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--static", action="store_true",
                        help="check corpus against the Python ABI codec only")
    args = parser.parse_args()
    if args.static:
        _, _, malformed, changed, digest = checked_corpus()
        result = {"schema": "s31-record-abi-v2-differential-static-v1",
                  "corpus_sha256": digest,
                  "malformed_rejected_by_python": len(malformed),
                  "well_formed_changed_claims_accepted_by_python": len(changed)}
    else:
        result = native_checks()
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
