#!/usr/bin/env python3
"""Pinned S31 text-to-native record statement and evaluated-word corpus.

The expected values come from the small source equations below, not from the
Python relation evaluator or statement decoder. The native runner checks its
own ABI parser, flat assignment projection, and relation evaluator together.
This is a finite executable audit, not a parser or compiler theorem.
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

from nested_alias_v2 import S31
from text_lowering_correspondence_v2 import expected_summaries, summary, texts

sys.path.insert(0, str(S31 / "python"))
from abi.binding_v2 import statement_from_assignment  # noqa: E402
from text_frontend import compile_text  # noqa: E402

P = 2**31 - 1
SCHEMA = "s31-record-statement-native-corpus-v2"
CORPUS_SHA256 = "37ca9286ff4e6fb5b43bc3ee6fe8f3512bea594ed9e90ae239e00f97716afdde"


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")


def input_words(path: str, width: int) -> list[int]:
    if path.endswith((".a", ".alpha")):
        return [2, 3][:width]
    if path.endswith(".b"):
        return [5][:width]
    if path.endswith(".flag"):
        return [1]
    if path.endswith(".delta"):
        return [7, 11][:width]
    if path.endswith(".inner.1"):
        return [13]
    raise AssertionError(f"unreviewed source input path: {path}")


def case_for(label: str, source_text: str, expected: list[tuple]) -> dict:
    source, _ = compile_text(source_text)
    if summary(source) != expected:
        raise AssertionError(f"{label}: compiled descriptor diverged from handwritten paths/wires")
    flat: dict[str, object] = {"public_inputs": {}, "private_inputs": {}, "public_outputs": {}}
    by_wire: dict[str, list[int]] = {}
    a: list[int] | None = None
    delta: list[int] | None = None
    expected_words: list[int] = []
    for path, _kind, width, wire, visibility in expected:
        if visibility == "result":
            continue
        words = input_words(path, width)
        if len(words) != width or wire in by_wire:
            raise AssertionError(f"{label}: invalid handwritten input width or duplicate wire")
        by_wire[wire] = words
        flat[f"{visibility}_inputs"][wire] = words
        if visibility == "public":
            expected_words.extend(words)
        if path.endswith((".a", ".alpha")):
            a = words
        if path.endswith(".delta"):
            delta = words
    if a is None or delta is None or len(a) != len(delta):
        raise AssertionError(f"{label}: missing equal-width arithmetic operands")
    by_wire["x"] = [(left + right) % P for left, right in zip(a, delta)]
    result_wires = list(dict.fromkeys(wire for _, _, _, wire, visibility in expected
                                     if visibility == "result"))
    if source["public_outputs"] != result_wires:
        raise AssertionError(f"{label}: relation result wire order differs from handwritten leaves")
    for wire in result_wires:
        words = by_wire[wire]
        flat["public_outputs"][wire] = words
        expected_words.extend(words)
    if not 1 <= len(expected_words) <= 8:
        raise AssertionError(f"{label}: public word count outside native budget")
    expected_words += [0] * (8 - len(expected_words))
    statement = statement_from_assignment(source, flat)
    return {"label": label, "source": canonical(source).decode("ascii"),
            "statement": statement.decode("ascii"),
            "assignment": canonical(flat).decode("ascii"),
            "expected_words": expected_words}


def make_corpus() -> tuple[dict, dict]:
    expected = expected_summaries()
    fixtures = texts()
    if {label for label, _ in fixtures} != set(expected):
        raise AssertionError("source cases and handwritten summaries differ")
    cases = [case_for(label, source_text, expected[label]) for label, source_text in fixtures]
    corpus = {"schema": SCHEMA, "cases": cases}
    digest = hashlib.sha256(canonical(corpus)).hexdigest()
    if CORPUS_SHA256 and digest != CORPUS_SHA256:
        raise AssertionError(f"review and repin changed corpus: {digest}")
    return corpus, {"schema": "s31-nested-record-relation-word-correspondence-v2",
                    "corpus_sha256": digest, "compiled_source_cases": len(cases),
                    "assignment_and_evaluation_checked": len(cases)}


def check_native(corpus: dict, report: dict) -> None:
    with tempfile.TemporaryDirectory(prefix="s31-record-relation-word-corpus-") as temporary:
        path = Path(temporary) / "corpus.json"

        def run(value: dict) -> subprocess.CompletedProcess[str]:
            path.write_bytes(canonical(value))
            return subprocess.run(
                ["zig", "build", "--build-file", str(S31 / "build.zig"),
                 "record-statement-parser-corpus", "-j1", "--", str(path)],
                cwd=S31.parents[2], capture_output=True, text=True, check=False)

        completed = run(corpus)
        if completed.returncode:
            raise AssertionError("native relation-word corpus failed:\n" + completed.stderr[-6000:])
        observed = json.loads(completed.stdout)
        if observed != {"accepted": report["compiled_source_cases"], "rejected": 0}:
            raise AssertionError(f"native case count differs: {observed}")
        report["native_parser"] = observed

        wrong_words = copy.deepcopy(corpus)
        wrong_words["cases"][0]["expected_words"][0] ^= 1
        rejected = run(wrong_words)
        if (rejected.returncode == 0 or "projected wrong words" not in rejected.stderr or
                "error: CorpusMismatch" not in rejected.stderr):
            raise AssertionError("native expected-word oracle failed its corruption control")

        wrong_private = copy.deepcopy(corpus)
        assignment = json.loads(wrong_private["cases"][0]["assignment"])
        assignment["private_inputs"]["_s31_abi_input_3"] = [8]
        wrong_private["cases"][0]["assignment"] = canonical(assignment).decode("ascii")
        rejected = run(wrong_private)
        if (rejected.returncode == 0 or
                "relation evaluation failed: PublicOutputMismatch" not in rejected.stderr or
                "error: CorpusMismatch" not in rejected.stderr):
            raise AssertionError("native evaluator failed its private-witness corruption control")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native", action="store_true",
                        help="check native record parser, flat projection, and evaluator")
    args = parser.parse_args()
    corpus, report = make_corpus()
    if args.native:
        check_native(corpus, report)
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
