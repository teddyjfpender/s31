"""Typed nested helper arguments must replay production evaluation order."""

from __future__ import annotations

import hashlib
import sys
import unittest
from pathlib import Path


S31 = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation  # noqa: E402
from package.correspondence import (UnsupportedFragment, canonical_ir_bytes,
                                    parse_source)  # noqa: E402
from package.direct_gate_schedule import exact_direct_gate_schedule  # noqa: E402
from text_frontend import compile_text  # noqa: E402


T = "[m31; 4]"
CIRCUIT = f"circuit c(public x: {T}) -> public {T} {{ let result = EXPR; result }}"
SQUARE = f"fn square(a: {T}) -> {T} {{ a .* a }}\n"
TWICE = f"fn twice(a: {T}) -> {T} {{ a + a }}\n"
P = (1 << 31) - 1
CORPUS_SHA256 = "910ceeadcc4a09e0da02ae9e23b5b64470b811723eda53d0d283a970bafda124"


def corpus() -> list[tuple[str, str, str, str, str]]:
    samples: list[tuple[str, str, str, str, str]] = []
    for first in ("+", ".*"):
        for last in ("+", ".*"):
            for route in ("nested-call", "nested-gate", "captured-function"):
                direct_body = (f"let w = x {first} x; let result = " +
                               (f"x {last} w" if route == "captured-function"
                                else f"w {last} w") + "; result")
                manual = f"circuit c(public x: {T}) -> public {T} {{ {direct_body} }}"
                first_fn = f"fn first(a: {T}) -> {T} {{ a {first} a }}\n"
                if route == "nested-call":
                    declarations = (first_fn + f"fn final(a: {T}) -> {T} {{ a {last} a }}\n" +
                                    f"fn composed(a: {T}) -> {T} {{ final(first(a)) }}\n")
                elif route == "nested-gate":
                    declarations = (f"fn final(a: {T}) -> {T} {{ a {last} a }}\n" +
                                    f"fn composed(a: {T}) -> {T} {{ final(a {first} a) }}\n")
                else:
                    declarations = (first_fn +
                                    f"fn apply(f: Fn({T}) -> {T}, v: {T}) -> {T} {{ f(v) }}\n" +
                                    f"fn composed(a: {T}) -> {T} {{ "
                                    f"apply(fun(v: {T}) -> {T} => a {last} v, first(a)) }}\n")
                for style in ("plain", "whitespace"):
                    body = "let result = composed(x); result"
                    if style == "whitespace":
                        body = body.replace("; ", ";\n\t")
                    source = declarations + f"circuit c(public x: {T}) -> public {T} {{ {body} }}"
                    samples.append((f"{first}:{last}:{route}:{style}", source,
                                    manual, first, last))
    return samples


def corpus_digest(samples: list[tuple[str, str, str, str, str]]) -> str:
    return hashlib.sha256(b"".join(
        label.encode() + b"\0" + source.encode() + b"\0" + manual.encode() + b"\0"
        for label, source, manual, _, _ in samples)).hexdigest()


class NestedHelperBodyTests(unittest.TestCase):
    def test_nested_body_corpus_has_direct_schedule_and_values(self) -> None:
        samples = corpus()
        self.assertEqual(len(samples), 24)
        self.assertEqual(corpus_digest(samples), CORPUS_SHA256)
        for label, source, manual, first, last in samples:
            with self.subTest(case=label):
                checked, syntax = parse_source(source.encode())
                direct, direct_syntax = parse_source(manual.encode())
                self.assertEqual(checked, compile_text(source)[0])
                self.assertEqual(direct, compile_text(manual)[0])
                self.assertEqual(canonical_ir_bytes(syntax), canonical_ir_bytes(direct_syntax))
                self.assertEqual(exact_direct_gate_schedule(syntax),
                                 exact_direct_gate_schedule(direct_syntax))
                for x in (0, 1, 7, P - 1):
                    w = (2 * x if first == "+" else x * x) % P
                    left = x if "captured-function" in label else w
                    value = (left + w if last == "+" else left * w) % P
                    assignment = {"public_inputs": {"x": [x] * 4},
                                  "private_inputs": {},
                                  "public_outputs": {"result": [value] * 4}}
                    self.assertEqual(evaluate_relation(checked, assignment),
                                     assignment["public_outputs"])
                    assignment["public_outputs"]["result"][0] = (value + 1) % P
                    with self.assertRaises(OracleError):
                        evaluate_relation(checked, assignment)

    def test_inline_capture_and_nested_array_call_match_handwritten_source(self) -> None:
        example = S31 / "examples/functional/release_helper_composition4"
        source = (example / "functional.s31").read_text()
        direct = (example / "manual.s31").read_text()
        checked = parse_source(source.encode())
        self.assertEqual(checked, parse_source(direct.encode()))
        self.assertEqual(checked[0], compile_text(source)[0])
        self.assertEqual([node["name"] for node in checked[0]["nodes"]],
                         ["_s31_0", "result"])

    def test_nested_calls_and_arithmetic_arguments_match_production(self) -> None:
        sources = (
            SQUARE + TWICE + f"fn compose(a: {T}) -> {T} {{ twice(square(a)) }}\n" +
            CIRCUIT.replace("EXPR", "compose(x)"),
            TWICE + f"fn compose(a: {T}) -> {T} {{ twice(a + a) }}\n" +
            CIRCUIT.replace("EXPR", "compose(x)"),
            f"fn make(a: {T}) -> Fn({T}) -> {T} {{ "
            f"fun(v: {T}) -> {T} => v + a }}\n" +
            f"fn identity(f: Fn({T}) -> {T}) -> Fn({T}) -> {T} {{ f }}\n" +
            f"fn relay(a: {T}) -> Fn({T}) -> {T} {{ identity(make(a)) }}\n" +
            CIRCUIT.replace("EXPR", "relay(x)(x)"),
        )
        for index, source in enumerate(sources):
            with self.subTest(route=index):
                checked, _ = parse_source(source.encode())
                self.assertEqual(checked, compile_text(source)[0])
                self.assertGreaterEqual(len(checked["nodes"]), 1)

    def test_nested_arguments_are_type_checked_before_emission(self) -> None:
        make = f"fn make(a: {T}) -> Fn({T}) -> {T} {{ " \
               f"fun(v: {T}) -> {T} => v + a }}\n"
        identity = f"fn identity(f: Fn({T}) -> {T}) -> Fn({T}) -> {T} {{ f }}\n"
        sources = (
            SQUARE + make + f"fn wrong(a: {T}) -> {T} {{ square(make(a)) }}\n" +
            CIRCUIT.replace("EXPR", "wrong(x)"),
            SQUARE + identity + f"fn wrong(a: {T}) -> Fn({T}) -> {T} "
            "{ identity(square(a)) }\n" +
            CIRCUIT.replace("EXPR", "wrong(x)(x)"),
            TWICE + f"fn wrong(a: {T}) -> {T} {{ twice(missing(a)) }}\n" +
            CIRCUIT.replace("EXPR", "wrong(x)"),
        )
        for index, source in enumerate(sources):
            with self.subTest(rejection=index), self.assertRaises(UnsupportedFragment):
                parse_source(source.encode())


if __name__ == "__main__":
    unittest.main()
