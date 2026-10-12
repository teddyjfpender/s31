"""Returned static functions and curried calls erase without extra gates."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import UnsupportedFragment, parse_source  # noqa: E402
from package import correspondence  # noqa: E402
from text_frontend import compile_text  # noqa: E402

T = "[m31; 4]"
CIRCUIT = f"circuit c(public x: {T}) -> public {T} {{ let result = EXPR; result }}"
SQUARE = f"fn square(v: {T}) -> {T} {{ v .* v }}\n"


class ReturnedFunctionReleaseTests(unittest.TestCase):
    def test_gate_free_factory_expansion_has_an_independent_call_budget(self) -> None:
        source = (SQUARE +
                  f"fn choose() -> Fn({T}) -> {T} {{ square }}\n" +
                  CIRCUIT.replace("EXPR", "choose()(x)"))
        with patch.object(correspondence, "MAX_STATIC_CALLS", 1):
            with self.assertRaisesRegex(UnsupportedFragment, "expansion exceeds"):
                parse_source(source.encode())

    def test_captured_factory_matches_handwritten_two_gate_source(self) -> None:
        example = S31 / "examples/functional/release_curried4"
        source = (example / "functional.s31").read_text()
        manual = (example / "manual.s31").read_text()
        checked = parse_source(source.encode())
        self.assertEqual(checked, parse_source(manual.encode()))
        self.assertEqual(checked[0], compile_text(source)[0])
        self.assertEqual([node["name"] for node in checked[0]["nodes"]],
                         ["_s31_i1_0", "result"])

    def test_nested_function_and_array_arguments_match_handwritten_gates(self) -> None:
        example = S31 / "examples/functional/release_nested4"
        source = (example / "functional.s31").read_text()
        manual = (example / "manual.s31").read_text()
        checked = parse_source(source.encode())
        self.assertEqual(checked, parse_source(manual.encode()))
        self.assertEqual(checked[0], compile_text(source)[0])
        self.assertEqual([node["name"] for node in checked[0]["nodes"]],
                         ["_s31_i1_0", "_s31_0", "result"])

    def test_nested_zero_arg_factory_can_be_passed_as_function_value(self) -> None:
        source = (SQUARE +
                  f"fn choose() -> Fn({T}) -> {T} {{ square }}\n" +
                  f"fn identity(f: Fn({T}) -> {T}) -> Fn({T}) -> {T} {{ f }}\n" +
                  CIRCUIT.replace("EXPR", "identity(choose())(x)"))
        checked = parse_source(source.encode())
        self.assertEqual(checked[0], compile_text(source)[0])
        self.assertEqual(len(checked[0]["nodes"]), 1)

    def test_returned_named_function_alias_and_relay_match_production(self) -> None:
        factory = f"fn make(a: {T}) -> Fn({T}) -> {T} {{ " \
                  f"fun(v: {T}) -> {T} => a + v }}\n"
        sources = (
            SQUARE + f"fn choose() -> Fn({T}) -> {T} {{ square }}\n" +
            CIRCUIT.replace("EXPR", "choose()(x)"),
            SQUARE + f"fn identity(f: Fn({T}) -> {T}) -> Fn({T}) -> {T} {{ f }}\n" +
            CIRCUIT.replace("EXPR", "identity(square)(x)"),
            factory + f"fn relay(a: {T}) -> Fn({T}) -> {T} {{ make(a) }}\n" +
            CIRCUIT.replace("EXPR", "relay(x)(x)"),
            factory + (f"circuit c(public x: {T}) -> public {T} {{ "
                       "let f = make(x); let result = f(x); result }"),
            factory + CIRCUIT.replace("EXPR", "let f = make(x) in f(x)"),
        )
        for index, source in enumerate(sources):
            with self.subTest(route=index):
                checked = parse_source(source.encode())
                self.assertEqual(checked[0], compile_text(source)[0])
                self.assertEqual(len(checked[0]["nodes"]), 1)

    def test_ill_typed_factory_and_invalid_postfix_calls_are_rejected(self) -> None:
        factory = f"fn make(a: {T}) -> Fn({T}) -> {T} {{ " \
                  f"fun(v: {T}) -> {T} => a + v }}\n"
        bad = (
            f"fn wrong(a: {T}) -> Fn({T}) -> {T} {{ a + a }}\n" +
            CIRCUIT.replace("EXPR", "wrong(x)(x)"),
            f"fn wrong(a: {T}) -> Fn({T}) -> {T} {{ "
            f"fun(v: [m31; 2]) -> {T} => a + v }}\n" +
            CIRCUIT.replace("EXPR", "wrong(x)(x)"),
            f"fn wrong(a: {T}) -> Fn({T}) -> {T} {{ "
            f"fun(v: {T}) -> {T} => missing + v }}\n" +
            CIRCUIT.replace("EXPR", "wrong(x)(x)"),
            SQUARE + CIRCUIT.replace("EXPR", "square(x)(x)"),
            factory + f"fn apply(f: Fn({T}) -> {T}, v: {T}) -> {T} {{ f(v) }}\n" +
            CIRCUIT.replace("EXPR", "apply(make, x)"),
            SQUARE + f"fn choose() -> Fn({T}) -> {T} {{ square }}\n" +
            CIRCUIT.replace("EXPR", "choose(x)"),
            SQUARE + f"fn identity(f: Fn({T}) -> {T}) -> Fn({T}) -> {T} {{ f }}\n" +
            CIRCUIT.replace("EXPR", "identity(square(x))(x)"),
        )
        for index, source in enumerate(bad):
            with self.subTest(rejection=index), self.assertRaises(UnsupportedFragment):
                parse_source(source.encode())


if __name__ == "__main__":
    unittest.main()
