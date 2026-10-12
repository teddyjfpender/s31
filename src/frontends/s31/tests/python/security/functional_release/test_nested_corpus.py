"""Exhaustive small nested-call corpus for the independent release checker.

Each source is checked against production compilation and a separately
written first-order program. The modular integer oracle does not call either
source parser. This is finite differential evidence, not a compiler proof.
"""

from __future__ import annotations

import hashlib
import sys
import unittest
from pathlib import Path


S31 = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation  # noqa: E402
from package.correspondence import canonical_ir_bytes, parse_source  # noqa: E402
from package.direct_gate_schedule import exact_direct_gate_schedule  # noqa: E402
from text_frontend import compile_text  # noqa: E402


P = (1 << 31) - 1
T = "[m31; 4]"
ROUTES = ("direct", "identity", "identity2", "relay", "wrap", "bound", "lexical")
STYLES = ("plain", "parenthesized", "whitespace")
CORPUS_SHA256 = "c342b334209828c8d3e5ff6cbe1f3d140706db2a38146f6ce67c6c5ee2d2b693"


def cases() -> list[tuple[str, str, str, str, str]]:
    result: list[tuple[str, str, str, str, str]] = []
    for first in ("+", ".*"):
        second = ".*" if first == "+" else "+"
        for combine in ("+", ".*"):
            for route in ROUTES:
                helpers = [
                    f"fn make(a: {T}) -> Fn({T}) -> {T} {{ "
                    f"let saved = a {first} a; "
                    f"fun(v: {T}) -> {T} => saved {combine} v }}",
                    f"fn twice(a: {T}) -> {T} {{ a {second} a }}",
                ]
                if route in {"identity", "identity2", "relay", "wrap", "bound", "lexical"}:
                    helpers.append(f"fn identity(f: Fn({T}) -> {T}) -> Fn({T}) -> {T} {{ f }}")
                if route == "relay":
                    helpers.append(f"fn relay(f: Fn({T}) -> {T}) -> Fn({T}) -> {T} "
                                   "{ identity(f) }")
                if route == "wrap":
                    helpers.append(f"fn wrap(a: {T}) -> Fn({T}) -> {T} {{ make(a) }}")
                expression = {
                    "direct": "make(x)(twice(x))",
                    "identity": "identity(make(x))(twice(x))",
                    "identity2": "identity(identity(make(x)))(twice(x))",
                    "relay": "relay(make(x))(twice(x))",
                    "wrap": "identity(wrap(x))(twice(x))",
                    "bound": "identity(make(x))",
                    "lexical": "let f = make(x) in identity(f)(twice(x))",
                }[route]
                body = (f"let f = {expression}; let result = f(twice(x)); result"
                        if route == "bound" else f"let result = {expression}; result")
                manual = (f"circuit c(public x: {T}) -> public {T} {{ "
                          f"let saved = x {first} x; "
                          f"let arg = x {second} x; "
                          f"let result = saved {combine} arg; result }}")
                for style in STYLES:
                    styled_body = body
                    if style == "parenthesized":
                        styled_body = styled_body.replace("make(x)", "(make(x))")
                        styled_body = styled_body.replace("wrap(x)", "(wrap(x))")
                        styled_body = styled_body.replace("twice(x)", "(twice(x))")
                    elif style == "whitespace":
                        styled_body = styled_body.replace("; ", ";\n\t")
                    source = ("\n".join(helpers) + "\n" +
                              f"circuit c(public x: {T}) -> public {T} {{ {styled_body} }}")
                    label = f"{first}:{combine}:{route}:{style}"
                    result.append((label, source, manual, first, combine))
    return result


def corpus_digest(samples: list[tuple[str, str, str, str, str]]) -> str:
    encoded = b"".join(label.encode() + b"\0" + source.encode() + b"\0" +
                       manual.encode() + b"\0" for label, source, manual, _, _ in samples)
    return hashlib.sha256(encoded).hexdigest()


class NestedCorpusTests(unittest.TestCase):
    def test_nested_calls_have_exact_direct_schedule_and_independent_values(self) -> None:
        samples = cases()
        self.assertEqual(len(samples), 2 * 2 * len(ROUTES) * len(STYLES))
        self.assertEqual(corpus_digest(samples), CORPUS_SHA256)
        for label, source, manual, first, combine in samples:
            with self.subTest(case=label):
                checked, syntax = parse_source(source.encode())
                produced, _ = compile_text(source)
                direct, direct_syntax = parse_source(manual.encode())
                self.assertEqual(checked, produced)
                self.assertEqual(len(checked["nodes"]), 3)
                self.assertEqual(canonical_ir_bytes(syntax), canonical_ir_bytes(direct_syntax))
                self.assertEqual(exact_direct_gate_schedule(syntax),
                                 exact_direct_gate_schedule(direct_syntax))
                self.assertEqual(direct, compile_text(manual)[0])
                for x in (0, 1, 7, P - 1):
                    saved = (2 * x if first == "+" else x * x) % P
                    arg = (x * x if first == "+" else 2 * x) % P
                    value = (saved + arg if combine == "+" else saved * arg) % P
                    assignment = {"public_inputs": {"x": [x] * 4},
                                  "private_inputs": {},
                                  "public_outputs": {"result": [value] * 4}}
                    self.assertEqual(evaluate_relation(checked, assignment),
                                     assignment["public_outputs"])
                    assignment["public_outputs"]["result"][3] = (value + 1) % P
                    with self.assertRaises(OracleError):
                        evaluate_relation(checked, assignment)


if __name__ == "__main__":
    unittest.main()
