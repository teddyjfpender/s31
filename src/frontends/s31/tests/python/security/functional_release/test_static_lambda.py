"""Captured lambda values erase to their body gates with lexical capture."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import UnsupportedFragment, parse_source  # noqa: E402
from text_frontend import compile_text  # noqa: E402

HEADER = "circuit calc(public x: [m31; 4]) -> public [m31; 4] {\n"
TAIL = "  result\n}\n"
LAMBDA = "fun(v: [m31; 4]) -> [m31; 4] => v .* v"
APPLY = ("fn apply(f: Fn([m31; 4]) -> [m31; 4], v: [m31; 4]) "
         "-> [m31; 4] { f(v) }\n")


class StaticLambdaReleaseTests(unittest.TestCase):
    def test_uncaptured_lambda_and_static_passage_have_one_gate(self) -> None:
        direct = parse_source((HEADER + "  let result = x .* x;\n" + TAIL).encode())
        programs = (
            HEADER + f"  let f = {LAMBDA};\n  let result = f(x);\n" + TAIL,
            APPLY + HEADER + f"  let f = {LAMBDA};\n"
            "  let g = f;\n  let result = apply(g, x);\n" + TAIL,
            HEADER + f"  let f = {LAMBDA};\n"
            "  let result = let g = f in g(x);\n" + TAIL,
        )
        for index, source in enumerate(programs):
            with self.subTest(route=index):
                checked = parse_source(source.encode())
                self.assertEqual(checked, direct)
                self.assertEqual(checked[0], compile_text(source)[0])

    def test_capture_survives_shadowing_and_matches_handwritten_gates(self) -> None:
        example = S31 / "examples/functional/release_closure4"
        source = (example / "functional.s31").read_text()
        manual = (example / "manual.s31").read_text()
        checked = parse_source(source.encode())
        self.assertEqual(checked, parse_source(manual.encode()))
        self.assertEqual(checked[0], compile_text(source)[0])
        self.assertEqual(len(checked[0]["nodes"]), 3)
        self.assertEqual(checked[0]["nodes"][-1]["lhs"], "saved")
        self.assertEqual(checked[0]["nodes"][-1]["rhs"], "_s31_0")

    def test_lambda_call_preserves_later_helper_wire_numbering(self) -> None:
        source = ("fn twice(v: [m31; 4]) -> [m31; 4] { "
                  "let s = v .* v; v + s }\n" + HEADER +
                  "  let f = fun(v: [m31; 4]) -> [m31; 4] => x + v;\n"
                  "  let first = f(x);\n  let result = twice(first);\n" + TAIL)
        checked = parse_source(source.encode())
        self.assertEqual(checked[0], compile_text(source)[0])
        self.assertEqual(checked[0]["nodes"][1]["name"], "_s31_i1_0")

    def test_unbound_ill_typed_and_non_gate_lambdas_are_rejected(self) -> None:
        programs = (
            HEADER + "  let f = fun(v: [m31; 4]) -> [m31; 4] => v + missing;\n"
            "  let result = f(x);\n" + TAIL,
            HEADER + "  let f = fun(v: [m31; 2]) -> [m31; 4] => v .* v;\n"
            "  let result = f(x);\n" + TAIL,
            HEADER + "  let f = fun(v: [m31; 4]) -> [m31; 4] => v + x + x;\n"
            "  let result = f(x);\n" + TAIL,
            HEADER + "  let f = fun(v: [m31; 4]) -> [m31; 4] => v;\n"
            "  let result = f(x);\n" + TAIL,
            HEADER + f"  let f = {LAMBDA};\n  let result = f(f);\n" + TAIL,
            HEADER + f"  let f = {LAMBDA};\n  let result = x .* x;\n  f\n}}\n",
        )
        for index, source in enumerate(programs):
            with self.subTest(rejection=index), self.assertRaises(UnsupportedFragment):
                parse_source(source.encode())


if __name__ == "__main__":
    unittest.main()
