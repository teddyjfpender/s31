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
    def test_inline_lambda_passed_to_fn_erases_to_handwritten_gates(self) -> None:
        example = S31 / "examples/functional/release_inline_lambda4"
        source = (example / "functional.s31").read_text()
        manual = (example / "manual.s31").read_text()
        checked = parse_source(source.encode())
        self.assertEqual(checked, parse_source(manual.encode()))
        self.assertEqual(checked[0], compile_text(source)[0])
        self.assertEqual([node["name"] for node in checked[0]["nodes"]],
                         ["_s31_i1_0", "result"])

    def test_inline_lambda_captures_current_lexical_wire(self) -> None:
        source = (APPLY + HEADER +
                  "  let saved = x .* x;\n"
                  "  let result = let y = x + x in "
                  "apply(fun(v: [m31; 4]) -> [m31; 4] => saved + v, y);\n" +
                  TAIL)
        checked = parse_source(source.encode())
        self.assertEqual(checked[0], compile_text(source)[0])
        self.assertEqual(checked[0]["nodes"][-1]["lhs"], "saved")
        self.assertEqual(checked[0]["nodes"][-1]["rhs"], "_s31_0")

    def test_expression_templates_match_production(self) -> None:
        bodies = (
            "v .* v", "v + v", "x + v", "v + x", "x .* v", "v .* x",
            "x + v .* v", "x + (v .* v)",
            "let t = v .* v in x + t",
            "let t = x + v in v .* t",
            "v .* (x + v)",
            "let t = v .* v in let u = x + t in x + u",
            "let t = v in t .* t",
        )
        for body in bodies:
            source = (HEADER +
                      "  let f = fun(v: [m31; 4]) -> [m31; 4] => " + body + ";\n"
                      "  let result = f(x);\n" + TAIL)
            with self.subTest(body=body):
                checked = parse_source(source.encode())
                self.assertEqual(checked[0], compile_text(source)[0])

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
        self.assertEqual(len(checked[0]["nodes"]), 4)
        self.assertEqual(checked[0]["nodes"][-1]["lhs"], "saved")
        self.assertEqual(checked[0]["nodes"][-1]["rhs"], "_s31_1")

    def test_nested_arithmetic_and_local_let_have_the_same_residual_circuit(self) -> None:
        programs = (
            HEADER + "  let f = fun(v: [m31; 4]) -> [m31; 4] => x + v .* v;\n"
            "  let result = f(x);\n" + TAIL,
            HEADER + "  let f = fun(v: [m31; 4]) -> [m31; 4] => "
            "let saved = v .* v in x + saved;\n  let result = f(x);\n" + TAIL,
        )
        checked = [parse_source(source.encode()) for source in programs]
        self.assertEqual(checked[0], checked[1])
        for source, relation in zip(programs, checked):
            self.assertEqual(relation[0], compile_text(source)[0])
        self.assertEqual([node["name"] for node in checked[0][0]["nodes"]],
                         ["_s31_0", "result"])

    def test_identity_lambda_is_a_wire_alias(self) -> None:
        source = (HEADER + "  let saved = x .* x;\n"
                  "  let f = fun(v: [m31; 4]) -> [m31; 4] => v;\n"
                  "  let result = f(saved);\n" + TAIL)
        checked = parse_source(source.encode())
        self.assertEqual(checked[0], compile_text(source)[0])
        self.assertEqual(len(checked[0]["nodes"]), 1)
        self.assertEqual(checked[0]["public_outputs"], ["saved"])

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
            HEADER + "  let f = fun(v: [m31; 4]) -> [m31; 4] => v + 1_m31;\n"
            "  let result = f(x);\n" + TAIL,
            HEADER + "  let f = fun(v: [m31; 4]) -> [m31; 4] => v;\n"
            "  let result = f(x);\n" + TAIL,
            HEADER + f"  let f = {LAMBDA};\n  let result = f(f);\n" + TAIL,
            HEADER + f"  let f = {LAMBDA};\n  let result = x .* x;\n  f\n}}\n",
            APPLY + HEADER + "  let result = apply("
            "fun(v: [m31; 2]) -> [m31; 4] => v .* v, x);\n" + TAIL,
            APPLY + HEADER + "  let result = apply("
            "fun(v: [m31; 4]) -> [m31; 4] => missing + v, x);\n" + TAIL,
        )
        for index, source in enumerate(programs):
            with self.subTest(rejection=index), self.assertRaises(UnsupportedFragment):
                parse_source(source.encode())


if __name__ == "__main__":
    unittest.main()
