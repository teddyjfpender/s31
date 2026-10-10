"""Postfix function application must erase without weakening effect checks."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_text


P = (1 << 31) - 1


class PostfixApplicationTests(unittest.TestCase):
    def check_pair(self, functional: str, direct: str,
                   inputs: dict[str, list[int]], expected: list[int]) -> None:
        relation, _ = compile_text(functional)
        reference, _ = compile_text(direct)
        self.assertEqual(relation, reference)
        self.assertTrue(all(node["op"] not in {"apply", "lambda", "call"}
                            for node in relation["nodes"]))
        output = relation["public_outputs"][0]
        assignment = {"public_inputs": inputs, "private_inputs": {},
                      "public_outputs": {output: expected[:]}}
        self.assertEqual(evaluate_relation(relation, assignment),
                         assignment["public_outputs"])
        assignment["public_outputs"][output][0] = (expected[0] + 1) % P
        with self.assertRaises(OracleError):
            evaluate_relation(relation, assignment)

    def test_parenthesized_lambda_and_let_function(self) -> None:
        signature = "circuit p(public x: [m31; 4]) -> public [m31; 4] { "
        direct = signature + "x .* x + splat<4>(7_m31) }"
        inline = (signature + "(fun(v: [m31; 4]) -> [m31; 4] => "
                  "v .* v + splat<4>(7_m31))(x) }")
        captured = (signature + "(let saved = splat<4>(7_m31) in "
                    "fun(v: [m31; 4]) -> [m31; 4] => v .* v + saved)(x) }")
        words = [0, 1, 2, P - 1]
        expected = [(word * word + 7) % P for word in words]
        for source in (inline, captured):
            with self.subTest(source=source):
                self.check_pair(source, direct, {"x": words}, expected)

    def test_function_returning_function_and_curried_calls(self) -> None:
        source = """fn curry(a: [m31; 1])
          -> Fn([m31; 1]) -> Fn([m31; 1]) -> [m31; 1] {
          fun(b: [m31; 1]) -> Fn([m31; 1]) -> [m31; 1] =>
            fun(c: [m31; 1]) -> [m31; 1] => (a + b) + c
        }
        circuit p(public x: [m31; 1], public y: [m31; 1],
                  public z: [m31; 1]) -> public [m31; 1] {
          curry(x)(y)(z)
        }"""
        direct = """circuit p(public x: [m31; 1], public y: [m31; 1],
                  public z: [m31; 1]) -> public [m31; 1] { (x + y) + z }"""
        for x, y, z in ((0, 1, P - 1), (P - 1, P - 1, 3), (17, 29, 41)):
            with self.subTest(x=x, y=y, z=z):
                self.check_pair(source, direct,
                                {"x": [x], "y": [y], "z": [z]},
                                [(x + y + z) % P])

    def test_partial_operation_in_inactive_arm_is_rejected(self) -> None:
        source = """fn inverse() -> Fn([m31; 1]) -> [m31; 1] {
          fun(v: [m31; 1]) -> [m31; 1] => std::math::inv(v)
        }
        circuit p(public b: bit, private x: [m31; 1]) -> public [m31; 1] {
          if b then inverse()(x) else x
        }"""
        with self.assertRaisesRegex(
            SourceError, r"^<source>:[0-9]+:[0-9]+: if branch may fail when inactive: std::math::inv"
        ):
            compile_text(source)

    def test_factory_parameter_resolves_nested_application_effect(self) -> None:
        source = """fn use_factory(factory: Fn([m31; 1]) -> Fn([m31; 1]) -> [m31; 1],
          b: bit, x: [m31; 1]) -> [m31; 1] {
          if b then factory(x)(x) else x
        }
        circuit p(public b: bit, public x: [m31; 1]) -> public [m31; 1] {
          let factory = fun(base: [m31; 1]) -> Fn([m31; 1]) -> [m31; 1] =>
            fun(v: [m31; 1]) -> [m31; 1] => base + v;
          use_factory(factory, b, x)
        }"""
        direct = """circuit p(public b: bit, public x: [m31; 1])
          -> public [m31; 1] { if b then x + x else x }"""
        relation, _ = compile_text(source)
        reference, _ = compile_text(direct)
        self.assertEqual(relation, reference)
        output = relation["public_outputs"][0]
        for bit, value in ((0, P - 1), (1, P - 1), (1, 17)):
            expected = (value * (bit + 1)) % P
            assignment = {"public_inputs": {"b": [bit], "x": [value]},
                          "private_inputs": {}, "public_outputs": {output: [expected]}}
            self.assertEqual(evaluate_relation(relation, assignment),
                             assignment["public_outputs"])
        partial = source.replace("base + v", "std::math::inv(v)")
        with self.assertRaisesRegex(
            SourceError, "if branch may fail when inactive: std::math::inv"
        ):
            compile_text(partial)

    def test_invalid_application_has_located_diagnostic(self) -> None:
        sources = (
            ("circuit p(public x: [m31; 1]) -> public [m31; 1] { (x)(x) }",
             "applied expression must have a Fn type"),
            ("circuit p(public x: [m31; 1]) -> public [m31; 1] { "
             "(fun(v: [m31; 1]) -> [m31; 1] => v)() }",
             "function value expects 1 arguments"),
        )
        for source, message in sources:
            with self.subTest(message=message), self.assertRaisesRegex(
                SourceError, r"^<source>:[0-9]+:[0-9]+: " + message
            ):
                compile_text(source)


if __name__ == "__main__":
    unittest.main()
