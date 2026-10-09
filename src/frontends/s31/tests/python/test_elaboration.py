"""Whole-program source typing must catch dead-code defects without emission."""

import sys
import unittest
from pathlib import Path
from unittest.mock import patch

SOURCE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(SOURCE / "python"))

from language.elaborate import Elaborator
from language.builtin_types import infer_builtin
from language.builtins import BUILTINS, STANDARD_ALIASES
from language.parser import Parser
from text_frontend import SourceError, compile_text


CIRCUIT = "circuit main(public x: [m31; 1]) -> public [m31; 1] { x }"


class ElaborationTests(unittest.TestCase):
    def test_every_registered_builtin_has_an_elaboration_rule(self) -> None:
        for name in sorted(BUILTINS):
            canonical = STANDARD_ALIASES.get(name, name)
            if canonical == "iterate":
                continue  # This has a checked user-function signature.
            with self.subTest(name=name):
                try:
                    infer_builtin(canonical, None, ())
                except ValueError as exc:
                    self.assertNotIn("unknown builtin or wrong arity", str(exc))

    def test_unused_function_bodies_are_checked(self) -> None:
        cases = (
            ("fn unused(x: [m31; 1]) -> [m31; 1] { x + missing }", "unknown value missing"),
            ("fn unused(x: [m31; 1]) -> [m31; 2] { x }", "result does not match"),
            ("fn unused(x: [m31; 1]) -> [m31; 1] { assert_eq(x, x); x }",
             "pure functions cannot contain assertions"),
            ("fn unused(x: [m31; 1]) -> [m31; 1] { std::math::sum([x, x .* x]) + bad }",
             "unknown value bad"),
            ("fn unused(f: Fn([m31; 2]) -> [m31; 1], x: [m31; 1]) -> [m31; 1] { f(x) }",
             "function value argument 1 expects"),
        )
        for declaration, message in cases:
            with self.subTest(message=message), self.assertRaisesRegex(SourceError, message):
                compile_text(f"{declaration}\n{CIRCUIT}", "unused.s31")

    def test_unused_lambda_body_is_checked_at_definition(self) -> None:
        cases = (
            ("fun(y: [m31; 1]) -> [m31; 2] => y", "function value result does not match"),
            ("fun(y: [m31; 1]) -> [m31; 1] => absent + y", "unknown value absent"),
        )
        for expression, message in cases:
            source = f"circuit main(public x: [m31; 1]) -> public [m31; 1] {{ let f = {expression}; x }}"
            with self.subTest(message=message), self.assertRaisesRegex(SourceError, message):
                compile_text(source, "lambda.s31")

    def test_unused_recursive_function_is_rejected(self) -> None:
        source = "fn unused(x: [m31; 1]) -> [m31; 1] { unused(x) }\n" + CIRCUIT
        with self.assertRaisesRegex(SourceError, "recursive"):
            compile_text(source)

    def test_shared_call_graph_still_rejects_deep_path(self) -> None:
        functions = [f"fn f{i}(x: [m31; 1]) -> [m31; 1] {{ f{i + 1}(x) }}"
                     for i in range(33)]
        functions.append("fn f33(x: [m31; 1]) -> [m31; 1] { x }")
        source = "\n".join(functions + [CIRCUIT])
        with self.assertRaisesRegex(SourceError, "excessively deep"):
            compile_text(source)

    def test_elaboration_does_not_construct_a_builder(self) -> None:
        source = """fn f(x: [m31; 1]) -> [m31; 1] {
            let square = fun(y: [m31; 1]) -> [m31; 1] => y .* y;
            square(x)
        }
        circuit main(public x: [m31; 1]) -> public [m31; 1] { f(x) }"""
        functions, circuit = Parser(source, "pure.s31").parse()
        with patch("s31_stdlib.Builder", side_effect=AssertionError("emitted during elaboration")):
            Elaborator(functions, circuit, "pure.s31").check()

    def test_dead_partial_operation_is_typed_without_evaluation(self) -> None:
        source = """fn unused() -> [m31; 1] { std::math::inv(splat<1>(0_m31)) }
        circuit main(public x: [m31; 1]) -> public [m31; 1] { x }"""
        relation, _ = compile_text(source)
        self.assertEqual(relation["nodes"], [])


if __name__ == "__main__":
    unittest.main()
