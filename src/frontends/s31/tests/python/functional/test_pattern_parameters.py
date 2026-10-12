"""Function parameter products are checked and erased before AIR lowering."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_text


class PatternParameterTests(unittest.TestCase):
    def check_direct(self, source: str, direct: str, inputs: dict[str, list[int]],
                     expected: int) -> None:
        relation, _ = compile_text(source)
        reference, _ = compile_text(direct)
        self.assertEqual(relation, reference)
        output = relation["public_outputs"][0]
        assignment = {"public_inputs": inputs, "private_inputs": {},
                      "public_outputs": {output: [expected]}}
        self.assertEqual(evaluate_relation(relation, assignment),
                         assignment["public_outputs"])
        assignment["public_outputs"][output][0] = expected + 1
        with self.assertRaises(OracleError):
            evaluate_relation(relation, assignment)

    def test_named_function_tuple_parameter_erases(self) -> None:
        source = """fn sum_product((a, b): ([m31; 1], [m31; 1])) -> [m31; 1] {
            a .* b + a
        }
        circuit p(public x: [m31; 1], public y: [m31; 1]) -> public [m31; 1] {
            sum_product((x, y))
        }"""
        direct = """circuit p(public x: [m31; 1], public y: [m31; 1])
            -> public [m31; 1] { x .* y + x }"""
        self.check_direct(source, direct, {"x": [7], "y": [9]}, 70)

    def test_lambda_parameter_can_unpack_function_value(self) -> None:
        source = """circuit p(public x: [m31; 1]) -> public [m31; 1] {
            let apply = fun((f, v): (Fn([m31; 1]) -> [m31; 1], [m31; 1]))
                -> [m31; 1] => f(v);
            apply((fun(y: [m31; 1]) -> [m31; 1] => y .* y, x))
        }"""
        direct = "circuit p(public x: [m31; 1]) -> public [m31; 1] { x .* x }"
        self.check_direct(source, direct, {"x": [11]}, 121)

    def test_parameter_components_are_eager_and_not_recomputed(self) -> None:
        source = """fn twice_first((a, ignored): ([m31; 1], [m31; 1]))
            -> [m31; 1] { a + a }
        circuit p(public x: [m31; 1]) -> public [m31; 1] {
            twice_first((x .* x, x + x))
        }"""
        direct = """circuit p(public x: [m31; 1]) -> public [m31; 1] {
            let square = x .* x;
            let ignored = x + x;
            square + square
        }"""
        relation, _ = compile_text(source)
        reference, _ = compile_text(direct)
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         ["mul", "add", "add"])
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         [node["op"] for node in reference["nodes"]])
        self.assertEqual(evaluate_relation(relation, {
            "public_inputs": {"x": [5]}, "private_inputs": {},
            "public_outputs": {relation["public_outputs"][0]: [50]}
        }), {relation["public_outputs"][0]: [50]})

    def test_record_parameter_uses_nominal_field_projection(self) -> None:
        source = """struct Pair { left: [m31; 1], right: [m31; 1] }
        fn add(Pair { left, right }: Pair) -> [m31; 1] { left + right }
        circuit p(public x: [m31; 1], public y: [m31; 1]) -> public [m31; 1] {
            add(Pair { right: y, left: x })
        }"""
        direct = """circuit p(public x: [m31; 1], public y: [m31; 1])
            -> public [m31; 1] { x + y }"""
        self.check_direct(source, direct, {"x": [3], "y": [5]}, 8)

    def test_patterned_step_survives_returned_function_route(self) -> None:
        source = """fn mix(v: [m31; 4]) -> [m31; 4] { std::math::mix4(v) }
        fn pass((step, state): (Fn([m31; 4]) -> [m31; 4], [m31; 4]))
            -> Fn([m31; 4]) -> [m31; 4] { step }
        fn go((step, state): (Fn([m31; 4]) -> [m31; 4], [m31; 4]))
            -> [m31; 4] { iterate<3>(pass((step, state)), state) }
        circuit p(public x: [m31; 4]) -> public [m31; 4] { go((mix, x)) }"""
        direct = """fn mix(v: [m31; 4]) -> [m31; 4] { std::math::mix4(v) }
        circuit p(public x: [m31; 4]) -> public [m31; 4] {
            iterate<3>(mix, x)
        }"""
        relation, _ = compile_text(source)
        self.assertEqual(relation, compile_text(direct)[0])
        self.assertEqual(relation["nodes"][0]["body"], [{"op": "mix4"}])

    def test_only_selected_nested_function_is_step_admitted(self) -> None:
        source = """fn square(v: [m31; 4]) -> [m31; 4] { v .* v }
        fn wrong(v: [m31; 4]) -> [m31; 4] { std::math::mix4(v) }
        fn route(((step, other), state):
            ((Fn([m31; 4]) -> [m31; 4], Fn([m31; 4]) -> [m31; 4]), [m31; 4]))
            -> [m31; 4] { iterate<3>(step, state) }
        circuit p(public x: [m31; 4]) -> public [m31; 4] {
            route(((square, wrong), x))
        }"""
        with self.assertRaisesRegex(SourceError, "std::math::mix4 requires an "):
            compile_text(source)

    def test_duplicate_and_incompatible_patterns_are_rejected(self) -> None:
        cases = (
            ("""fn bad((a, b): ([m31; 1], [m31; 1]), a: [m31; 1])
                -> [m31; 1] { a }
                circuit p(public x: [m31; 1]) -> public [m31; 1] { x }""",
             "duplicate parameter name"),
            ("""fn bad((a, b): [m31; 1]) -> [m31; 1] { a }
                circuit p(public x: [m31; 1]) -> public [m31; 1] { x }""",
             "tuple projection index is out of range"),
            ("""struct One { item: [m31; 1] }
                struct Two { item: [m31; 1] }
                fn bad(One { item }: Two) -> [m31; 1] { item }
                circuit p(public x: [m31; 1]) -> public [m31; 1] { x }""",
             "struct pattern expects One"),
            ("""circuit p(public (a, b): ([m31; 1], [m31; 1]))
                -> public [m31; 1] { a + b }""",
             "expected identifier"),
        )
        for source, message in cases:
            with self.subTest(message=message), self.assertRaisesRegex(
                SourceError, r"^<source>:[0-9]+:[0-9]+: " + message
            ):
                compile_text(source)

    def test_destructured_closure_preserves_inactive_branch_effect(self) -> None:
        source = """fn apply((f, x): (Fn([m31; 1]) -> [m31; 1], [m31; 1]))
            -> [m31; 1] { f(x) }
        circuit p(public b: bit, private x: [m31; 1]) -> public [m31; 1] {
            if b then apply((fun(v: [m31; 1]) -> [m31; 1] => std::math::inv(v), x))
                 else x
        }"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(source)

        returned = """fn choose((f, x): (Fn([m31; 1]) -> [m31; 1], [m31; 1]))
            -> Fn([m31; 1]) -> [m31; 1] { f }
        circuit p(public b: bit, private x: [m31; 1]) -> public [m31; 1] {
            if b then choose((fun(v: [m31; 1]) -> [m31; 1] =>
                std::math::inv(v), x))(x) else x
        }"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(returned)

        ignored_component = """fn first((a, ignored): ([m31; 1], [m31; 1]))
            -> [m31; 1] { a }
        circuit p(public b: bit, private x: [m31; 1]) -> public [m31; 1] {
            if b then first((x, std::math::inv(x))) else x
        }"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(ignored_component)


if __name__ == "__main__":
    unittest.main()
