"""Static products preserve types and eager effects while erasing from AIR."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from s31_stdlib import TypeErrorS31
from text_frontend import SourceError, compile_text


class TupleValuesTests(unittest.TestCase):
    def test_product_of_circuit_values_is_zero_cost(self) -> None:
        example = S31 / "examples/arithmetic/tuple_square_sum.s31"
        relation, _ = compile_text(example.read_text(), str(example))
        direct, _ = compile_text(example.with_name("tuple_square_sum_manual.s31").read_text())
        self.assertEqual(relation, direct)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["mul", "add", "add"])
        assignment = {"public_inputs": {}, "private_inputs": {"x": [0, 1, 2, 7]},
                      "public_outputs": {"result": [0, 3, 8, 63]}}
        self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])
        assignment["public_outputs"]["result"][3] = 64
        with self.assertRaises(OracleError):
            evaluate_relation(relation, assignment)

    def test_nested_product_and_function_value(self) -> None:
        source = """fn pair(f: Fn([m31; 1]) -> [m31; 1], x: [m31; 1])
          -> ((Fn([m31; 1]) -> [m31; 1], [m31; 1]), [m31; 1]) {
          ((f, x), x + x)
        }
        circuit p(public x: [m31; 1]) -> public [m31; 1] {
          let f = fun(v: [m31; 1]) -> [m31; 1] => v .* v;
          pair(f, x).0.0(pair(f, x).0.1)
        }"""
        # Both helper calls eagerly compute their second components.
        direct = """circuit p(public x: [m31; 1]) -> public [m31; 1] {
          let first = x + x;
          let second = x + x;
          x .* x
        }"""
        relation, _ = compile_text(source)
        reference, _ = compile_text(direct)
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         [node["op"] for node in reference["nodes"]])
        self.assertEqual(len(relation["nodes"]), 3)
        result = relation["public_outputs"][0]
        self.assertEqual(evaluate_relation(relation, {
            "public_inputs": {"x": [7]}, "private_inputs": {},
            "public_outputs": {result: [49]}}), {result: [49]})

    def test_expression_and_nested_pattern_destructuring(self) -> None:
        header = "circuit p(public x: [m31; 1]) -> public [m31; 1] { "
        block = header + "let ((a, b), c) = ((x .* x, x + x), x); let result = a + b + c; result }"
        expression = (header + "let result = let ((a, b), c) = ((x .* x, x + x), x) "
                      "in a + b + c; result }")
        direct = header + "let result = (x .* x) + (x + x) + x; result }"
        reference, _ = compile_text(direct)
        for source in (block, expression):
            with self.subTest(source=source):
                relation, _ = compile_text(source)
                self.assertEqual(relation, reference)
                self.assertEqual(evaluate_relation(relation, {
                    "public_inputs": {"x": [7]}, "private_inputs": {},
                    "public_outputs": {"result": [70]}}), {"result": [70]})

    def test_destructuring_preserves_function_and_eager_effects(self) -> None:
        source = """circuit p(public x: [m31; 1]) -> public [m31; 1] {
          let (f, v) = (fun(y: [m31; 1]) -> [m31; 1] => y .* y, x);
          f(v)
        }"""
        relation, _ = compile_text(source)
        direct, _ = compile_text("circuit p(public x: [m31; 1]) -> public [m31; 1] { x .* x }")
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         [node["op"] for node in direct["nodes"]])
        partial = """circuit p(public b: bit, private x: [m31; 1]) -> public [m31; 1] {
          if b then (let (kept, ignored) = (x, std::math::inv(x)) in kept) else x
        }"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(partial)

    def test_bad_projection_and_boundary_are_rejected(self) -> None:
        invalid = (
            ("circuit p(public x: [m31; 1]) -> public [m31; 1] { (x, x).2 }",
             "tuple projection index is out of range"),
            ("circuit p(public x: ([m31; 1], [m31; 1])) -> public [m31; 1] { x.0 }",
             "circuit inputs must be first-order values"),
            ("circuit p(public x: [m31; 1]) -> public ([m31; 1], [m31; 1]) { (x, x) }",
             "circuit output must be a first-order value"),
            ("circuit p(public x: [m31; 1]) -> public [m31; 1] { x.0 }",
             "tuple projection index is out of range"),
            ("circuit p(public x: [m31; 1]) -> public [m31; 1] { (x,) }",
             "expected expression"),
            ("circuit p(public x: [m31; 1]) -> public [m31; 1] { (x,x).field }",
             "expected a compile-time natural number"),
            ("circuit p(public x: [m31; 1]) -> public [m31; 1] { "
             "let (a,a) = (x,x) in a }", "duplicate tuple binding"),
            ("circuit p(public x: [m31; 1]) -> public [m31; 1] { "
             "let (a,b) = x in a }", "tuple projection index is out of range"),
        )
        for source, message in invalid:
            with self.subTest(source=source), self.assertRaisesRegex(SourceError, message):
                compile_text(source)

    def test_unselected_partial_component_still_rejected_in_inactive_arm(self) -> None:
        source = """circuit p(public b: bit, private x: [m31; 1]) -> public [m31; 1] {
          if b then (x, std::math::inv(x)).0 else x
        }"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(source)

    def test_tuple_projection_cannot_hide_unconstrained_bit_input(self) -> None:
        source = """circuit p(public b: bit, public x: [m31; 1]) -> public [m31; 1] {
          (b, x).1
        }"""
        with self.assertRaisesRegex(TypeErrorS31, "every bit input must be constrained"):
            compile_text(source)

    def test_pattern_nesting_is_bounded_with_location(self) -> None:
        pattern = "x"
        for index in range(33):
            pattern = f"({pattern}, other_{index})"
        source = ("circuit p(public x: [m31; 1]) -> public [m31; 1] { "
                  f"let {pattern} = x in x }}")
        with self.assertRaisesRegex(
            SourceError, r"^<source>:[0-9]+:[0-9]+: tuple pattern nesting limit exceeded"
        ):
            compile_text(source)

    def test_pattern_expansion_is_bounded_with_location(self) -> None:
        pattern = "(" + ", ".join(f"item_{index}" for index in range(4200)) + ")"
        for index in range(24):
            pattern = f"({pattern}, tail_{index})"
        source = ("circuit p(public x: [m31; 1]) -> public [m31; 1] { "
                  f"let {pattern} = x in x }}")
        with self.assertRaisesRegex(
            SourceError, r"^<source>:[0-9]+:[0-9]+: tuple pattern expansion limit exceeded"
        ):
            compile_text(source)

    def test_returned_tuple_can_supply_restricted_recurrence_step(self) -> None:
        source = """fn steps() -> (Fn([m31; 4]) -> [m31; 4],
                             Fn([m31; 4]) -> [m31; 4]) {
          (fun(v: [m31; 4]) -> [m31; 4] => std::math::mix4(v),
           fun(v: [m31; 4]) -> [m31; 4] => v)
        }
        circuit p(public x: [m31; 4]) -> public [m31; 4] {
          iterate<3>(steps().0, x)
        }"""
        direct = """circuit p(public x: [m31; 4]) -> public [m31; 4] {
          iterate<3>(fun(v: [m31; 4]) -> [m31; 4] => std::math::mix4(v), x)
        }"""
        relation, _ = compile_text(source)
        reference, _ = compile_text(direct)
        self.assertEqual(relation, reference)
        self.assertEqual(relation["nodes"][0]["body"], [{"op": "mix4"}])

    def test_tuple_factory_propagates_named_step_parameter(self) -> None:
        source = """fn mix(v: [m31; 4]) -> [m31; 4] { std::math::mix4(v) }
        fn relay(f: Fn([m31; 4]) -> [m31; 4])
          -> (Fn([m31; 4]) -> [m31; 4], Fn([m31; 4]) -> [m31; 4]) {
          (f, f)
        }
        circuit p(public x: [m31; 4]) -> public [m31; 4] {
          iterate<3>(relay(mix).0, x)
        }"""
        relation, _ = compile_text(source)
        self.assertEqual(relation["nodes"][0]["body"], [{"op": "mix4"}])
        destructured = source.replace("iterate<3>(relay(mix).0, x)",
                                      "let (selected, unused) = relay(mix); iterate<3>(selected, x)")
        self.assertEqual(compile_text(destructured)[0], relation)
        with self.assertRaisesRegex(SourceError, r"requires an \[m31; 4\] iterate state"):
            compile_text(source.replace("iterate<3>(relay(mix).0, x)", "mix(x)"))


if __name__ == "__main__":
    unittest.main()
