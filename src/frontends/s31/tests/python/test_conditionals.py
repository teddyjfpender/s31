"""Witness-dependent branches must be typed, total and strict-select sized."""

import sys
import unittest
from pathlib import Path

SOURCE = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(SOURCE / "python"))

from language.builtins import BUILTINS, STANDARD_ALIASES
from language.effects import (CANONICAL_BUILTINS, PARTIAL_BUILTINS,
                              STEP_ONLY_BUILTINS, TOTAL_BUILTINS)
from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_text


class ConditionalTests(unittest.TestCase):
    def test_builtin_effect_inventory_is_exhaustive_and_disjoint(self) -> None:
        self.assertEqual(CANONICAL_BUILTINS,
                         {STANDARD_ALIASES.get(name, name) for name in BUILTINS})
        self.assertEqual(CANONICAL_BUILTINS | STEP_ONLY_BUILTINS,
                         TOTAL_BUILTINS | PARTIAL_BUILTINS)
        self.assertFalse(TOTAL_BUILTINS & PARTIAL_BUILTINS)

    def test_if_is_one_strict_select_node(self) -> None:
        inputs = "public b: bit, public x: [m31; 1], public y: [m31; 1]"
        conditional, _ = compile_text(f"circuit choose({inputs}) -> public [m31; 1] {{ if b then x else y }}")
        explicit, _ = compile_text(f"circuit choose({inputs}) -> public [m31; 1] {{ select(b, y, x) }}")
        self.assertEqual(conditional, explicit)
        self.assertEqual([node["op"] for node in conditional["nodes"]], ["select"])
        output = conditional["public_outputs"][0]
        for bit, expected in ((0, 9), (1, 5)):
            assignment = {"public_inputs": {"b": [bit], "x": [5], "y": [9]},
                          "private_inputs": {}, "public_outputs": {output: [expected]}}
            self.assertEqual(evaluate_relation(conditional, assignment), assignment["public_outputs"])
            assignment["public_outputs"][output] = [expected + 1]
            with self.assertRaises(OracleError):
                evaluate_relation(conditional, assignment)

    def test_bit_result_uses_constrained_boolean_select(self) -> None:
        relation, _ = compile_text("""circuit choose(public b: bit, public x: bit, public y: bit)
            -> public bit { if b then x else y }""")
        self.assertEqual([node["op"] for node in relation["nodes"]], ["bool_select"])
        self.assertEqual(relation["nodes"][0]["selector"], "b")

    def test_total_function_and_closure_calls_in_arms(self) -> None:
        relation, _ = compile_text("""fn plus_one(x: [m31; 1]) -> [m31; 1] {
            x + splat<1>(1_m31)
        }
        circuit choose(public b: bit, public x: [m31; 1]) -> public [m31; 1] {
            let square = fun(v: [m31; 1]) -> [m31; 1] => v .* v;
            if b then plus_one(x) else square(x)
        }""")
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         ["add_const", "mul", "select"])
        output = relation["public_outputs"][0]
        for bit, expected in ((0, 25), (1, 6)):
            assignment = {"public_inputs": {"b": [bit], "x": [5]},
                          "private_inputs": {}, "public_outputs": {output: [expected]}}
            self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])

    def test_partial_operations_in_either_arm_are_rejected_transitively(self) -> None:
        cases = (
            ("if b then std::math::inv(x) else x", "std::math::inv"),
            ("if b then x else std::math::div(x, x)", "std::math::div"),
            ("if b then checked(x) else x", "std::math::inv"),
            ("if b then f(x) else x", "std::math::inv"),
        )
        prefix = """fn checked(v: [m31; 1]) -> [m31; 1] { std::math::inv(v) }
        circuit choose(public b: bit, public x: [m31; 1]) -> public [m31; 1] {
            let f = fun(v: [m31; 1]) -> [m31; 1] => checked(v);
        """
        for expression, operation in cases:
            with self.subTest(expression=expression), self.assertRaisesRegex(
                SourceError, "if branch may fail when inactive: .*" + operation.replace("::", "::")
            ):
                compile_text(prefix + expression + "\n}")

    def test_partial_eight_bit_view_and_checked_integer_are_rejected(self) -> None:
        sources = (
            """circuit choose(public b: bit, public raw: [u16; 1], public valid: u8)
               -> public u8 { if b then std::int::from_limbs_u8(raw) else valid }""",
            """circuit choose(public b: bit, public x: u8, public y: u8)
               -> public u8 { if b then std::int::add_checked(x, y) else x }""",
        )
        for source in sources:
            with self.subTest(source=source), self.assertRaisesRegex(SourceError, "if branch may fail when inactive"):
                compile_text(source)

    def test_higher_order_effect_is_resolved_at_each_static_call(self) -> None:
        source = """fn choose(f: Fn([m31; 1]) -> [m31; 1], b: bit, x: [m31; 1])
          -> [m31; 1] { if b then f(x) else x }
        fn relay(g: Fn([m31; 1]) -> [m31; 1], b: bit, x: [m31; 1])
          -> [m31; 1] { choose(g, b, x) }
        circuit main(public b: bit, public x: [m31; 1]) -> public [m31; 1] {
          let identity = fun(v: [m31; 1]) -> [m31; 1] => v;
          relay(identity, b, x)
        }"""
        relation, _ = compile_text(source)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["select"])
        partial = source.replace("=> v;", "=> std::math::inv(v);")
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(partial)

    def test_opaque_call_cannot_mask_concrete_partial_operation(self) -> None:
        source = """fn unused(f: Fn([m31; 1]) -> [m31; 1], b: bit, x: [m31; 1])
          -> [m31; 1] { if b then f(x) + std::math::inv(x) else x }
        circuit main(public x: [m31; 1]) -> public [m31; 1] { x }"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(source)

    def test_dead_conditional_is_still_checked(self) -> None:
        source = """fn unused(b: bit, x: [m31; 1]) -> [m31; 1] {
          if b then std::math::inv(x) else x
        }
        circuit main(public x: [m31; 1]) -> public [m31; 1] { x }"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive"):
            compile_text(source)

    def test_condition_and_result_types_are_checked(self) -> None:
        cases = (
            ("if x then x else x", "if condition must have type bit"),
            ("if b then x else b", "if branches must have the same"),
            ("if b then [x] else [x]", "same first-order circuit type"),
        )
        for expression, message in cases:
            source = ("circuit main(public b: bit, public x: [m31; 1]) "
                      f"-> public [m31; 1] {{ {expression} }}")
            with self.subTest(expression=expression), self.assertRaisesRegex(SourceError, message):
                compile_text(source)

    def test_if_is_not_a_repeat_step(self) -> None:
        source = """fn step(v: [m31; 4]) -> [m31; 4] {
          if is_zero(std::array::get<0>(v)) then v .* v else v
        }
        circuit main(public x: [m31; 4]) -> public [m31; 4] {
          iterate<16>(step, x)
        }"""
        with self.assertRaisesRegex(SourceError, "iterate steps cannot contain"):
            compile_text(source)


if __name__ == "__main__":
    unittest.main()
