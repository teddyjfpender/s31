"""Static sum tags select one source arm and disappear before relation lowering."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_text


class StaticSumTests(unittest.TestCase):
    def test_reverse_arm_order_and_exact_direct_relation(self) -> None:
        wrapped = """enum Choice { Square: [m31; 4], Double: [m31; 4] }
fn choose(x: [m31; 4]) -> Choice { Choice::Square(x) }
fn run(choice: Choice) -> [m31; 4] {
    match choice {
        Choice::Double(z) => z + z,
        Choice::Square(y) => y .* y
    }
}
circuit p(private x: [m31; 4]) -> public [m31; 4] {
    let result = run(choose(x));
    result
}"""
        direct = """circuit p(private x: [m31; 4]) -> public [m31; 4] {
    let result = x .* x;
    result
}"""
        wrapped_relation, _ = compile_text(wrapped)
        direct_relation, _ = compile_text(direct)
        self.assertEqual(wrapped_relation, direct_relation)
        self.assertEqual(evaluate_relation(wrapped_relation, {
            "public_inputs": {}, "private_inputs": {"x": [0, 1, 2, 7]},
            "public_outputs": {"result": [0, 1, 4, 49]},
        }), {"result": [0, 1, 4, 49]})

    def test_constructor_payload_eager_selected_arm_only_and_no_tag_wire(self) -> None:
        source = """enum Choice { Left: [m31; 4], Right: [m31; 4] }
fn choose(x: [m31; 4]) -> Choice { Choice::Left(x .* x) }
fn unwrap(choice: Choice) -> [m31; 4] {
    match choice { Choice::Left(v) => v + v, Choice::Right(v) => v .* v }
}
circuit p(private x: [m31; 4]) -> public [m31; 4] {
    let out = unwrap(choose(x));
    out
}"""
        relation, _ = compile_text(source)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["mul", "add"])
        self.assertEqual([item["name"] for item in relation["inputs"]], ["x"])
        self.assertEqual(evaluate_relation(relation, {
            "public_inputs": {}, "private_inputs": {"x": [0, 1, 2, 7]},
            "public_outputs": {"out": [0, 2, 8, 98]},
        }), {"out": [0, 2, 8, 98]})

        eager = """enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let choice = Choice::Left(x .* x);
    let out = match choice { Choice::Left(v) => x, Choice::Right(v) => v };
    out
}"""
        eager_relation, _ = compile_text(eager)
        # Specialization evaluates the payload; the total, unobserved
        # multiplication is erased before the relation crosses to native AIR.
        self.assertEqual(eager_relation["nodes"], [])

    def test_known_tag_erases_inactive_partial_arm(self) -> None:
        source = """enum Choice { Left: u16, Right: u16 }
circuit p(private x: u16) -> public u16 {
    let choice = Choice::Left(x);
    let out = match choice {
        Choice::Left(v) => v,
        Choice::Right(v) => std::int::div_checked(v, v)
    };
    out
}"""
        relation, _ = compile_text(source)
        self.assertNotIn("int_div_rem", [node["op"] for node in relation["nodes"]])

    def test_generic_static_match_defers_effect_until_the_tag_is_known(self) -> None:
        prelude = """enum Choice { Safe: [m31; 1], Risky: [m31; 1] }
fn choose(choice: Choice, flag: bit, x: [m31; 1]) -> [m31; 1] {
    if flag then match choice {
        Choice::Safe(v) => v + v,
        Choice::Risky(v) => std::math::inv(v)
    } else x
}
fn relay(choice: Choice, flag: bit, x: [m31; 1]) -> [m31; 1] {
    choose(choice, flag, x)
}
"""
        circuit = """circuit p(public flag: bit, private x: [m31; 1]) -> public [m31; 1] {
    let out = relay(Choice::Safe(x), flag, x);
    out
}"""
        relation, _ = compile_text(prelude + circuit)
        direct, _ = compile_text("""circuit p(public flag: bit, private x: [m31; 1])
            -> public [m31; 1] { let out = if flag then x + x else x; out }""")
        self.assertEqual(relation, direct)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["add", "select"])
        for flag, expected in ((0, 7), (1, 14)):
            with self.subTest(flag=flag):
                assignment = {"public_inputs": {"flag": [flag]},
                              "private_inputs": {"x": [7]},
                              "public_outputs": {"out": [expected]}}
                self.assertEqual(evaluate_relation(relation, assignment),
                                 assignment["public_outputs"])
                assignment["public_outputs"]["out"] = [expected + 1]
                with self.assertRaises(OracleError):
                    evaluate_relation(relation, assignment)

        risky = circuit.replace("Choice::Safe(x)", "Choice::Risky(x)")
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(prelude + risky)

        # Building the selected static variant is still eager. Its payload
        # failure cannot be hidden in a dynamically inactive `if` arm.
        eager = prelude + """circuit p(public flag: bit, private x: [m31; 1])
            -> public [m31; 1] {
            let out = if flag then
                relay(Choice::Safe(std::math::inv(x)), flag, x)
            else x;
            out
        }"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(eager)

    def test_unselected_static_arm_defers_its_nested_dynamic_if(self) -> None:
        prelude = """enum Choice { Safe: [m31; 1], Risky: [m31; 1] }
fn choose(choice: Choice, flag: bit) -> [m31; 1] {
    match choice {
        Choice::Safe(v) => v + v,
        Choice::Risky(v) => if flag then std::math::inv(v) else v
    }
}
"""
        circuit = """circuit p(public flag: bit, private x: [m31; 1])
            -> public [m31; 1] {
            let out = if flag then choose(Choice::Safe(x), flag) else x;
            out
        }"""
        relation, _ = compile_text(prelude + circuit)
        direct, _ = compile_text("""circuit p(public flag: bit, private x: [m31; 1])
            -> public [m31; 1] { let out = if flag then x + x else x; out }""")
        self.assertEqual(relation, direct)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["add", "select"])

        selected_risky = circuit.replace("Choice::Safe(x)", "Choice::Risky(x)")
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(prelude + selected_risky)

    def test_dynamic_if_cannot_hide_partial_constructor_payload(self) -> None:
        source = """enum Choice { Left: u16, Right: u16 }
circuit p(private x: u16, private flag: bit) -> public u16 {
    let out = if flag then
        match Choice::Left(std::int::div_checked(x, x)) {
            Choice::Left(v) => v, Choice::Right(v) => v
        }
    else x;
    out
}"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive"):
            compile_text(source)

    def test_static_sum_types_and_match_are_checked_before_lowering(self) -> None:
        prefix = "enum Choice { Left: [m31; 1], Right: [m31; 1] }\n"
        cases = (
            ("match Choice::Left(x) { Choice::Left(v) => v }", "non-exhaustive Choice match"),
            ("match Choice::Left(x) { Choice::Left(v) => v, Choice::Left(w) => w }", "duplicate Choice match arm"),
            ("match Choice::Left(x) { Choice::Left(v) => v, Choice::Right(w) => splat<2>(0_m31) }",
             "match arms must have the same type"),
            ("match x { Choice::Left(v) => v, Choice::Right(w) => w }", "match expects Choice"),
            ("match Choice::Left(splat<2>(0_m31)) { Choice::Left(v) => v, Choice::Right(w) => w }",
             "Choice::Left expects"),
            ("if std::field::is_zero(x) then Choice::Left(x) else Choice::Right(x)",
             "if result type cannot be selected"),
        )
        for body, message in cases:
            with self.subTest(body=body), self.assertRaisesRegex(SourceError, message):
                compile_text(prefix + "circuit p(private x: [m31; 1]) -> public [m31; 1] { " + body + " }")

    def test_sum_cannot_cross_circuit_boundary(self) -> None:
        with self.assertRaisesRegex(SourceError, "circuit inputs must be first-order"):
            compile_text("""enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(private value: Choice) -> public [m31; 1] { value }""")
        with self.assertRaisesRegex(SourceError, "circuit output must be"):
            compile_text("""enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(private value: [m31; 1]) -> public Choice { Choice::Left(value) }""")


if __name__ == "__main__":
    unittest.main()
