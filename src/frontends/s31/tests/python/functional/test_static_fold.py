"""A bounded higher-order left fold has exactly the explicit-call relation."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_text


P = (1 << 31) - 1
STEP = """fn horner_step(x: [m31; 4]) -> Fn([m31; 4], [m31; 4]) -> [m31; 4] {
    fun(acc: [m31; 4], coeff: [m31; 4]) -> [m31; 4] => acc .* x + coeff
}
"""
FRAME = """circuit horner(private x: [m31; 4], private a: [m31; 4],
    private b: [m31; 4], private c: [m31; 4]) -> public [m31; 4] {
    let step = horner_step(x);
    let zero = splat<4>(0_m31);
    let out = BODY;
    out
}"


class StaticFoldTests(unittest.TestCase):
    def test_captured_fold_has_exact_explicit_relation_and_values(self) -> None:
        folded, _ = compile_text(STEP + FRAME.replace(
            "BODY", "std::array::fold(step, zero, [a, b, c])"))
        explicit, _ = compile_text(STEP + FRAME.replace(
            "BODY", "step(step(step(zero, a), b), c)"))
        self.assertEqual(folded, explicit)
        self.assertEqual([node["op"] for node in folded["nodes"]],
                         ["mul", "add", "mul", "add", "mul", "add"])
        assignment = {
            "public_inputs": {},
            "private_inputs": {
                "x": [0, 1, 2, 7], "a": [1, 2, 3, 4],
                "b": [5, 6, 7, 8], "c": [9, 10, 11, 12],
            },
            "public_outputs": {"out": [9, 18, 37, 264]},
        }
        expected = [((a * x + b) * x + c) % P for x, a, b, c in zip(
            assignment["private_inputs"]["x"], assignment["private_inputs"]["a"],
            assignment["private_inputs"]["b"], assignment["private_inputs"]["c"])]
        self.assertEqual(assignment["public_outputs"]["out"], expected)
        self.assertEqual(evaluate_relation(folded, assignment), assignment["public_outputs"])
        assignment["public_outputs"]["out"][3] += 1
        with self.assertRaises(OracleError):
            evaluate_relation(folded, assignment)

    def test_generated_lengths_preserve_explicit_call_order(self) -> None:
        step = "fn advance(acc: [m31; 1], item: [m31; 1]) -> [m31; 1] { acc .* item + item }\n"
        for count in range(1, 9):
            with self.subTest(count=count):
                names = [f"a{index}" for index in range(count)]
                params = ", ".join(f"private {name}: [m31; 1]" for name in names)
                frame = (f"circuit p({params}) -> public [m31; 1] "
                         "{ let seed = splat<1>(3_m31); let out = BODY; out }")
                folded, _ = compile_text(step + frame.replace(
                    "BODY", f"std::array::fold(advance, seed, [{', '.join(names)}])"))
                direct = "seed"
                for name in names:
                    direct = f"advance({direct}, {name})"
                explicit, _ = compile_text(step + frame.replace("BODY", direct))
                self.assertEqual(folded, explicit)
                values = {name: [index + 2] for index, name in enumerate(names)}
                answer = 3
                for item in values.values():
                    answer = (answer * item[0] + item[0]) % P
                assignment = {"public_inputs": {}, "private_inputs": values,
                              "public_outputs": {"out": [answer]}}
                self.assertEqual(evaluate_relation(folded, assignment),
                                 assignment["public_outputs"])

    def test_fold_checks_static_shape_and_function_type(self) -> None:
        step = "fn add(acc: [m31; 1], item: [m31; 1]) -> [m31; 1] { acc + item }\n"
        frame = "circuit p(private x: [m31; 1]) -> public [m31; 1] { let ignored = BODY; x }"
        for expression, error in (
            ("std::array::fold(add, x, x)", "requires a static array"),
            ("std::array::fold(add, x, [x, splat<2>(1_m31)])", "matching its function"),
            ("std::array::fold<2>(add, x, [x])", "does not accept a static parameter"),
            ("std::array::fold(add, x, [" + ", ".join(["x"] * 65) + "])", "1..64 terms"),
            ("std::array::fold(add, x, [])", "1..64 terms"),
            ("std::array::fold(add, [x], [x])", "expected a circuit value"),
        ):
            with self.subTest(expression=expression), self.assertRaisesRegex(SourceError, error):
                compile_text(step + frame.replace("BODY", expression))


if __name__ == "__main__":
    unittest.main()
