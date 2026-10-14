"""Static higher-order map erases to the same relation as explicit calls."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_text


class StaticMapTests(unittest.TestCase):
    def test_named_map_has_exact_direct_relation_and_independent_values(self) -> None:
        header = "fn square(v: [m31; 4]) -> [m31; 4] { v .* v }\n"
        circuit = """circuit p(private x: [m31; 4], private y: [m31; 4])
            -> public [m31; 8] { let out = BODY; out }"""
        mapped, _ = compile_text(header + circuit.replace(
            "BODY", "std::array::flatten(std::array::map(square, [x, y]))"))
        direct, _ = compile_text(header + circuit.replace(
            "BODY", "std::array::flatten([square(x), square(y)])"))
        self.assertEqual(mapped, direct)
        self.assertEqual([node["op"] for node in mapped["nodes"]],
                         ["mul", "mul", "array_concat"])
        assignment = {
            "public_inputs": {},
            "private_inputs": {"x": [0, 1, 2, 7], "y": [3, 4, 5, 6]},
            "public_outputs": {"out": [0, 1, 4, 49, 9, 16, 25, 36]},
        }
        self.assertEqual(evaluate_relation(mapped, assignment), assignment["public_outputs"])
        assignment["public_outputs"]["out"][7] += 1
        with self.assertRaises(OracleError):
            evaluate_relation(mapped, assignment)

    def test_captured_closure_map_erases_to_direct_arithmetic(self) -> None:
        header = """fn offset(c: [m31; 4]) -> Fn([m31; 4]) -> [m31; 4] {
            fun(v: [m31; 4]) -> [m31; 4] => v + c
        }
"""
        circuit = """circuit p(private x: [m31; 4], private y: [m31; 4],
            private c: [m31; 4]) -> public [m31; 8] {
            let out = BODY;
            out
        }"""
        mapped, _ = compile_text(header + circuit.replace(
            "BODY", "std::array::flatten(std::array::map(offset(c), [x, y]))"))
        direct, _ = compile_text(circuit.replace(
            "BODY", "std::array::flatten([x + c, y + c])"))
        self.assertEqual(mapped, direct)
        self.assertEqual([node["op"] for node in mapped["nodes"]],
                         ["add", "add", "array_concat"])

    def test_generated_lengths_preserve_explicit_calls(self) -> None:
        prelude = "fn step(v: [m31; 1]) -> [m31; 1] { v .* v + splat<1>(7_m31) }\n"
        for count in range(1, 9):
            with self.subTest(count=count):
                names = [f"a{index}" for index in range(count)]
                params = ", ".join(f"private {name}: [m31; 1]" for name in names)
                static_array = ", ".join(names)
                direct_calls = ", ".join(f"step({name})" for name in names)
                frame = (f"circuit p({params}) -> public [m31; {count}] "
                         "{ let out = std::array::flatten(BODY); out }")
                mapped, _ = compile_text(prelude + frame.replace(
                    "BODY", f"std::array::map(step, [{static_array}])"))
                direct, _ = compile_text(prelude + frame.replace(
                    "BODY", f"[{direct_calls}]"))
                self.assertEqual(mapped, direct)
                words = {name: [(index * 3 + 2) % ((1 << 31) - 1)]
                         for index, name in enumerate(names)}
                expected = [(value[0] * value[0] + 7) % ((1 << 31) - 1)
                            for value in words.values()]
                assignment = {"public_inputs": {}, "private_inputs": words,
                              "public_outputs": {mapped["public_outputs"][0]: expected}}
                self.assertEqual(evaluate_relation(mapped, assignment),
                                 assignment["public_outputs"])

    def test_partial_mapped_function_is_rejected_in_inactive_if_arm(self) -> None:
        source = """fn risky(v: [m31; 1]) -> [m31; 1] { std::math::inv(v) }
circuit p(public flag: bit, private x: [m31; 1]) -> public [m31; 1] {
    let out = if flag then std::array::get<0>(std::array::map(risky, [x])) else x;
    out
}"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(source)

    def test_map_checks_shape_and_function_type_before_emission(self) -> None:
        header = "fn square(v: [m31; 4]) -> [m31; 4] { v .* v }\n"
        body = """circuit p(private x: [m31; 4]) -> public [m31; 4] {
            let unused = BODY;
            x
        }"""
        for expression, message in (
            ("std::array::map(square, x)", "requires a static array"),
            ("std::array::map(square, [x, splat<3>(1_m31)])", "matching its function"),
            ("std::array::map<2>(square, [x])", "does not accept a static parameter"),
            ("std::array::map(square, [" + ", ".join(["x"] * 65) + "])", "1..64 terms"),
        ):
            with self.subTest(expression=expression), self.assertRaisesRegex(SourceError, message):
                compile_text(header + body.replace("BODY", expression))


if __name__ == "__main__":
    unittest.main()
