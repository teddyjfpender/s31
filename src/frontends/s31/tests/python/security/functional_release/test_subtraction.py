"""Ordered subtraction must survive independent source and Gate schedule checks."""

from __future__ import annotations

import itertools
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(S31 / "python"))

from oracle import evaluate_relation
from package.correspondence import (canonical_ir_bytes, parse_source,
                                    parse_source_optimized)
from package.direct_gate_schedule import exact_direct_gate_schedule
from text_frontend import compile_text

P = (1 << 31) - 1
EXAMPLE = S31 / "examples/functional/release_sub4"


class SubtractionCorrespondenceTests(unittest.TestCase):
    def test_function_erases_to_ordered_native_subtraction(self) -> None:
        functional = (EXAMPLE / "functional.s31").read_text()
        manual = (EXAMPLE / "manual.s31").read_text()
        checked, syntax = parse_source(functional.encode())
        direct, direct_syntax = parse_source(manual.encode())
        self.assertEqual((checked, syntax), (direct, direct_syntax))
        self.assertEqual(checked, compile_text(functional)[0])
        self.assertEqual(canonical_ir_bytes(syntax), canonical_ir_bytes(direct_syntax))
        self.assertEqual([(step["op"], step["lhs"], step["rhs"])
                          for step in syntax["instructions"]],
                         [("add", 0, 0), ("sub", 0, 1), ("sub", 2, 0)])
        gates, _, rows, source = exact_direct_gate_schedule(syntax)
        self.assertEqual(rows, 512)
        self.assertEqual([step["out"] for step in source], [23, 24, 25])
        self.assertEqual([step["op"] for step in source], ["add", "sub", "sub"])
        self.assertEqual(gates["sub"][:2], [
            {"in0": 22, "in1": 23, "out": 24},
            {"in0": 24, "in1": 22, "out": 25},
        ])
        for values in ([0, 1, 2, 7], [P - 1, P - 2, P // 2, 99]):
            claim = {"public_inputs": {"x": values}, "private_inputs": {},
                     "public_outputs": {"result": [(-2 * x) % P for x in values]}}
            self.assertEqual(evaluate_relation(checked, claim), claim["public_outputs"])

    def test_reversing_subtraction_changes_canonical_ir_and_values(self) -> None:
        source = ("circuit order(public x: [m31; 4]) -> public [m31; 4] { "
                  "let a = x + x; let result = x - a; result }")
        reversed_source = source.replace("x - a", "a - x")
        left, left_syntax = parse_source(source.encode())
        right, right_syntax = parse_source(reversed_source.encode())
        self.assertNotEqual(canonical_ir_bytes(left_syntax),
                            canonical_ir_bytes(right_syntax))
        self.assertEqual(left, compile_text(source)[0])
        self.assertEqual(right, compile_text(reversed_source)[0])
        self.assertEqual(left_syntax["instructions"][-1]["lhs"], 0)
        self.assertEqual(right_syntax["instructions"][-1]["lhs"], 1)

    def test_optimized_cse_keeps_subtraction_operand_order(self) -> None:
        source = ("circuit ordered(public x: [m31; 4]) -> public [m31; 4] { "
                  "let a = x + x; let b = x - a; let c = a - x; "
                  "let d = x - a; d }")
        checked, syntax = parse_source_optimized(source.encode())
        self.assertEqual(checked, compile_text(source)[0])
        self.assertEqual(syntax["source_to_canonical"], [0, 1, 2, 3, 2])
        self.assertEqual([(step["op"], step["lhs"], step["rhs"])
                          for step in syntax["instructions"]],
                         [("add", 0, 0), ("sub", 0, 1), ("sub", 1, 0)])
        gates, _, _, _ = exact_direct_gate_schedule(syntax)
        self.assertEqual(len(gates["sub"]), 3)  # two source gates and one constant gate

    def test_subtraction_precedence_matches_production_in_pure_helper(self) -> None:
        source = ("fn mix(a: [m31; 4], b: [m31; 4]) -> [m31; 4] { "
                  "a - a .* b }\n"
                  "circuit precedence(public x: [m31; 4]) -> public [m31; 4] { "
                  "let twice = x + x; let result = mix(x, twice); result }")
        checked, syntax = parse_source(source.encode())
        self.assertEqual(checked, compile_text(source)[0])
        self.assertEqual([step["op"] for step in syntax["instructions"]],
                         ["add", "mul", "sub"])
        for x in (0, 1, 7, P - 1):
            claim = {"public_inputs": {"x": [x] * 4}, "private_inputs": {},
                     "public_outputs": {"result": [(x - 2 * x * x) % P] * 4}}
            self.assertEqual(evaluate_relation(checked, claim), claim["public_outputs"])

    def test_helper_mixed_operator_spellings_match_production(self) -> None:
        checked = 0
        for first, second, left, middle, right in itertools.product(
                ("+", "-", ".*"), ("+", "-", ".*"),
                ("a", "b"), ("a", "b"), ("a", "b")):
            source = ("fn mix(a: [m31; 4], b: [m31; 4]) -> [m31; 4] { "
                      f"{left} {first} {middle} {second} {right} }}\n"
                      "circuit mixed(public x: [m31; 4]) -> public [m31; 4] { "
                      "let twice = x + x; let result = mix(x, twice); result }")
            relation, _ = parse_source_optimized(source.encode())
            self.assertEqual(relation, compile_text(source)[0])
            for x in (0, 7, P - 1):
                bindings = {"a": x, "b": 2 * x % P}
                values = [bindings[left], bindings[middle], bindings[right]]
                operations = [first, second]
                index = 0
                while index < len(operations):
                    if operations[index] == ".*":
                        values[index] = values[index] * values[index + 1] % P
                        values.pop(index + 1)
                        operations.pop(index)
                    else:
                        index += 1
                expected = values[0]
                for operation, value in zip(operations, values[1:], strict=True):
                    expected = (expected + value if operation == "+" else
                                expected - value) % P
                claim = {"public_inputs": {"x": [x] * 4}, "private_inputs": {},
                         "public_outputs": {"result": [expected] * 4}}
                self.assertEqual(evaluate_relation(relation, claim), claim["public_outputs"])
            checked += 1
        self.assertEqual(checked, 72)

    def test_captured_lambda_and_lexical_subtraction(self) -> None:
        source = ("circuit captured_sub(public x: [m31; 4]) -> public [m31; 4] { "
                  "let f = fun(v: [m31; 4]) -> [m31; 4] => x - v; "
                  "let twice = x + x; let result = f(twice); result }")
        checked, syntax = parse_source(source.encode())
        self.assertEqual(checked, compile_text(source)[0])
        self.assertEqual([step["op"] for step in syntax["instructions"]],
                         ["add", "sub"])
        lexical = ("circuit lexical_sub(public x: [m31; 4]) -> public [m31; 4] { "
                   "let result = let doubled = x + x in x - doubled; result }")
        checked, syntax = parse_source(lexical.encode())
        self.assertEqual(checked, compile_text(lexical)[0])
        self.assertEqual([step["op"] for step in syntax["instructions"]],
                         ["add", "sub"])

    def test_two_step_operator_dags_against_integer_oracle(self) -> None:
        names = ("x", "a", "b")
        count = 0
        for first_op, second_op, left, right, output in itertools.product(
                ("+", "-", ".*"), ("+", "-", ".*"), range(2), range(2), ("a", "b")):
            text = ("circuit scan(public x: [m31; 4]) -> public [m31; 4] { "
                    f"let a = x {first_op} x; "
                    f"let b = {names[left]} {second_op} {names[right]}; "
                    f"{output} }}")
            relation, syntax = parse_source_optimized(text.encode())
            self.assertEqual(relation, compile_text(text)[0])
            self.assertEqual(len(syntax["source_to_canonical"]), 3)
            for x in (0, 1, 2, P - 1):
                def operation(op: str, a: int, b: int) -> int:
                    return ({"+": a + b, "-": a - b, ".*": a * b}[op]) % P
                a = operation(first_op, x, x)
                b = operation(second_op, (x, a)[left], (x, a)[right])
                expected = (a if output == "a" else b)
                values = [x, x, x, x]
                claim = {"public_inputs": {"x": values}, "private_inputs": {},
                         "public_outputs": {output: [expected] * 4}}
                self.assertEqual(evaluate_relation(relation, claim), claim["public_outputs"])
            count += 1
        self.assertEqual(count, 72)


if __name__ == "__main__":
    unittest.main()
