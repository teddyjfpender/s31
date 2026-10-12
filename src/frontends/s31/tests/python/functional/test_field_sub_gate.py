"""Field subtraction lowers to a single native arithmetic operation."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import compile_text


P = (1 << 31) - 1
HEADER = "circuit p(private a: [m31; 4], private b: [m31; 4]) -> public [m31; 4] { "


class FieldSubGateTests(unittest.TestCase):
    def test_named_function_erases_to_the_same_subtraction_relation(self) -> None:
        direct, _ = compile_text(HEADER + "let out = a - b; out }")
        wrapped, _ = compile_text(
            "fn difference(x: [m31; 4], y: [m31; 4]) -> [m31; 4] { x - y }\n" +
            HEADER + "let out = difference(a, b); out }")
        self.assertEqual(wrapped, direct)
        self.assertEqual([node["op"] for node in wrapped["nodes"]], ["sub"])

    def test_dynamic_sub_is_one_relation_node_and_matches_modular_oracle(self) -> None:
        relation, _ = compile_text(HEADER + "a - b }")
        self.assertEqual(relation["nodes"], [{"name": "_s31_0", "op": "sub",
                                               "lhs": "a", "rhs": "b"}])
        left = [0, 1, P - 1, 7]
        right = [1, P - 1, P - 1, 11]
        expected = [(a - b) % P for a, b in zip(left, right)]
        assignment = {"public_inputs": {}, "private_inputs": {"a": left, "b": right},
                      "public_outputs": {"_s31_0": expected}}
        self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])
        wrong = {**assignment, "public_outputs": {"_s31_0": left}}
        with self.assertRaises(OracleError):
            evaluate_relation(relation, wrong)

    def test_functional_subtraction_is_zero_cost_across_packed_boundaries(self) -> None:
        for length in (1, 2, 3, 5, 7, 8):
            with self.subTest(length=length):
                header = (f"circuit p(private a: [m31; {length}], "
                          f"private b: [m31; {length}]) -> public [m31; {length}] {{ ")
                direct, _ = compile_text(header + "let out = a - b; out }")
                helper, _ = compile_text(
                    f"fn difference(x: [m31; {length}], y: [m31; {length}]) "
                    f"-> [m31; {length}] {{ x - y }}\n" +
                    header + "let out = difference(a, b); out }")
                self.assertEqual(helper, direct)
                self.assertEqual([node["op"] for node in direct["nodes"]], ["sub"])
                left = [0, 1, P - 1, 7, 123456789, P - 2, 42, 0][:length]
                right = [1, P - 1, P - 1, 11, 9876, 3, P - 1, 0][:length]
                expected = [(a - b) % P for a, b in zip(left, right)]
                assignment = {"public_inputs": {}, "private_inputs": {"a": left, "b": right},
                              "public_outputs": {"out": expected}}
                self.assertEqual(evaluate_relation(direct, assignment), assignment["public_outputs"])
                wrong = expected.copy()
                wrong[-1] = (wrong[-1] + 1) % P
                assignment["public_outputs"] = {"out": wrong}
                with self.assertRaises(OracleError):
                    evaluate_relation(direct, assignment)

    def test_constant_right_preserves_one_add_const_node(self) -> None:
        relation, _ = compile_text(HEADER + "a - splat<4>(7_m31) }")
        self.assertEqual(relation["nodes"], [{"name": "_s31_0", "op": "add_const",
                                               "lhs": "a", "constant": P - 7}])

    def test_constant_left_is_not_commuted(self) -> None:
        relation, _ = compile_text(HEADER + "splat<4>(7_m31) - b }")
        self.assertEqual([node["op"] for node in relation["nodes"]], ["constant", "sub"])
        assignment = {"public_inputs": {}, "private_inputs": {"a": [0] * 4, "b": [8, 7, 0, P - 1]},
                      "public_outputs": {relation["public_outputs"][0]: [P - 1, 0, 7, 8]}}
        self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])

    def test_constant_subtraction_folds(self) -> None:
        relation, _ = compile_text(HEADER + "splat<4>(2_m31) - splat<4>(7_m31) }")
        self.assertEqual(relation["nodes"], [{"name": "_s31_0", "op": "constant",
                                               "constant": P - 5, "length": 4}])


if __name__ == "__main__":
    unittest.main()
