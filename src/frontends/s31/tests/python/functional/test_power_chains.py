"""Static power schedules preserve field meaning and never add multiplications."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from library.addition_chains import binary_chain, exponent_chain
from oracle import OracleError, evaluate_relation
from text_frontend import compile_text

P = (1 << 31) - 1


def graph(relation: dict) -> list[tuple[str, int, int]]:
    """Operation order and sharing, independent of readable source names."""
    references = {item["name"]: index for index, item in enumerate(relation["inputs"])}
    result = []
    for node in relation["nodes"]:
        result.append((node["op"], references[node["lhs"]], references[node["rhs"]]))
        references[node["name"]] = len(references)
    return result


class PowerChainTests(unittest.TestCase):
    def test_every_short_chain_has_valid_parents_and_no_cost_regression(self) -> None:
        for exponent in range(1, 256):
            with self.subTest(exponent=exponent):
                chain = exponent_chain(exponent)
                self.assertEqual((chain[0], chain[-1]), (1, exponent))
                self.assertLessEqual(len(chain), len(binary_chain(exponent)))
                for index, next_power in enumerate(chain[1:], 1):
                    self.assertGreater(next_power, chain[index - 1])
                    self.assertIn(next_power - chain[index - 1], chain[:index])
        self.assertEqual({n: len(exponent_chain(n)) - 1 for n in (15, 31, 63, 255)},
                         {15: 5, 31: 7, 63: 8, 255: 10})
        self.assertEqual(exponent_chain(256), binary_chain(256))

    def test_pow15_matches_handwritten_five_gate_graph(self) -> None:
        optimized = """circuit p(private x: [m31; 1]) -> public [m31; 1] {
            let result = std::math::pow<15>(x); result
        }"""
        handwritten = """circuit p(private x: [m31; 1]) -> public [m31; 1] {
            let x2 = x .* x;
            let x4 = x2 .* x2;
            let x5 = x4 .* x;
            let x10 = x5 .* x5;
            let result = x10 .* x5;
            result
        }"""
        binary = """circuit p(private x: [m31; 1]) -> public [m31; 1] {
            let x2 = x .* x;
            let x3 = x2 .* x;
            let x6 = x3 .* x3;
            let x7 = x6 .* x;
            let x14 = x7 .* x7;
            let result = x14 .* x;
            result
        }"""
        produced, _ = compile_text(optimized)
        manual, _ = compile_text(handwritten)
        old, _ = compile_text(binary)
        self.assertEqual(graph(produced), graph(manual))
        self.assertEqual(len(produced["nodes"]), 5)
        self.assertEqual(len(old["nodes"]), 6)
        self.assertTrue(all(node["op"] == "mul" for node in produced["nodes"]))

    def test_power_values_and_false_claims(self) -> None:
        for exponent in (0, 1, 2, 3, 5, 7, 15, 31, 63, 127, 255, 256, P - 2):
            with self.subTest(exponent=exponent):
                relation, _ = compile_text(
                    f"circuit p(private x: [m31; 1]) -> public [m31; 1] "
                    f"{{ std::math::pow<{exponent}>(x) }}")
                output = relation["public_outputs"][0]
                for value in (0, 1, 2, P - 1, 1_234_567):
                    expected = pow(value, exponent, P)
                    assignment = {"public_inputs": {}, "private_inputs": {"x": [value]},
                                  "public_outputs": {output: [expected]}}
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"])
                    assignment["public_outputs"][output] = [(expected + 1) % P]
                    with self.assertRaises(OracleError):
                        evaluate_relation(relation, assignment)


if __name__ == "__main__":
    unittest.main()
