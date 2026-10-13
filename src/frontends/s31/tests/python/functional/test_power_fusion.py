"""Composed static powers lower to a smaller, zero-safe field circuit."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from language.dead_code import prune_total_dead_nodes
from language.elaborate import Elaborator
from language.effects import TotalityChecker
from language.parser import Parser
from language.specialize import Compiler
from oracle import OracleError, evaluate_relation
from text_frontend import compile_text

P = (1 << 31) - 1
EXAMPLES = S31 / "examples/arithmetic/powers"


def unfused(source: str) -> dict:
    parser = Parser(source, "<unfused>")
    functions, circuit = parser.parse()
    Elaborator(functions, circuit, "<unfused>").check()
    TotalityChecker(functions, circuit, "<unfused>").check()
    relation, source_map = Compiler(functions, circuit, "<unfused>").compile()
    return prune_total_dead_nodes(relation, source_map)[0]


class PowerFusionTests(unittest.TestCase):
    def test_four_calls_reduce_cost_and_preserve_all_example_values(self) -> None:
        for filename, old_nodes, new_nodes, exponent in (
            ("pow65535_chain4.s31", 76, 39, 65535),
            ("pow196605_factor4.s31", 84, 47, 196605),
            ("pow196605_functional4.s31", 84, 47, 196605),
        ):
            with self.subTest(filename=filename):
                source = (EXAMPLES / filename).read_text()
                baseline = unfused(source)
                optimized, _ = compile_text(source)
                self.assertEqual(len(baseline["nodes"]), old_nodes)
                self.assertEqual(len(optimized["nodes"]), new_nodes)
                self.assertTrue(all(node["op"] == "mul" for node in optimized["nodes"]))
                assignment = json.loads((EXAMPLES / (
                    "pow65535_chain4.valid.json" if exponent == 65535
                    else "pow196605_factor4.valid.json")).read_text())
                for relation in (baseline, optimized):
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"])
                values = assignment["private_inputs"]["x"]
                self.assertEqual(assignment["public_outputs"]["result"],
                                 [pow(value, exponent**4, P) for value in values])

    def test_zero_residue_uses_p_minus_one_not_zero(self) -> None:
        source = ("circuit p(private x: [m31; 1]) -> public [m31; 1] { "
                  "let first = std::math::pow<2147483646>(x); "
                  "let result = std::math::pow<2>(first); result }")
        relation, _ = compile_text(source)
        self.assertLess(len(relation["nodes"]), len(unfused(source)["nodes"]))
        for value in (0, 1, 2, P - 1):
            expected = pow(value, 2 * (P - 1), P)
            assignment = {"public_inputs": {}, "private_inputs": {"x": [value]},
                          "public_outputs": {"result": [expected]}}
            self.assertEqual(evaluate_relation(relation, assignment),
                             assignment["public_outputs"])
            assignment["public_outputs"]["result"] = [(expected + 1) % P]
            with self.assertRaises(OracleError):
                evaluate_relation(relation, assignment)

    def test_zero_power_erases_total_argument_but_keeps_partial_argument(self) -> None:
        total = ("circuit p(private x: [m31; 1]) -> public [m31; 1] { "
                 "std::math::pow<0>(std::math::pow<15>(x)) }")
        relation, _ = compile_text(total)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["constant"])
        output = relation["public_outputs"][0]
        for value in (0, 2):
            assignment = {"public_inputs": {}, "private_inputs": {"x": [value]},
                          "public_outputs": {output: [1]}}
            self.assertEqual(evaluate_relation(relation, assignment),
                             assignment["public_outputs"])

        partial = ("circuit p(private x: [m31; 1]) -> public [m31; 1] { "
                   "std::math::pow<0>(std::math::inv(x)) }")
        relation, _ = compile_text(partial)
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         ["inv", "constant"])
        output = relation["public_outputs"][0]
        assignment = {"public_inputs": {}, "private_inputs": {"x": [2]},
                      "public_outputs": {output: [1]}}
        self.assertEqual(evaluate_relation(relation, assignment),
                         assignment["public_outputs"])
        assignment["private_inputs"]["x"] = [0]
        with self.assertRaises(OracleError):
            evaluate_relation(relation, assignment)

    def test_shared_intermediate_keeps_cheaper_unfused_graph(self) -> None:
        source = """use std@1;
struct Both { first: [m31; 1], second: [m31; 1] }
circuit both(private x: [m31; 1]) -> public Both {
    let first = std::math::pow<196605>(x);
    let second = std::math::pow<196605>(first);
    Both { first: first, second: second }
}"""
        baseline = unfused(source)
        selected, _ = compile_text(source)
        self.assertEqual(len(baseline["nodes"]), 42)
        self.assertEqual(selected, baseline)


if __name__ == "__main__":
    unittest.main()
