"""Unused total enum work may erase without discarding source obligations."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from abi.binding_v2 import validate_binding
from language.dead_code import prune_total_dead_nodes
from oracle import OracleError, evaluate_relation
from package.correspondence import parse_source
from text_frontend import compile_text


class StaticSumDeadCodeTests(unittest.TestCase):
    def test_ignored_total_payload_matches_direct_graph(self) -> None:
        wrapped = """enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let out = match Choice::Left(x .* x + x) {
        Choice::Left(ignored) => x + x,
        Choice::Right(other) => other
    };
    out
}"""
        direct = """circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let out = x + x;
    out
}"""
        relation, source_map = compile_text(wrapped)
        direct_relation, _ = compile_text(direct)
        self.assertEqual(relation, direct_relation)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["add"])
        self.assertEqual(set(source_map), {node["name"] for node in relation["nodes"]})
        assignment = {"public_inputs": {}, "private_inputs": {"x": [7]},
                      "public_outputs": {"out": [14]}}
        self.assertEqual(evaluate_relation(relation, assignment), {"out": [14]})

    def test_ignored_subtraction_payload_matches_direct_graph(self) -> None:
        wrapped = """enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let ignored = Choice::Left(x - x);
    let out = x + x;
    out
}"""
        direct = """circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let out = x + x;
    out
}"""
        relation, _ = compile_text(wrapped)
        direct_relation, _ = compile_text(direct)
        self.assertEqual(relation, direct_relation)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["add"])
        for value in (0, 1, 2**31 - 2):
            expected = (2 * value) % (2**31 - 1)
            assignment = {"public_inputs": {}, "private_inputs": {"x": [value]},
                          "public_outputs": {"out": [expected]}}
            self.assertEqual(evaluate_relation(relation, assignment), {"out": [expected]})

    def test_ignored_partial_payload_still_fails_at_zero(self) -> None:
        source = """enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let ignored = Choice::Left(std::math::inv(x));
    x
}"""
        relation, source_map = compile_text(source)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["inv"])
        self.assertEqual(set(source_map), {node["name"] for node in relation["nodes"]})
        with self.assertRaisesRegex(OracleError, "division by zero"):
            evaluate_relation(relation, {"public_inputs": {}, "private_inputs": {"x": [0]},
                                         "public_outputs": {"x": [0]}})

    def test_assertion_keeps_dependencies_while_unrelated_payload_erases(self) -> None:
        source = """enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let ignored = Choice::Left(x .* x);
    assert_eq(x + x, x);
    x
}"""
        relation, _ = compile_text(source)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["add"])
        self.assertEqual(len(relation["assertions"]), 1)
        self.assertEqual(relation["assertions"][0]["lhs"], relation["nodes"][0]["name"])
        evaluate_relation(relation, {"public_inputs": {}, "private_inputs": {"x": [0]},
                                     "public_outputs": {"x": [0]}})
        with self.assertRaises(OracleError):
            evaluate_relation(relation, {"public_inputs": {}, "private_inputs": {"x": [1]},
                                         "public_outputs": {"x": [1]}})

    def test_public_record_binding_survives_dead_payload_pruning(self) -> None:
        wrapped = """struct Box { value: [m31; 1] }
enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(public box: Box) -> public Box {
    let ignored = Choice::Left(box.value .* box.value);
    box
}"""
        direct = """struct Box { value: [m31; 1] }
circuit p(public box: Box) -> public Box { box }"""
        relation, source_map = compile_text(wrapped)
        direct_relation, _ = compile_text(direct)
        self.assertEqual(relation, direct_relation)
        self.assertEqual(relation["nodes"], [])
        self.assertEqual(source_map, {})
        base = {**relation, "version": 1}
        binding = base.pop("public_abi")
        validate_binding(base, binding)

    def test_dead_payload_does_not_block_one_node_chip_shape(self) -> None:
        prefix = """enum Choice { Left: [m31; 4], Right: [m31; 4] }
fn step(v: [m31; 4]) -> [m31; 4] { v .* v + splat<4>(7_m31) }
"""
        wrapped = prefix + """circuit p(public x: [m31; 4]) -> public [m31; 4] {
    let ignored = Choice::Left(x .* x);
    let result = iterate<16>(step, x);
    result
}"""
        direct = prefix + """circuit p(public x: [m31; 4]) -> public [m31; 4] {
    let result = iterate<16>(step, x);
    result
}"""
        relation, _ = compile_text(wrapped)
        direct_relation, _ = compile_text(direct)
        self.assertEqual(relation, direct_relation)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["repeat"])

    def test_live_selector_retains_its_total_ancestor(self) -> None:
        source = """enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let ignored = Choice::Left(x .* x);
    let bit = std::field::is_zero(x + x);
    let result = select(bit, x, x);
    result
}"""
        relation, _ = compile_text(source)
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         ["add", "is_zero", "select"])
        self.assertEqual(relation["nodes"][1]["lhs"], relation["nodes"][0]["name"])
        self.assertEqual(relation["nodes"][2]["selector"], relation["nodes"][1]["name"])

    def test_bounded_correspondence_fragment_remains_unchanged(self) -> None:
        source = """circuit p(public x: [m31; 4]) -> public [m31; 4] {
    let dead = x .* x;
    let result = x + x;
    result
}"""
        relation, _ = compile_text(source)
        independently_checked, _ = parse_source(source.encode())
        self.assertEqual(relation, independently_checked)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["mul", "add"])

    def test_unknown_node_metadata_fails_closed(self) -> None:
        source = """circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let dead = x .* x;
    let out = x + x;
    out
}"""
        relation, source_map = compile_text(source)
        relation["nodes"][1]["future_wire"] = "dead"
        pruned, locations = prune_total_dead_nodes(relation, source_map)
        self.assertIs(pruned, relation)
        self.assertIs(locations, source_map)
        self.assertEqual([node["op"] for node in pruned["nodes"]], ["mul", "add"])


if __name__ == "__main__":
    unittest.main()
