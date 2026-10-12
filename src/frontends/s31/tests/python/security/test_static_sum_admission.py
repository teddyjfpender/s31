"""Adversarial resource-admission cases for source-only enum payloads."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from language.parser import Parser
from language.syntax import SourceError
from oracle import evaluate_relation
from text_frontend import compile_text


def enum_with_payload_leaves(count: int) -> str:
    payload = "(" + ", ".join("[m31; 1]" for _ in range(count)) + ")"
    return (f"enum Huge {{ One: {payload}, Two: [m31; 1] }}\n"
            "circuit p(private x: [m31; 1]) -> public [m31; 1] { x }")


def enum_with_payload_depth(record_index: int) -> str:
    records = ["struct S0 { x: u16 }"]
    records.extend(f"struct S{index} {{ inner: S{index - 1} }}"
                   for index in range(1, record_index + 1))
    records.append(f"enum Huge {{ One: (S{record_index}, u16), Two: u16 }}")
    records.append("circuit p(private x: [m31; 1]) -> public [m31; 1] { x }")
    return "\n".join(records)


class StaticSumAdmissionTests(unittest.TestCase):
    def test_enum_payload_flattened_leaf_limit(self) -> None:
        Parser(enum_with_payload_leaves(1024), "at-limit.s31").parse()
        with self.assertRaisesRegex(SourceError, "enum payload.*limit exceeded"):
            Parser(enum_with_payload_leaves(1025), "over-limit.s31").parse()

    def test_enum_payload_layout_depth_limit(self) -> None:
        Parser(enum_with_payload_depth(29), "at-depth.s31").parse()
        with self.assertRaisesRegex(SourceError, "enum payload.*limit exceeded"):
            Parser(enum_with_payload_depth(30), "over-depth.s31").parse()

    def test_known_tag_erases_to_direct_relation(self) -> None:
        wrapped = """enum Choice { Left: [m31; 1], Right: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    match Choice::Left(x .* x) {
        Choice::Left(v) => v + v,
        Choice::Right(v) => v .* v
    }
}"""
        direct = """circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let square = x .* x;
    square + square
}"""

        def topology(source: str) -> tuple[object, ...]:
            relation, _ = compile_text(source)
            wires = {item["name"]: f"input{index}"
                     for index, item in enumerate(relation["inputs"])}
            nodes = []
            for index, node in enumerate(relation["nodes"]):
                nodes.append((node["op"], wires[node["lhs"]], wires[node["rhs"]]))
                wires[node["name"]] = f"node{index}"
            return (tuple(sorted(relation)), relation["version"], relation["name"],
                    tuple((item["kind"], item["length"], item["visibility"])
                          for item in relation["inputs"]),
                    tuple(nodes), tuple(relation["assertions"]),
                    tuple(wires[name] for name in relation["public_outputs"]))

        self.assertEqual(topology(wrapped), topology(direct))

    def test_three_variants_selects_named_arm_independent_of_arm_order(self) -> None:
        source = """enum Choice { Left: [m31; 1], Middle: [m31; 1], Right: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let out = match Choice::Middle(x .* x) {
        Choice::Right(v) => v + v,
        Choice::Middle(v) => v .* v,
        Choice::Left(v) => v + x
    };
    out
}"""
        relation, _ = compile_text(source)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["mul", "mul"])
        self.assertEqual(evaluate_relation(relation, {
            "public_inputs": {}, "private_inputs": {"x": [2]},
            "public_outputs": {"out": [16]},
        }), {"out": [16]})


if __name__ == "__main__":
    unittest.main()
