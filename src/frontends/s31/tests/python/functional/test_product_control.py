"""Source products select and assert only through their first-order leaves."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from abi.binding_v2 import flat_assignment_from_typed
from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_file, compile_text


class ProductControlTests(unittest.TestCase):
    def test_nested_record_selection_has_exact_fieldwise_relation(self) -> None:
        example = S31 / "examples/control/record_choice.s31"
        product, _ = compile_file(example)
        fieldwise, _ = compile_file(example.with_name("record_choice_manual.s31"))
        self.assertEqual(product, fieldwise)
        self.assertEqual(product["version"], 2)
        self.assertEqual([node["op"] for node in product["nodes"]],
                         ["is_zero", "add", "add", "select", "select", "select"])
        semantic = {**product, "version": 1}
        semantic.pop("public_abi")
        fixture = example.with_suffix(".valid.json")
        for x, y, outputs in ((0, 7, (0, 0, 7)), (3, 7, (14, 7, 3))):
            typed = json.loads(fixture.read_text())
            typed["private_inputs"] = {"x": [x], "y": [y]}
            typed["result"] = {"first": [outputs[0]],
                               "nested": [[outputs[1]], [outputs[2]]]}
            assignment = flat_assignment_from_typed(product, json.dumps(typed).encode())
            self.assertEqual(evaluate_relation(semantic, assignment), assignment["public_outputs"])
            first = product["public_outputs"][0]
            assignment["public_outputs"][first][0] += 1
            with self.assertRaises(OracleError):
                evaluate_relation(semantic, assignment)

    def test_record_assertion_has_exact_leafwise_relation(self) -> None:
        common = """struct Pair { first: [m31; 1], nested: ([m31; 1], [m31; 1]) }
circuit eq(private x: [m31; 1], private y: [m31; 1]) -> public [m31; 1] {
    let a = Pair { first: x, nested: (y, x) };
    let c = Pair { first: y, nested: (x, y) };
"""
        product, _ = compile_text(common + "assert_eq(a, c); x }")
        fieldwise, _ = compile_text(common + """assert_eq(a.first, c.first);
    assert_eq(a.nested.0, c.nested.0);
    assert_eq(a.nested.1, c.nested.1);
    x }""")
        self.assertEqual(product, fieldwise)
        self.assertEqual(len(product["assertions"]), 3)
        self.assertEqual(evaluate_relation(product, {
            "public_inputs": {}, "private_inputs": {"x": [7], "y": [7]},
            "public_outputs": {"x": [7]},
        }), {"x": [7]})
        with self.assertRaises(OracleError):
            evaluate_relation(product, {
                "public_inputs": {}, "private_inputs": {"x": [7], "y": [8]},
                "public_outputs": {"x": [7]},
            })

    def test_tuple_bit_leaf_and_projection_keep_eager_selection(self) -> None:
        common = """circuit pick(public b: bit, private x: [m31; 1],
    private y: [m31; 1]) -> public [m31; 1] {
"""
        product, _ = compile_text(common +
                                  "let pair = if b then (x, b) else (y, b); pair.0 }")
        fieldwise, _ = compile_text(common +
                                    "let pair = (if b then x else y, if b then b else b); pair.0 }")
        self.assertEqual(product, fieldwise)
        self.assertEqual([node["op"] for node in product["nodes"]],
                         ["select", "bool_select"])

    def test_product_control_rejects_partial_and_static_function_leaves(self) -> None:
        record = """struct Pair { first: [m31; 1], second: [m31; 1] }
circuit pick(public b: bit, private x: [m31; 1]) -> public [m31; 1] {
    let pair = if b then Pair { first: x, second: std::math::inv(x) }
                    else Pair { first: x, second: x };
    pair.first
}"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(record)
        function_leaf = """fn id(x: [m31; 1]) -> [m31; 1] { x }
circuit pick(public b: bit, private x: [m31; 1]) -> public [m31; 1] {
    let pair = if b then (id, x) else (id, x);
    pair.1
}"""
        with self.assertRaisesRegex(SourceError, "result type cannot be selected"):
            compile_text(function_leaf)

    def test_nominal_record_assertion_rejects_equal_shapes(self) -> None:
        source = """struct A { value: [m31; 1] }
struct B { value: [m31; 1] }
circuit eq(private x: [m31; 1]) -> public [m31; 1] {
    assert_eq(A { value: x }, B { value: x });
    x
}"""
        with self.assertRaisesRegex(SourceError, "assert_eq requires matching"):
            compile_text(source)


if __name__ == "__main__":
    unittest.main()
