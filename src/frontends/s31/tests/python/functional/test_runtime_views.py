"""Runtime reshape/flatten semantics, liveness, and view-origin tests."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import evaluate_relation
from text_frontend import compile_text


class RuntimeViewTests(unittest.TestCase):
    def test_runtime_reshape_flatten_erases_only_complete_ordered_views(self) -> None:
        for kind, values in (("m31", [2, 3, 5, 7, 11, 13]),
                             ("u16", [2, 3, 5, 7, 11, 13])):
            with self.subTest(kind=kind):
                source = f"""use std@1;
circuit identity(private x: [{kind}; 6]) -> public [{kind}; 6] {{
    let rows = std::array::reshape<3>(x);
    std::array::flatten(rows)
}}"""
                relation, locations = compile_text(source)
                self.assertEqual(relation["nodes"], [])
                self.assertEqual(relation["public_outputs"], ["x"])
                self.assertEqual(locations, {})
                assigned = {"public_inputs": {}, "private_inputs": {"x": values},
                            "public_outputs": {"x": values}}
                self.assertEqual(evaluate_relation(relation, assigned), {"x": values})

        for rows in range(1, 17):
            with self.subTest(rows=rows):
                length = 2 * rows
                relation, _ = compile_text(f"""use std@1;
circuit coverage(private x: [m31; {length}]) -> public [m31; 1] {{
    let matrix = std::array::reshape<{rows}>(x);
    let flat = std::array::flatten(matrix);
    std::array::get<{length - 1}>(flat)
}}""")
                self.assertEqual([node["op"] for node in relation["nodes"]],
                                 ["array_get"])
                self.assertEqual(relation["nodes"][0]["lhs"], "x")
                inputs = list(range(length))
                output = relation["public_outputs"][0]
                self.assertEqual(evaluate_relation(relation, {
                    "public_inputs": {}, "private_inputs": {"x": inputs},
                    "public_outputs": {output: [length - 1]},
                }), {output: [length - 1]})

        # The row order and full interval are semantic conditions. A changed
        # order, a duplicate, or missing final row must retain real relation
        # nodes that the native circuit will constrain.
        variants = (
            ("reordered", "[std::array::get<1>(rows), std::array::get<0>(rows), std::array::get<2>(rows)]",
             [5, 7, 2, 3, 11, 13], 3),
            ("duplicated", "[std::array::get<0>(rows), std::array::get<0>(rows), std::array::get<2>(rows)]",
             [2, 3, 2, 3, 11, 13], 2),
            ("partial", "[std::array::get<0>(rows), std::array::get<1>(rows)]",
             [2, 3, 5, 7], 2),
        )
        values = [2, 3, 5, 7, 11, 13]
        for label, rows, expected, unique_rows in variants:
            with self.subTest(label=label):
                source = f"""use std@1;
circuit {label}(private x: [m31; 6]) -> public [m31; {len(expected)}] {{
    let rows = std::array::reshape<3>(x);
    std::array::flatten({rows})
}}"""
                relation, _ = compile_text(source)
                operations = [node["op"] for node in relation["nodes"]]
                self.assertEqual(operations.count("array_slice"), unique_rows)
                self.assertEqual(operations.count("array_concat"), len(expected[::2]) - 1)
                self.assertEqual(len(operations), unique_rows + len(expected[::2]) - 1)
                output = relation["public_outputs"][0]
                self.assertEqual(evaluate_relation(relation, {
                    "public_inputs": {}, "private_inputs": {"x": values},
                    "public_outputs": {output: expected},
                }), {output: expected})

        # A separately consumed row is materialized even when another use
        # flattens the complete matrix back to x.
        retained, _ = compile_text("""use std@1;
circuit retained(private x: [m31; 6]) -> public [m31; 4] {
    let rows = std::array::reshape<3>(x);
    let head = std::array::get<0>(rows);
    let flat = std::array::flatten(rows);
    std::array::concat(head, std::array::take<2>(flat))
}""")
        self.assertEqual([node["op"] for node in retained["nodes"]],
                         ["array_slice", "array_slice", "array_concat"])

        # One shifted row used twice must share the same constrained slice.
        # Lazy realization may erase work, but cannot duplicate it.
        shared, _ = compile_text("""use std@1;
circuit shared(private x: [m31; 6]) -> public [m31; 4] {
    let rows = std::array::reshape<3>(x);
    let middle = std::array::get<1>(rows);
    std::array::concat(middle, middle)
}""")
        self.assertEqual([node["op"] for node in shared["nodes"]],
                         ["array_slice", "array_concat"])
        self.assertEqual(evaluate_relation(shared, {
            "public_inputs": {}, "private_inputs": {"x": values},
            "public_outputs": {shared["public_outputs"][0]: [5, 7, 5, 7]},
        }), {shared["public_outputs"][0]: [5, 7, 5, 7]})

        # Equal shapes and complementary offsets do not justify an alias
        # when the rows came from different witness arrays.
        crossed, _ = compile_text("""use std@1;
circuit crossed(private x: [m31; 4], private y: [m31; 4]) -> public [m31; 4] {
    let left = std::array::reshape<2>(x);
    let right = std::array::reshape<2>(y);
    std::array::flatten([std::array::get<0>(left), std::array::get<1>(right)])
}""")
        self.assertEqual([node["op"] for node in crossed["nodes"]],
                         ["array_slice", "array_slice", "array_concat"])
        crossed_output = crossed["public_outputs"][0]
        self.assertEqual(evaluate_relation(crossed, {
            "public_inputs": {}, "private_inputs": {"x": [2, 3, 5, 7],
                                                      "y": [11, 13, 17, 19]},
            "public_outputs": {crossed_output: [2, 3, 17, 19]},
        }), {crossed_output: [2, 3, 17, 19]})

        # The first intermediate use owns one row wire. Returning that row
        # later aliases the same wire, and its source map points back to the
        # reshape that created it rather than losing its origin span.
        late_source = """use std@1;
circuit late_named(private x: [m31; 6]) -> public [m31; 2] {
    let rows = std::array::reshape<3>(x);
    let middle = std::array::get<1>(rows);
    let prefix = std::array::take<1>(middle);
    middle
}"""
        late, locations = compile_text(late_source)
        self.assertEqual([node["op"] for node in late["nodes"]],
                         ["array_slice", "array_slice"])
        self.assertEqual(late["public_outputs"], [late["nodes"][0]["name"]])
        self.assertEqual(locations[late["nodes"][0]["name"]]["line"], 3)
        self.assertEqual(evaluate_relation(late, {
            "public_inputs": {}, "private_inputs": {"x": values},
            "public_outputs": {late["public_outputs"][0]: [5, 7]},
        }), {late["public_outputs"][0]: [5, 7]})

        # A reshape of an already lazy row remains a view of that row. The
        # complete inner flatten returns it, and the outer slice is realized
        # once when the final lane is selected.
        nested, nested_locations = compile_text("""use std@1;
circuit nested(private x: [m31; 8]) -> public [m31; 1] {
    let rows = std::array::reshape<2>(x);
    let row = std::array::get<1>(rows);
    let sub = std::array::reshape<2>(row);
    let flat = std::array::flatten(sub);
    std::array::get<2>(flat)
}""")
        self.assertEqual([node["op"] for node in nested["nodes"]],
                         ["array_slice", "array_get"])
        self.assertEqual(nested["nodes"][0]["index"], 4)
        self.assertEqual(nested_locations[nested["nodes"][0]["name"]]["line"], 3)
        nested_output = nested["public_outputs"][0]
        self.assertEqual(evaluate_relation(nested, {
            "public_inputs": {}, "private_inputs": {"x": [2, 3, 5, 7, 11, 13, 17, 19]},
            "public_outputs": {nested_output: [17]},
        }), {nested_output: [17]})

        # A forged internal view outside its source cannot be mistaken for a
        # full interval; realizing it still performs the bounds check.
        from library.stdlib import Builder, SliceView, StaticGroup, Type, Value
        builder = Builder("invalid_view")
        source = builder.input("x", Type("m31", 4), "private")
        invalid = Value(Type("m31", 2), slice_view=SliceView(source, 4, 2))
        with self.assertRaisesRegex(ValueError, "inside the array"):
            builder.array_flatten(StaticGroup((invalid, invalid)))
