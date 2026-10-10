"""Nominal source records preserve types and eager effects without proof rows."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_file, compile_text


class RecordTests(unittest.TestCase):
    def test_named_fields_erase_to_identical_relation(self) -> None:
        example = S31 / "examples/arithmetic/record_square_sum.s31"
        relation, _ = compile_file(example)
        manual, _ = compile_file(example.with_name("record_square_sum_manual.s31"))
        destructured, _ = compile_file(example.with_name("record_square_sum_destructure.s31"))
        self.assertEqual(relation, manual)
        self.assertEqual(relation, destructured)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["mul", "add", "add"])
        assignment = json.loads(example.with_suffix(".valid.json").read_text())
        self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])
        assignment["public_outputs"]["result"][3] = 64
        with self.assertRaises(OracleError):
            evaluate_relation(relation, assignment)

    def test_nested_records_and_tuple_fields(self) -> None:
        source = """struct Inner { value: [m31; 1] }
struct Outer { nested: Inner, pair: ([m31; 1], [m31; 1]) }
fn make(x: [m31; 1]) -> Outer {
    Outer { pair: (x + x, x .* x), nested: Inner { value: x } }
}
fn read(p: Outer) -> [m31; 1] {
    p.nested.value + p.pair.0 + p.pair.1
}
circuit nested(private x: [m31; 1]) -> public [m31; 1] {
    let p = make(x);
    let result = read(p);
    result
}"""
        relation, _ = compile_text(source)
        assignment = {"public_inputs": {}, "private_inputs": {"x": [7]},
                      "public_outputs": {"result": [70]}}
        self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])

    def test_lambda_captures_record_without_extra_relation_nodes(self) -> None:
        source = """struct Params { bias: [m31; 1] }
fn apply(x: [m31; 1]) -> [m31; 1] {
    let params = Params { bias: x };
    let f = fun(y: [m31; 1]) -> [m31; 1] => y + params.bias;
    f(x)
}
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let result = apply(x);
    result
}"""
        relation, _ = compile_text(source)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["add"])
        self.assertEqual(evaluate_relation(relation, {
            "public_inputs": {}, "private_inputs": {"x": [7]},
            "public_outputs": {"result": [14]},
        }), {"result": [14]})

    def test_record_pattern_in_static_repeat_step(self) -> None:
        source = """struct State { value: [m31; 4] }
fn square(x: [m31; 4]) -> [m31; 4] {
    let State { value } = State { value: x .* x };
    value
}
circuit p(private x: [m31; 4]) -> public [m31; 4] {
    let result = iterate<2>(square, x);
    result
}"""
        relation, _ = compile_text(source)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["repeat"])
        self.assertEqual(relation["nodes"][0]["rounds"], 2)
        self.assertEqual(evaluate_relation(relation, {
            "public_inputs": {}, "private_inputs": {"x": [0, 1, 2, 7]},
            "public_outputs": {"result": [0, 1, 16, 2401]},
        }), {"result": [0, 1, 16, 2401]})

    def test_record_patterns_are_nominal_and_can_nest_in_tuple_patterns(self) -> None:
        prelude = """struct A { value: [m31; 1] }
struct B { value: [m31; 1] }
"""
        source = prelude + """circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let (A { value }, y) = (A { value: x }, x + x);
    let result = value + y;
    result
}"""
        relation, _ = compile_text(source)
        self.assertEqual(evaluate_relation(relation, {
            "public_inputs": {}, "private_inputs": {"x": [7]},
            "public_outputs": {"result": [21]},
        }), {"result": [21]})
        partial = """struct Powers { square: [m31; 1], doubled: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let result = let Powers { square } =
        Powers { square: x .* x, doubled: x + x } in square;
    result
}"""
        partial_relation, _ = compile_text(partial)
        self.assertEqual([node["op"] for node in partial_relation["nodes"]], ["mul", "add"])
        output_name = partial_relation["public_outputs"][0]
        self.assertEqual(evaluate_relation(partial_relation, {
            "public_inputs": {}, "private_inputs": {"x": [7]},
            "public_outputs": {output_name: [49]},
        }), {output_name: [49]})
        invalid = (
            ("let A { value } = B { value: x }; value", "struct pattern expects A"),
            ("let A { value, value } = A { value: x }; value", "duplicate A pattern field"),
            ("let A { missing } = A { value: x }; x", "unknown A pattern field"),
            ("let A {} = A { value: x }; x", "struct pattern needs at least one field"),
        )
        for body, message in invalid:
            with self.subTest(body=body), self.assertRaisesRegex(SourceError, message):
                compile_text(prelude + "circuit p(private x: [m31; 1]) -> public [m31; 1] { "
                             + body + " }")

    def test_nominal_identity_and_field_type_are_checked(self) -> None:
        prelude = """struct A { value: [m31; 1] }
struct B { value: [m31; 1] }
fn read(a: A) -> [m31; 1] { a.value }
"""
        invalid = (
            ("read(B { value: x })", "argument a expects"),
            ("A { value: (x, x) }.value", "A.value expects"),
            ("A { value: x }.missing", "A has no field missing"),
        )
        for body, message in invalid:
            with self.subTest(body=body), self.assertRaisesRegex(SourceError, message):
                compile_text(prelude + "circuit p(private x: [m31; 1]) -> public [m31; 1] { "
                             + body + " }")

    def test_constructor_shape_and_declarations_are_checked(self) -> None:
        invalid = (
            ("struct A { value: [m31; 1], value: [m31; 1] }", "duplicate struct field"),
            ("struct A {}", "struct needs at least one field"),
            ("struct A { next: B }", "expected a circuit type"),
            ("struct A { f: Fn([m31; 1]) -> [m31; 1] }", "struct fields must contain first-order"),
            ("struct UInt256 { value: [m31; 1] }", "duplicate or reserved struct type"),
        )
        for declaration, message in invalid:
            with self.subTest(declaration=declaration), self.assertRaisesRegex(SourceError, message):
                compile_text(declaration + "\ncircuit p(private x: [m31; 1]) -> public [m31; 1] { x }")
        with self.assertRaisesRegex(SourceError, "duplicate or reserved struct type A"):
            compile_text("fn A(x: [m31; 1]) -> [m31; 1] { x }\n"
                         "struct A { value: [m31; 1] }\n"
                         "circuit p(private x: [m31; 1]) -> public [m31; 1] { x }")
        fields = ", ".join(f"field{i}: [m31; 1]" for i in range(65))
        with self.assertRaisesRegex(SourceError, "struct field limit exceeded"):
            compile_text(f"struct TooMany {{ {fields} }}\n"
                         "circuit p(private x: [m31; 1]) -> public [m31; 1] { x }")
        leaf_fields = ", ".join(f"field{i}: [m31; 1]" for i in range(32))
        wide_fields = ", ".join(f"field{i}: Leaf" for i in range(33))
        with self.assertRaisesRegex(SourceError, "flattened field limit exceeded"):
            compile_text(f"struct Leaf {{ {leaf_fields} }}\n"
                         f"struct TooWide {{ {wide_fields} }}\n"
                         "circuit p(private x: [m31; 1]) -> public [m31; 1] { x }")
        constructor = "struct A { x: [m31; 1], y: [m31; 1] }\n"
        for body, message in (
            ("A { x: x }.x", "missing A fields: y"),
            ("A { x: x, y: x, y: x }.x", "duplicate A field y"),
            ("A { x: x, y: x, z: x }.x", "unknown A field z"),
        ):
            with self.subTest(body=body), self.assertRaisesRegex(SourceError, message):
                compile_text(constructor +
                             "circuit p(private x: [m31; 1]) -> public [m31; 1] { " + body + " }")

    def test_eager_fields_keep_partial_effects_visible(self) -> None:
        source = """struct Pair { kept: [m31; 1], ignored: [m31; 1] }
circuit p(public b: bit, private x: [m31; 1]) -> public [m31; 1] {
    if b then (Pair { kept: x, ignored: std::math::inv(x) }).kept else x
}"""
        with self.assertRaisesRegex(SourceError, "if branch may fail when inactive: std::math::inv"):
            compile_text(source)
        direct = """struct Pair { kept: [m31; 1], ignored: [m31; 1] }
circuit p(private x: [m31; 1]) -> public [m31; 1] {
    let pair = Pair { kept: x, ignored: std::math::inv(x) };
    pair.kept
}"""
        relation, _ = compile_text(direct)
        self.assertIn("inv", [node["op"] for node in relation["nodes"]])
        with self.assertRaisesRegex(OracleError, "division by zero"):
            evaluate_relation(relation, {"public_inputs": {}, "private_inputs": {"x": [0]},
                                         "public_outputs": {"x": [0]}})

    def test_record_inputs_remain_rejected_but_public_record_outputs_bind_names(self) -> None:
        prelude = "struct A { value: [m31; 1] }\n"
        with self.assertRaisesRegex(SourceError, "circuit inputs must be first-order values"):
            compile_text(prelude + "circuit p(private x: A) -> public [m31; 1] { x.value }")
        relation, _ = compile_text(prelude +
            "circuit p(private x: [m31; 1]) -> public A { A { value: x } }")
        self.assertEqual(relation["version"], 2)
        self.assertEqual(relation["public_outputs"], ["x"])
        self.assertEqual(relation["public_abi"]["result"]["leaves"][0]["path"],
                         [{"root": "result"}, {"field": "value"}])

    def test_repeated_result_fields_count_one_distinct_proof_word(self) -> None:
        fields = ", ".join(f"f{i}: [m31; 1]" for i in range(9))
        values = ", ".join(f"f{i}: x" for i in range(9))
        source = (f"struct Many {{ {fields} }}\n"
                  f"circuit many(private x: [m31; 1]) -> public Many {{ Many {{ {values} }} }}")
        relation, _ = compile_text(source)
        self.assertEqual(relation["public_outputs"], ["x"])
        self.assertEqual(len(relation["public_abi"]["result"]["leaves"]), 9)


if __name__ == "__main__":
    unittest.main()
