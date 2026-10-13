"""Nested product binders erase to typed projections of one source value."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import SourceError, compile_file, compile_text


class NestedRecordPatternTests(unittest.TestCase):
    def test_nested_parameter_has_exact_direct_relation(self) -> None:
        examples = S31 / "examples/functional/nested_record_patterns"
        relation, _ = compile_file(examples / "nested.s31")
        direct, _ = compile_file(examples / "direct.s31")
        self.assertEqual(relation, direct)
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         ["mul", "add", "add"])
        for x, y in ((0, 0), (3, 5), (7, 11), (2_147_483_646, 1)):
            with self.subTest(x=x, y=y):
                output = (x * y + x + y) % 2_147_483_647
                assignment = {"public_inputs": {"x": [x], "y": [y]},
                              "private_inputs": {}, "public_outputs": {"result": [output]}}
                self.assertEqual(evaluate_relation(relation, assignment),
                                 assignment["public_outputs"])
                assignment["public_outputs"]["result"] = [(output + 1) % 2_147_483_647]
                with self.assertRaises(OracleError):
                    evaluate_relation(relation, assignment)

    def test_nested_let_and_lambda_preserve_single_eager_evaluation(self) -> None:
        source = """struct Inner { value: [m31; 1], ignored: [m31; 1] }
struct Outer { inner: Inner, pair: ([m31; 1], [m31; 1]) }
circuit p(public x: [m31; 1]) -> public [m31; 1] {
    let f = fun(Outer { inner: Inner { value: a }, pair: (b, c) }: Outer)
        -> [m31; 1] => a + b + c;
    let result = f(Outer { inner: Inner { value: x, ignored: x .* x },
                           pair: (x + x, x) });
    result
}"""
        relation, _ = compile_text(source)
        # The unbound field is still evaluated. Pattern projections themselves
        # add no nodes and do not evaluate any component a second time.
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         ["mul", "add", "add", "add"])
        self.assertEqual(evaluate_relation(relation, {
            "public_inputs": {"x": [7]}, "private_inputs": {},
            "public_outputs": {"result": [28]},
        }), {"result": [28]})
        expression_let = """struct Inner { value: [m31; 1] }
struct Outer { inner: Inner }
circuit p(public x: [m31; 1]) -> public [m31; 1] {
    let result = let Outer { inner: Inner { value: renamed } } =
        Outer { inner: Inner { value: x .* x } } in renamed + x;
    result
}"""
        relation, _ = compile_text(expression_let)
        self.assertEqual([node["op"] for node in relation["nodes"]], ["mul", "add"])

    def test_nested_nominal_and_binding_errors(self) -> None:
        prelude = """struct Inner { value: [m31; 1] }
struct Other { value: [m31; 1] }
struct Outer { inner: Inner, pair: ([m31; 1], [m31; 1]) }
"""
        cases = (
            ("let Outer { inner: Other { value: a } } = "
             "Outer { inner: Inner { value: x }, pair: (x, x) }; a",
             "struct pattern expects Other"),
            ("let Outer { inner: Inner { missing: a } } = "
             "Outer { inner: Inner { value: x }, pair: (x, x) }; a",
             "unknown Inner pattern field missing"),
            ("let Outer { inner: Inner { value: a }, pair: (a, b) } = "
             "Outer { inner: Inner { value: x }, pair: (x, x) }; a",
             "duplicate tuple binding"),
            ("let Outer { inner: (a, b) } = "
             "Outer { inner: Inner { value: x }, pair: (x, x) }; a",
             "tuple projection index is out of range"),
        )
        for body, message in cases:
            with self.subTest(message=message), self.assertRaisesRegex(
                SourceError, r"^<source>:[0-9]+:[0-9]+: " + message
            ):
                compile_text(prelude +
                             "circuit p(public x: [m31; 1]) -> public [m31; 1] { "
                             + body + " }")

    def test_omitted_nested_field_does_not_hide_partial_effect(self) -> None:
        source = """struct Inner { value: [m31; 1], ignored: [m31; 1] }
struct Outer { inner: Inner }
circuit p(public flag: bit, private x: [m31; 1]) -> public [m31; 1] {
    if flag then
        let Outer { inner: Inner { value: selected } } =
            Outer { inner: Inner { value: x, ignored: std::math::inv(x) } }
        in selected
    else x
}"""
        with self.assertRaisesRegex(SourceError,
                                    "if branch may fail when inactive: std::math::inv"):
            compile_text(source)


if __name__ == "__main__":
    unittest.main()
