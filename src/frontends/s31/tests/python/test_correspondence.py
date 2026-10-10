"""Bounded independent parser and ambiguous-input rejection controls."""

from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import (UnsupportedFragment, parse_source,
                                    read_canonical_json)
from text_frontend import compile_text


class CorrespondenceParserTests(unittest.TestCase):
    def test_add_mul_and_shared_let_match_production_relation(self) -> None:
        cases = (
            "let result = x + x; result",
            "let square = x .* x; let result = square .* square; result",
            "let a = x + x; let b = a .* x; let result = b + a; result",
        )
        for body in cases:
            source = ("circuit arithmetic(public x: [m31; 4]) -> public "
                      f"[m31; 4] {{ {body} }}")
            with self.subTest(body=body):
                independent, syntax = parse_source(source.encode())
                produced, _ = compile_text(source)
                self.assertEqual(independent, produced)
                self.assertEqual(len(syntax["instructions"]), len(produced["nodes"]))

    def test_rejects_forward_duplicate_and_unsupported_syntax(self) -> None:
        cases = (
            "let result = later .* x; let later = x .* x; result",
            "let result = x .* x; let result = result + x; result",
            "let result = (x .* x); result",
            "let result = std::math::pow<2>(x); result",
        )
        for body in cases:
            source = ("circuit arithmetic(public x: [m31; 4]) -> public "
                      f"[m31; 4] {{ {body} }}")
            with self.subTest(body=body), self.assertRaises(UnsupportedFragment):
                parse_source(source.encode())

    def test_duplicate_keys_and_noncanonical_json_reject(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "ambiguous.json"
            for data in ('{"op":"mul","op":"add"}\n',
                         '{"op": NaN}\n', '{ "op": "mul" }\n'):
                with self.subTest(data=data):
                    path.write_text(data)
                    with self.assertRaises(ValueError):
                        read_canonical_json(path)


if __name__ == "__main__":
    unittest.main()
