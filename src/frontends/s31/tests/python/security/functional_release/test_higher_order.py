"""Static named function values must erase without changing the gate graph."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import UnsupportedFragment, parse_source  # noqa: E402
from text_frontend import compile_text  # noqa: E402

SQUARE = "fn square(v: [m31; 4]) -> [m31; 4] { v .* v }\n"
APPLY = ("fn apply(f: Fn([m31; 4]) -> [m31; 4], v: [m31; 4]) "
         "-> [m31; 4] { f(v) }\n")
CIRCUIT = ("circuit calc(public x: [m31; 4]) -> public [m31; 4] {\n"
           "  let result = EXPR;\n  result\n}\n")
DIRECT = CIRCUIT.replace("EXPR", "x .* x")


class HigherOrderReleaseTests(unittest.TestCase):
    def test_named_function_routes_erase_to_one_gate(self) -> None:
        sources = (
            SQUARE + APPLY + CIRCUIT.replace("EXPR", "apply(square, x)"),
            SQUARE + APPLY + CIRCUIT.replace("EXPR", "let f = square in apply(f, x)"),
            SQUARE + APPLY + ("circuit calc(public x: [m31; 4]) -> public [m31; 4] {\n"
                              "  let f = square;\n  let g = f;\n"
                              "  let result = apply(g, x);\n  result\n}\n"),
            SQUARE + ("circuit calc(public x: [m31; 4]) -> public [m31; 4] {\n"
                      "  let f = square;\n  let result = f(x);\n  result\n}\n"),
            SQUARE + ("circuit calc(public x: [m31; 4]) -> public [m31; 4] {\n"
                      "  let f = let g = square in g;\n"
                      "  let result = f(x);\n  result\n}\n"),
            SQUARE + APPLY +
            ("fn relay(g: Fn([m31; 4]) -> [m31; 4], v: [m31; 4]) "
             "-> [m31; 4] { apply(g, v) }\n") +
            CIRCUIT.replace("EXPR", "relay(square, x)"),
        )
        direct = parse_source(DIRECT.encode())
        for index, source in enumerate(sources):
            with self.subTest(route=index):
                checked = parse_source(source.encode())
                self.assertEqual(checked, direct)
                self.assertEqual(checked[0], compile_text(source)[0])
                self.assertEqual(len(checked[0]["nodes"]), 1)

    def test_function_values_do_not_cross_the_circuit_boundary(self) -> None:
        rejected = (
            SQUARE + APPLY + CIRCUIT.replace("EXPR", "apply(x, x)"),
            SQUARE + APPLY + CIRCUIT.replace("EXPR", "apply(square, square)"),
            SQUARE + APPLY + CIRCUIT.replace("EXPR", "let f = square in let f = x .* x in apply(f, x)"),
            SQUARE + CIRCUIT.replace("EXPR", "let f = square in f"),
            SQUARE + APPLY + CIRCUIT.replace("EXPR", "apply(missing, x)"),
        )
        for index, source in enumerate(rejected):
            with self.subTest(rejection=index), self.assertRaises(UnsupportedFragment):
                parse_source(source.encode())


if __name__ == "__main__":
    unittest.main()
