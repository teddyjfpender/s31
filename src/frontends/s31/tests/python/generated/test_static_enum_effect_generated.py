"""Differentially check static enum erasure across array and function routes.

The expected program is written without an enum. Its outputs are calculated
from M31 arithmetic separately from either compiler lowering. This corpus
covers the same effect rule as the native one-lane acceptance fixture without
making 112 redundant native proofs.
"""

from __future__ import annotations

import hashlib
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation  # noqa: E402
from text_frontend import SourceError, compile_text  # noqa: E402

P = (1 << 31) - 1
VALUES = (0, 1, 2, 7, P - 1, P - 2, 1_234_567)
ROUTES = ("direct", "relay", "factory", "lambda")
CORPUS_SHA256 = "909fcdb218488057cbcdf031fd8ebc697d920eccf6de0fab3d1946f7277502bf"


def static_source(lanes: int, op: str, side: str, route: str, *,
                  selected: str = "Safe", eager_inverse: bool = False) -> str:
    payload = "std::math::inv(x)" if eager_inverse else "x"
    prelude = f"""use std@1;
enum Choice {{ Safe: [m31; {lanes}], Risky: [m31; {lanes}] }}
fn choose(choice: Choice, flag: bit) -> [m31; {lanes}] {{
    match choice {{
        Choice::Risky(v) => if flag then std::math::inv(v) else v,
        Choice::Safe(v) => v {op} v
    }}
}}
"""
    choice = f"Choice::{selected}({payload})"
    if route == "relay":
        prelude += (f"fn relay(choice: Choice, flag: bit) -> [m31; {lanes}] "
                    "{ choose(choice, flag) }\n")
        selected_expr = f"relay({choice}, flag)"
    elif route == "factory":
        prelude += (f"fn make(x: [m31; {lanes}]) -> Choice "
                    f"{{ {choice} }}\n")
        selected_expr = "choose(make(x), flag)"
    elif route == "lambda":
        selected_expr = (f"(fun(c: Choice) -> [m31; {lanes}] => "
                         f"choose(c, flag))({choice})")
    elif route == "direct":
        selected_expr = f"choose({choice}, flag)"
    else:
        raise ValueError(f"unknown static enum route: {route}")
    conditional = (f"if flag then {selected_expr} else x" if side == "then" else
                   f"if flag then x else {selected_expr}")
    return prelude + (f"circuit p(public flag: bit, private x: [m31; {lanes}]) "
                      f"-> public [m31; {lanes}] "
                      f"{{ let out = {conditional}; out }}")


def direct_source(lanes: int, op: str, side: str) -> str:
    arithmetic = f"x {op} x"
    conditional = (f"if flag then {arithmetic} else x" if side == "then" else
                   f"if flag then x else {arithmetic}")
    return (f"circuit p(public flag: bit, private x: [m31; {lanes}]) "
            f"-> public [m31; {lanes}] "
            f"{{ let out = {conditional}; out }}")


class StaticEnumEffectCorpus(unittest.TestCase):
    def test_static_routes_erase_to_exact_direct_relation_and_values(self) -> None:
        corpus = hashlib.sha256()
        for lanes in range(1, len(VALUES) + 1):
            x = list(VALUES[:lanes])
            for op in ("+", ".*"):
                for side in ("then", "else"):
                    direct, _ = compile_text(direct_source(lanes, op, side))
                    for route in ROUTES:
                        with self.subTest(lanes=lanes, op=op, side=side, route=route):
                            source = static_source(lanes, op, side, route)
                            handwritten = direct_source(lanes, op, side)
                            corpus.update(source.encode() + b"\0" + handwritten.encode() + b"\0")
                            wrapped, source_map = compile_text(source)
                            self.assertEqual(wrapped, direct)
                            self.assertEqual([node["op"] for node in wrapped["nodes"]],
                                             ["add" if op == "+" else "mul", "select"])
                            self.assertEqual(set(source_map),
                                             {node["name"] for node in wrapped["nodes"]})
                            for flag in (0, 1):
                                chosen = flag == (side == "then")
                                expected = [(((2 * value if op == "+" else value * value)
                                              if chosen else value) % P) for value in x]
                                assignment = {
                                    "public_inputs": {"flag": [flag]},
                                    "private_inputs": {"x": x},
                                    "public_outputs": {"out": expected},
                                }
                                self.assertEqual(evaluate_relation(wrapped, assignment),
                                                 {"out": expected})
                                changed = {**assignment, "public_outputs": {
                                    "out": [((expected[0] + 1) % P), *expected[1:]]}}
                                with self.assertRaises(OracleError):
                                    evaluate_relation(wrapped, changed)
        self.assertEqual(corpus.hexdigest(), CORPUS_SHA256)

    def test_selected_and_eager_inverse_are_rejected_through_every_route(self) -> None:
        for route in ROUTES:
            for side in ("then", "else"):
                for selected, eager_inverse in (("Risky", False), ("Safe", True)):
                    with self.subTest(route=route, side=side,
                                      selected=selected, eager_inverse=eager_inverse):
                        source = static_source(1, "+", side, route,
                                               selected=selected,
                                               eager_inverse=eager_inverse)
                        with self.assertRaisesRegex(
                                SourceError,
                                "if branch may fail when inactive: std::math::inv"):
                            compile_text(source)


if __name__ == "__main__":
    unittest.main()
