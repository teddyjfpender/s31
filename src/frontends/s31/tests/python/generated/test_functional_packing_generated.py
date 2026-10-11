"""Independent functional/first-order parity across packed-lane boundaries.

The expected result is calculated from Python integers without reading S31's
AST, relation IR, value oracle, or circuit implementation. The programs use
the same source expressions at lengths before, on, and after a four-lane wire
boundary, including a capturing closure and an eager total conditional.
"""

from __future__ import annotations

import hashlib
import random
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import compile_text


P = (1 << 31) - 1
LENGTHS = (1, 2, 3, 4, 5, 7, 8, 9, 15)
SEED = 0x531F00E
CORPUS_SHA256 = "2f14de2c93593cd5b3ee5b3f405a5c925f485ed8f2c8115c7945de987c10f691"


def sources(length: int) -> tuple[str, str]:
    header = (f"circuit packed(private choice: bit, private x: [m31; {length}], "
              f"private y: [m31; {length}]) -> public [m31; 1] {{\n")
    common = "    let saved = x + y;\n"
    functional = ("use std@1;\n"
                  f"fn apply_array(f: Fn([m31; {length}]) -> [m31; {length}], "
                  f"v: [m31; {length}]) -> [m31; {length}] {{ f(v) }}\n"
                  + header + common
                  + f"    let f = fun(v: [m31; {length}]) -> [m31; {length}] => "
                    "v .* y + x;\n"
                  + "    let chosen = apply_array(f, saved);\n")
    first_order = ("use std@1;\n" + header + common
                   + "    let chosen = saved .* y + x;\n")
    tail = ("    let other = y + x;\n"
            "    let result = if choice then chosen else other;\n"
            "    let out = std::math::sum_lanes(result);\n"
            "    out\n}\n")
    return (functional + tail,
            first_order + tail.replace("if choice then chosen else other",
                                       "select(choice, other, chosen)"))


def expected(choice: int, x: list[int], y: list[int]) -> int:
    if choice:
        return sum((((a + b) % P) * b + a) % P for a, b in zip(x, y, strict=True)) % P
    return sum((a + b) % P for a, b in zip(x, y, strict=True)) % P


class FunctionalPackingGeneratedTests(unittest.TestCase):
    def test_corpus_identity_and_boundary_lengths(self) -> None:
        corpus = "\n===CASE===\n".join("\n===SOURCE===\n".join(sources(n))
                                     for n in LENGTHS)
        self.assertEqual(hashlib.sha256(corpus.encode()).hexdigest(), CORPUS_SHA256)
        self.assertTrue({3, 4, 5, 7, 8, 9} <= set(LENGTHS))

    def test_functional_packing_semantics_and_zero_cost_ir(self) -> None:
        rng = random.Random(SEED)
        for length in LENGTHS:
            functional, direct = sources(length)
            with self.subTest(length=length):
                relation, _ = compile_text(functional, f"packed-{length}.s31")
                reference, _ = compile_text(direct, f"direct-{length}.s31")
                self.assertEqual(relation, reference)
                self.assertEqual([node["op"] for node in relation["nodes"]],
                                 ["add", "mul", "add", "add", "select"] +
                                 (["sum_lanes"] if length > 1 else []))
                output_name = relation["public_outputs"][0]
                samples = [
                    ([0] * length, [0] * length),
                    ([P - 1] * length, [1] * length),
                    ([rng.randrange(P) for _ in range(length)],
                     [rng.randrange(P) for _ in range(length)]),
                ]
                for choice in (0, 1):
                    for x, y in samples:
                        value = expected(choice, x, y)
                        assignment = {
                            "public_inputs": {},
                            "private_inputs": {"choice": [choice], "x": x, "y": y},
                            "public_outputs": {output_name: [value]},
                        }
                        self.assertEqual(evaluate_relation(relation, assignment),
                                         assignment["public_outputs"])
                        assignment["public_outputs"][output_name][0] = (value + 1) % P
                        with self.assertRaises(OracleError):
                            evaluate_relation(relation, assignment)


if __name__ == "__main__":
    unittest.main()
