"""Generated tuple programs against an independent source evaluator.

The expression generator/evaluator is shared with the scalar functional
corpus; it does not inspect S31's AST or specialization internals. Every
case compares the entire emitted relation with a direct first-order source.
"""

from __future__ import annotations

import hashlib
import itertools
import random
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from oracle import OracleError, evaluate_relation
from test_functional_generated import P, Term, generate_term
from text_frontend import compile_text


SEED = 0x5317A1E
CASES = 40
CORPUS_SHA256 = "f872ca5191da1dcf52d30d30fcaba1918e2530e6ff6df43f0c6a157f7077ff0a"
T = "[m31; 1]"
HEADER = f"""circuit generated_tuple(public b: bit, private x: {T},
    private y: {T}) -> public {T} {{
"""
PAIR = f"fn make_pair(a: {T}, c: {T}) -> ({T}, {T}) {{ (a, c) }}\n"
NESTED = (f"fn make_nested(a: {T}, c: {T}) -> (({T}, {T}), {T}) "
          "{ ((a, c), a) }\n")


def cases() -> list[tuple[Term, Term, bool]]:
    rng = random.Random(SEED)
    return [(generate_term(rng, 2, ("x", "y"), itertools.count()),
             generate_term(rng, 2, ("x", "y"), itertools.count()),
             index % 2 == 1)
            for index in range(CASES)]


def sources(first: Term, second: Term, nested: bool) -> tuple[str, str]:
    shared = (HEADER + f"    let first = {first.source()};\n"
              f"    let second = {second.source()};\n")
    if nested:
        functional = NESTED + shared + (
            "    let packed = make_nested(first, second);\n"
            "    let result = if b then packed.0.1 else packed.1;\n"
            "    result\n}\n")
        direct = shared + "    let result = if b then second else first;\n    result\n}\n"
    else:
        functional = PAIR + shared + (
            "    let packed = make_pair(first, second);\n"
            "    let result = if b then packed.0 else packed.1;\n"
            "    result\n}\n")
        direct = shared + "    let result = if b then first else second;\n    result\n}\n"
    return functional, direct


class GeneratedTupleTests(unittest.TestCase):
    def test_corpus_identity(self) -> None:
        samples = cases()
        corpus = "\n===CASE===\n".join("\n===SOURCE===\n".join(sources(*case))
                                          for case in samples)
        self.assertEqual(len(samples), CASES)
        self.assertEqual(hashlib.sha256(corpus.encode()).hexdigest(), CORPUS_SHA256)
        self.assertEqual(sum(nested for _, _, nested in samples), CASES // 2)

    def test_semantics_and_exact_relation(self) -> None:
        rng = random.Random(SEED ^ 0xA11CE)
        for index, (first, second, nested) in enumerate(cases()):
            with self.subTest(case=index):
                functional, direct = sources(first, second, nested)
                relation, _ = compile_text(functional)
                reference, _ = compile_text(direct)
                self.assertEqual(relation, reference)
                self.assertFalse(any(node["op"] in {"tuple", "project", "call"}
                                     for node in relation["nodes"]))
                for bit in (0, 1):
                    for x, y in ((0, 0), (P - 1, 1),
                                 (rng.randrange(P), rng.randrange(P))):
                        env = {"b": bit, "x": x, "y": y}
                        a, c = first.value(env), second.value(env)
                        expected = (c if nested else a) if bit else (a if nested else c)
                        assignment = {"public_inputs": {"b": [bit]},
                                      "private_inputs": {"x": [x], "y": [y]},
                                      "public_outputs": {"result": [expected]}}
                        self.assertEqual(evaluate_relation(relation, assignment),
                                         assignment["public_outputs"])
                        assignment["public_outputs"]["result"] = [(expected + 1) % P]
                        with self.assertRaises(OracleError):
                            evaluate_relation(relation, assignment)


if __name__ == "__main__":
    unittest.main()
