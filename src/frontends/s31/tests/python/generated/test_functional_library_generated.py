"""Independent library arithmetic and hash values through erased closures.

These cases exercise library calls whose implementations are outside the Lean
functional core. Their expected values use modular integer arithmetic and the
separate Poseidon2 reference implementation, never the S31 relation builder.
"""

from __future__ import annotations

import hashlib
import random
import sys
import unittest
from dataclasses import dataclass
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from poseidon2_oracle import leaf, pair
from text_frontend import compile_text


P = (1 << 31) - 1
SEED = 0x5311B
CORPUS_SHA256 = "1dd55d10c2f97a3a9125f6c01e672545edcbd604b33220442c18207ef7eadd80"


def scalar(value: int) -> str:
    return f"splat<4>({value}_m31)"


@dataclass(frozen=True)
class MathCase:
    family: str
    constants: tuple[int, ...]

    def body(self, variable: str) -> str:
        c = self.constants
        if self.family == "poly":
            return (f"std::math::poly_eval({variable}, [{scalar(c[0])}, x, y, "
                    f"{scalar(c[1])}])")
        if self.family == "dot":
            return (f"std::math::dot([{variable}, x, y], "
                    f"[x, y, {scalar(c[0])}])")
        if self.family == "matvec":
            return (f"std::math::sum(std::math::matvec([[{variable}, x], "
                    f"[y, {variable}]], [x, y]))")
        if self.family == "matmul":
            return ("std::math::sum(std::array::flatten(std::math::matmul(" 
                    f"[[{variable}, x], [y, {variable}]], [[x, y], [{variable}, x]])))")
        if self.family == "pow_sub":
            return f"std::math::pow<{c[0]}>({variable}) + std::math::sub(x, y)"
        raise AssertionError(self.family)

    def sources(self) -> tuple[str, str]:
        header = ("circuit library(private x: [m31; 4], private y: [m31; 4]) "
                  "-> public [m31; 4] {\n"
                  "    let saved = x + y;\n")
        helper = ("fn apply(f: Fn([m31; 4]) -> [m31; 4], z: [m31; 4]) "
                  "-> [m31; 4] { f(z) }\n")
        functional = ("use std@1;\n" + helper + header +
                      "    let f = fun(v: [m31; 4]) -> [m31; 4] => " +
                      self.body("v") + ";\n    apply(f, saved)\n}\n")
        direct = ("use std@1;\n" + header +
                  "    " + self.body("saved") + "\n}\n")
        return functional, direct

    def value(self, x: list[int], y: list[int]) -> list[int]:
        c = self.constants
        result = []
        for a, b in zip(x, y):
            v = (a + b) % P
            if self.family == "poly":
                z = c[0] + a * v + b * v * v + c[1] * v * v * v
            elif self.family == "dot":
                z = v * a + a * b + b * c[0]
            elif self.family == "matvec":
                z = v * a + a * b + b * a + v * b
            elif self.family == "matmul":
                z = v * a + a * v + v * b + a * a + b * a + v * v + b * b + v * a
            elif self.family == "pow_sub":
                z = pow(v, c[0], P) + a - b
            else:
                raise AssertionError(self.family)
            result.append(z % P)
        return result


def math_cases() -> list[MathCase]:
    rng = random.Random(SEED)
    cases = []
    for family in ("poly", "dot", "matvec", "matmul", "pow_sub"):
        for _ in range(4):
            constants = ((rng.randrange(P), rng.randrange(P)) if family == "poly" else
                         (rng.choice((0, 1, 2, 3, 5, 7, 17)) if family == "pow_sub" else
                          rng.randrange(P),))
            cases.append(MathCase(family, constants))
    return cases


def hash_sources(length: int, salt: int) -> tuple[str, str]:
    header = (f"circuit hash(private x: [m31; {length}]) "
              "-> public Digest<Poseidon2> {\n")
    expression = f"std::hash::poseidon2_leaf(x + splat<{length}>({salt}_m31))"
    functional = ("use std@1;\nfn apply(f: Fn([m31; " + str(length) +
                  "]) -> Digest<Poseidon2>, z: [m31; " + str(length) +
                  "]) -> Digest<Poseidon2> { f(z) }\n" + header +
                  f"    let salt = splat<{length}>({salt}_m31);\n"
                  f"    let f = fun(v: [m31; {length}]) -> Digest<Poseidon2> "
                  "=> std::hash::poseidon2_leaf(v + salt);\n"
                  "    apply(f, x)\n}\n")
    return functional, "use std@1;\n" + header + "    " + expression + "\n}\n"


def pair_sources() -> tuple[str, str]:
    header = ("circuit hash_pair(private x: [m31; 8], private y: [m31; 8]) "
              "-> public Digest<Poseidon2> {\n"
              "    let left = std::hash::poseidon2_leaf(x);\n")
    body = "std::hash::poseidon2_pair(left, std::hash::poseidon2_leaf(y))"
    functional = ("use std@1;\n"
                  "fn apply(f: Fn([m31; 8]) -> Digest<Poseidon2>, z: [m31; 8]) "
                  "-> Digest<Poseidon2> { f(z) }\n" + header +
                  "    let f = fun(v: [m31; 8]) -> Digest<Poseidon2> => "
                  "std::hash::poseidon2_pair(left, std::hash::poseidon2_leaf(v));\n"
                  "    apply(f, y)\n}\n")
    return functional, "use std@1;\n" + header + "    " + body + "\n}\n"


class GeneratedFunctionalLibraryTests(unittest.TestCase):
    def test_corpus_inventory(self) -> None:
        pairs = ([case.sources() for case in math_cases()] +
                 [hash_sources(length, salt) for length in (4, 8, 12, 16)
                  for salt in (0, 7)] + [pair_sources()])
        sources = "\n===CASE===\n".join("\n===SOURCE===\n".join(pair)
                                          for pair in pairs)
        self.assertEqual(len(pairs), 29)
        self.assertEqual(hashlib.sha256(sources.encode()).hexdigest(), CORPUS_SHA256)

    def test_math_semantics_and_exact_relation(self) -> None:
        rng = random.Random(SEED ^ 0xA11CE)
        samples = [([0] * 4, [P - 1] * 4),
                   ([P - 1, 0, 1, 2], [1, P - 1, P - 2, 7])]
        samples += [([rng.randrange(P) for _ in range(4)],
                     [rng.randrange(P) for _ in range(4)]) for _ in range(2)]
        for index, case in enumerate(math_cases()):
            with self.subTest(index=index, family=case.family):
                relation, _ = compile_text(case.sources()[0])
                direct, _ = compile_text(case.sources()[1])
                self.assertEqual(relation, direct)
                self.assertNotIn("call", [node["op"] for node in relation["nodes"]])
                output = relation["public_outputs"][0]
                for x, y in samples:
                    expected = case.value(x, y)
                    assignment = {"public_inputs": {}, "private_inputs": {"x": x, "y": y},
                                  "public_outputs": {output: expected}}
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"])
                    assignment["public_outputs"][output] = [(expected[0] + 1) % P, *expected[1:]]
                    with self.assertRaises(OracleError):
                        evaluate_relation(relation, assignment)

    def test_poseidon_semantics_and_exact_relation(self) -> None:
        rng = random.Random(SEED ^ 0xBEEF)
        for length in (4, 8, 12, 16):
            for salt in (0, 7):
                with self.subTest(length=length, salt=salt):
                    relation, _ = compile_text(hash_sources(length, salt)[0])
                    direct, _ = compile_text(hash_sources(length, salt)[1])
                    self.assertEqual(relation, direct)
                    self.assertEqual([node["op"] for node in relation["nodes"]][-1],
                                     "hash_poseidon2_leaf")
                    output = relation["public_outputs"][0]
                    for words in ([0] * length,
                                  [rng.randrange(P) for _ in range(length)]):
                        expected = leaf([(word + salt) % P for word in words])
                        assignment = {"public_inputs": {}, "private_inputs": {"x": words},
                                      "public_outputs": {output: expected}}
                        self.assertEqual(evaluate_relation(relation, assignment),
                                         assignment["public_outputs"])
                        assignment["public_outputs"][output] = [
                            (expected[0] + 1) % P, *expected[1:]]
                        with self.assertRaises(OracleError):
                            evaluate_relation(relation, assignment)

        relation, _ = compile_text(pair_sources()[0])
        direct, _ = compile_text(pair_sources()[1])
        self.assertEqual(relation, direct)
        self.assertEqual([node["op"] for node in relation["nodes"]],
                         ["hash_poseidon2_leaf", "hash_poseidon2_leaf", "hash_poseidon2_pair"])
        output = relation["public_outputs"][0]
        x = [rng.randrange(P) for _ in range(8)]
        y = [rng.randrange(P) for _ in range(8)]
        expected = pair(leaf(x), leaf(y))
        assignment = {"public_inputs": {}, "private_inputs": {"x": x, "y": y},
                      "public_outputs": {output: expected}}
        self.assertEqual(evaluate_relation(relation, assignment), assignment["public_outputs"])
        assignment["public_outputs"][output] = [(expected[0] + 1) % P, *expected[1:]]
        with self.assertRaises(OracleError):
            evaluate_relation(relation, assignment)


if __name__ == "__main__":
    unittest.main()
