"""Independent array source terms versus functional/direct S31 lowering.

This generator owns its syntax and value semantics. It does not read the S31
AST, specializer, builder or relation oracle to calculate expected values.
All generated operations are total on canonical M31 arrays, so both arms of a
source conditional can occupy one fixed circuit.
"""

from __future__ import annotations

import hashlib
import itertools
import random
import sys
import unittest
from dataclasses import dataclass
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import compile_text


P = (1 << 31) - 1
SEED = 0xA224531
CASES = 64
CORPUS_SHA256 = "f68e0c786c7532b7572346e790e5075eaf4e1317665833d0248da700306b018e"
Words = tuple[int, int, int, int]


@dataclass(frozen=True)
class ArrayTerm:
    op: str
    atom: str | int | None = None
    args: tuple[ArrayTerm, ...] = ()

    def source(self, rename: dict[str, str] | None = None) -> str:
        rename = rename or {}
        if self.op == "var":
            assert isinstance(self.atom, str)
            return rename.get(self.atom, self.atom)
        if self.op == "literal":
            return f"splat<4>({self.atom}_m31)"
        if self.op == "let":
            assert isinstance(self.atom, str)
            next_rename = rename.copy()
            next_rename.pop(self.atom, None)
            return (f"(let {self.atom} = {self.args[0].source(rename)} in "
                    f"{self.args[1].source(next_rename)})")
        if self.op == "if":
            return (f"(if b then {self.args[0].source(rename)} "
                    f"else {self.args[1].source(rename)})")
        if self.op == "rotate":
            operand = self.args[0].source(rename)
            return ("std::array::concat(std::array::drop<2>(" + operand + "), "
                    "std::array::take<2>(" + operand + "))")
        operator = "+" if self.op == "add" else ".*"
        return f"({self.args[0].source(rename)} {operator} {self.args[1].source(rename)})"

    def value(self, env: dict[str, Words | int]) -> Words:
        if self.op == "var":
            assert isinstance(self.atom, str)
            value = env[self.atom]
            assert isinstance(value, tuple)
            return value
        if self.op == "literal":
            assert isinstance(self.atom, int)
            return (self.atom,) * 4
        if self.op == "let":
            assert isinstance(self.atom, str)
            bound = self.args[0].value(env)
            return self.args[1].value(env | {self.atom: bound})
        if self.op == "if":
            return self.args[0 if env["b"] else 1].value(env)
        if self.op == "rotate":
            values = self.args[0].value(env)
            return values[2:] + values[:2]
        lhs, rhs = (arg.value(env) for arg in self.args)
        return tuple((a + b if self.op == "add" else a * b) % P
                     for a, b in zip(lhs, rhs))  # type: ignore[return-value]


def generate_term(rng: random.Random, depth: int, names: tuple[str, ...],
                  serial: itertools.count) -> ArrayTerm:
    if depth == 0 or rng.randrange(5) == 0:
        if rng.randrange(4) == 0:
            return ArrayTerm("literal", rng.choice((0, 1, 7, P - 1)))
        return ArrayTerm("var", rng.choice(names))
    op = rng.choice(("add", "mul", "rotate", "let", "if"))
    if op == "rotate":
        return ArrayTerm(op, args=(generate_term(rng, depth - 1, names, serial),))
    if op == "let":
        local = "v" if "v" in names and rng.randrange(3) == 0 else f"local_{next(serial)}"
        return ArrayTerm(op, local, (generate_term(rng, depth - 1, names, serial),
                                     generate_term(rng, depth - 1, names + (local,), serial)))
    return ArrayTerm(op, args=(generate_term(rng, depth - 1, names, serial),
                               generate_term(rng, depth - 1, names, serial)))


@dataclass(frozen=True)
class Case:
    seed: ArrayTerm
    body: ArrayTerm
    alternate: ArrayTerm

    def sources(self) -> tuple[str, str]:
        header = """circuit generated_array(public b: bit, private x: [m31; 4],
    private y: [m31; 4]) -> public [m31; 4] {
"""
        common = f"    let saved = {self.seed.source()};\n"
        functional = """use std@1;
fn apply_array(f: Fn([m31; 4]) -> [m31; 4], z: [m31; 4]) -> [m31; 4] { f(z) }
""" + header + common + (
            "    let f = fun(v: [m31; 4]) -> [m31; 4] => "
            f"{self.body.source()};\n"
            "    let chosen = apply_array(f, saved);\n")
        direct = "use std@1;\n" + header + common + (
            f"    let chosen = {self.body.source({'v': 'saved'})};\n")
        tail = (f"    let other = {self.alternate.source()};\n"
                "    let result = if b then chosen else other;\n"
                "    result\n}\n")
        direct_tail = tail.replace("if b then chosen else other",
                                   "select(b, other, chosen)")
        return functional + tail, direct + direct_tail

    def value(self, bit: int, x: Words, y: Words) -> Words:
        env: dict[str, Words | int] = {"b": bit, "x": x, "y": y}
        saved = self.seed.value(env)
        return (self.body.value(env | {"v": saved}) if bit else
                self.alternate.value(env | {"saved": saved}))


def cases() -> list[Case]:
    rng = random.Random(SEED)
    result = []
    for _ in range(CASES):
        serial = itertools.count()
        result.append(Case(
            generate_term(rng, 2, ("x", "y"), serial),
            generate_term(rng, 3, ("v", "x", "y"), serial),
            generate_term(rng, 2, ("saved", "x", "y"), serial)))
    return result


def count(term: ArrayTerm, operation: str) -> int:
    return (term.op == operation) + sum(count(child, operation) for child in term.args)


class GeneratedFunctionalArrayTests(unittest.TestCase):
    def test_corpus_inventory(self) -> None:
        corpus = cases()
        sources = "\n===CASE===\n".join(
            "\n===SOURCE===\n".join(case.sources()) for case in corpus)
        self.assertEqual(len(corpus), CASES)
        self.assertEqual(hashlib.sha256(sources.encode()).hexdigest(), CORPUS_SHA256)
        for operation in ("add", "mul", "rotate", "let", "if"):
            self.assertGreater(sum(count(case.body, operation) for case in corpus), 8)
        self.assertGreater(sum("let v =" in case.body.source() for case in corpus), 4)

    def test_array_semantics_and_exact_relation(self) -> None:
        rng = random.Random(SEED ^ 0xA11CE)
        corpus = cases()
        for index, case in enumerate(corpus):
            functional, direct = case.sources()
            with self.subTest(case=index):
                relation, _ = compile_text(functional)
                reference, _ = compile_text(direct)
                self.assertEqual(relation, reference,
                                 "array function or conditional changed normalized IR")
                self.assertFalse(any(node["op"] in {"call", "lambda", "let", "if"}
                                     for node in relation["nodes"]))
                samples = (
                    ((0, 1, 2, 3), (3, 2, 1, 0)),
                    ((P - 1, 0, 1, 7), (1, P - 1, 9, 0)),
                    (tuple(rng.randrange(P) for _ in range(4)),
                     tuple(rng.randrange(P) for _ in range(4))),
                )
                for bit in (0, 1):
                    for x, y in samples:
                        expected = list(case.value(bit, x, y))
                        assignment = {"public_inputs": {"b": [bit]},
                                      "private_inputs": {"x": list(x), "y": list(y)},
                                      "public_outputs": {"result": expected[:]}}
                        self.assertEqual(evaluate_relation(relation, assignment),
                                         assignment["public_outputs"])
                        assignment["public_outputs"]["result"][0] = (expected[0] + 1) % P
                        with self.assertRaises(OracleError):
                            evaluate_relation(relation, assignment)


if __name__ == "__main__":
    unittest.main()
