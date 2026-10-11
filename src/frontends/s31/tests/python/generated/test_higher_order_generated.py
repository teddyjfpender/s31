"""Pinned higher-order erasure corpus with an independent field evaluator.

Each source variant uses the same arithmetic tree through named functions,
function values, returned closures, local shadowing or a captured lambda. The
comparison is the complete normalized relation, including operation order.
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
from text_frontend import SourceError, compile_text


P = (1 << 31) - 1
T = "[m31; 1]"
SEED = 0x531F0A1
TREES = 16
VARIANTS = 10
CORPUS_SHA256 = "5dca21038a630563a2cab32507b4b2a17a55273ab573039efa51035af376bdfc"


@dataclass(frozen=True)
class Tree:
    op: str
    left: Tree | None = None
    right: Tree | None = None

    def source(self, x: str = "x", y: str = "y") -> str:
        if self.op == "x":
            return x
        if self.op == "y":
            return y
        assert self.left is not None and self.right is not None
        symbol = "+" if self.op == "add" else ".*"
        return f"({self.left.source(x, y)} {symbol} {self.right.source(x, y)})"

    def value(self, x: int, y: int) -> int:
        if self.op == "x":
            return x
        if self.op == "y":
            return y
        assert self.left is not None and self.right is not None
        left, right = self.left.value(x, y), self.right.value(x, y)
        return ((left + right) if self.op == "add" else (left * right)) % P

    def operations(self) -> int:
        return 0 if self.left is None else 1 + self.left.operations() + self.right.operations()


def generate(rng: random.Random, depth: int) -> Tree:
    if depth == 0 or rng.randrange(5) == 0:
        return Tree(rng.choice(("x", "y")))
    return Tree(rng.choice(("add", "mul")), generate(rng, depth - 1),
                generate(rng, depth - 1))


def trees() -> list[Tree]:
    rng = random.Random(SEED)
    return [generate(rng, 4) for _ in range(TREES)]


def declarations(body: str) -> str:
    return f"""fn combine(v: {T}, rhs: {T}) -> {T} {{ {body} }}
fn apply(f: Fn({T}, {T}) -> {T}, v: {T}, rhs: {T}) -> {T} {{ f(v, rhs) }}
fn choose() -> Fn({T}, {T}) -> {T} {{ combine }}
fn factory(rhs: {T}) -> Fn({T}) -> {T} {{
  fun(v: {T}) -> {T} => {body}
}}
fn apply_factory(f: Fn({T}) -> Fn({T}) -> {T}, rhs: {T}, v: {T}) -> {T} {{
  f(rhs)(v)
}}
"""


def expressions(body: str) -> tuple[str, ...]:
    captured = body.replace("rhs", "y")
    return (
        "combine(x, y)",
        "apply(combine, x, y)",
        "(combine)(x, y)",
        "(let f = combine in f)(x, y)",
        "choose()(x, y)",
        "factory(y)(x)",
        "apply_factory(factory, y, x)",
        f"(fun(v: {T}) -> {T} => {captured})(x)",
        f"(let combine = fun(v: {T}, rhs: {T}) -> {T} => {body} in combine)(x, y)",
        "(let f = choose() in f)(x, y)",
    )


def source(decls: str, expression: str) -> str:
    return (decls + f"circuit generated(public b: bit, private x: {T}, private y: {T}) "
            f"-> public {T} {{ let result = if b then {expression} else y; result }}\n")


class GeneratedHigherOrderTests(unittest.TestCase):
    def test_corpus_identity_and_coverage(self) -> None:
        samples = trees()
        corpus = "\n===TREE===\n".join(
            "\n===SOURCE===\n".join(
                source(declarations(tree.source("v", "rhs")), expression)
                for expression in expressions(tree.source("v", "rhs")))
            for tree in samples)
        self.assertEqual(len(samples) * VARIANTS, 160)
        self.assertGreater(sum(tree.operations() for tree in samples), 45)
        self.assertEqual(hashlib.sha256(corpus.encode()).hexdigest(), CORPUS_SHA256)

    def test_zero_cost_and_independent_values(self) -> None:
        rng = random.Random(SEED ^ 0xA11CE)
        for tree_index, tree in enumerate(trees()):
            direct, _ = compile_text(source("", tree.source()))
            body = tree.source("v", "rhs")
            decls = declarations(body)
            for variant_index, expression in enumerate(expressions(body)):
                with self.subTest(tree=tree_index, variant=variant_index):
                    relation, _ = compile_text(source(decls, expression))
                    self.assertEqual(relation, direct)
                    self.assertFalse(any(node["op"] in {"lambda", "apply", "call"}
                                         for node in relation["nodes"]))
                    for x, y in ((0, P - 1), (P - 1, 1),
                                 (rng.randrange(P), rng.randrange(P))):
                        for bit in (0, 1):
                            expected = tree.value(x, y) if bit else y
                            assignment = {
                                "public_inputs": {"b": [bit]},
                                "private_inputs": {"x": [x], "y": [y]},
                                "public_outputs": {"result": [expected]},
                            }
                            self.assertEqual(evaluate_relation(relation, assignment),
                                             assignment["public_outputs"])
                            assignment["public_outputs"]["result"] = [(expected + 1) % P]
                            with self.assertRaises(OracleError):
                                evaluate_relation(relation, assignment)

    def test_partial_effect_survives_every_function_value_route(self) -> None:
        body = "std::math::inv(v)"
        decls = declarations(body)
        for index, expression in enumerate(expressions(body)):
            with self.subTest(variant=index), self.assertRaisesRegex(
                SourceError, "if branch may fail when inactive: std::math::inv"
            ):
                compile_text(source(decls, expression))


if __name__ == "__main__":
    unittest.main()
