"""Generated source semantics versus independent arithmetic and direct S31.

The generator owns its syntax tree and evaluator. It never reads the S31 AST,
specializer, builder or oracle internals to decide the expected source value.
The S31 oracle separately evaluates the emitted relation. Identical relations
for functional and direct forms are a zero-abstraction-cost regression gate.
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
from text_frontend import SourceError, compile_text


P = (1 << 31) - 1
SEED = 0x531F00D
CASES = 96
CORPUS_SHA256 = "82d0e03d5af05b4fa1eb7ebfeaf8adde3e3c118a808ea9a2922a930c744f74cb"


@dataclass(frozen=True)
class Term:
    op: str
    atom: str | int | None = None
    args: tuple[Term, ...] = ()

    def source(self, rename: dict[str, str] | None = None) -> str:
        rename = rename or {}
        if self.op == "var":
            assert isinstance(self.atom, str)
            return rename.get(self.atom, self.atom)
        if self.op == "literal":
            return f"splat<1>({self.atom}_m31)"
        if self.op == "let":
            assert isinstance(self.atom, str)
            return (f"(let {self.atom} = {self.args[0].source(rename)} in "
                    f"{self.args[1].source(rename)})")
        if self.op == "if":
            return (f"(if b then {self.args[0].source(rename)} "
                    f"else {self.args[1].source(rename)})")
        symbol = "+" if self.op == "add" else ".*"
        return f"({self.args[0].source(rename)} {symbol} {self.args[1].source(rename)})"

    def value(self, env: dict[str, int]) -> int:
        if self.op == "var":
            assert isinstance(self.atom, str)
            return env[self.atom]
        if self.op == "literal":
            assert isinstance(self.atom, int)
            return self.atom
        if self.op == "let":
            assert isinstance(self.atom, str)
            bound = self.args[0].value(env)
            return self.args[1].value(env | {self.atom: bound})
        if self.op == "if":
            return self.args[0 if env["b"] else 1].value(env)
        lhs, rhs = (child.value(env) for child in self.args)
        return (lhs + rhs if self.op == "add" else lhs * rhs) % P


def generate_term(rng: random.Random, depth: int, names: tuple[str, ...],
                  serial: itertools.count) -> Term:
    if depth == 0 or rng.randrange(5) == 0:
        if rng.randrange(4) == 0:
            return Term("literal", rng.choice((0, 1, 2, 7, P - 1)))
        return Term("var", rng.choice(names))
    op = rng.choice(("add", "mul", "if", "let"))
    if op == "let":
        local = f"local_{next(serial)}"
        return Term(op, local, (generate_term(rng, depth - 1, names, serial),
                                generate_term(rng, depth - 1, names + (local,), serial)))
    return Term(op, args=(generate_term(rng, depth - 1, names, serial),
                          generate_term(rng, depth - 1, names, serial)))


@dataclass(frozen=True)
class Case:
    seed: Term
    body: Term
    alternate: Term

    def sources(self) -> tuple[str, str]:
        header = """circuit generated(public b: bit, public x: [m31; 1],
            public y: [m31; 1]) -> public [m31; 1] {
"""
        common = f"    let saved = {self.seed.source()};\n"
        functional = """use std@1;
fn apply(f: Fn([m31; 1]) -> [m31; 1], z: [m31; 1]) -> [m31; 1] { f(z) }
""" + header + common + (
            "    let f = fun(v: [m31; 1]) -> [m31; 1] => "
            f"{self.body.source()};\n"
            "    let trueValue = apply(f, saved);\n")
        direct = "use std@1;\n" + header + common + (
            f"    let trueValue = {self.body.source({'v': 'saved'})};\n")
        tail = (f"    let falseValue = {self.alternate.source()};\n"
                "    let result = if b then trueValue else falseValue;\n"
                "    result\n}\n")
        direct_tail = tail.replace("if b then trueValue else falseValue",
                                   "select(b, falseValue, trueValue)")
        return functional + tail, direct + direct_tail

    def value(self, b: int, x: int, y: int) -> int:
        env = {"b": b, "x": x, "y": y}
        saved = self.seed.value(env)
        return (self.body.value(env | {"v": saved}) if b else
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


def count(term: Term, op: str) -> int:
    return (term.op == op) + sum(count(child, op) for child in term.args)


class GeneratedFunctionalTests(unittest.TestCase):
    def test_corpus_inventory(self) -> None:
        generated = cases()
        sources = "\n===CASE===\n".join(
            "\n===SOURCE===\n".join(case.sources()) for case in generated)
        self.assertEqual(len(generated), CASES)
        self.assertEqual(hashlib.sha256(sources.encode()).hexdigest(), CORPUS_SHA256)
        self.assertGreater(sum(count(case.body, "let") for case in generated), 10)
        self.assertGreater(sum(count(case.body, "if") for case in generated), 10)
        self.assertGreater(sum(count(case.body, "mul") for case in generated), 10)
        self.assertGreater(sum(count(case.body, "add") for case in generated), 10)
        self.assertGreater(sum("x" in case.body.source() or "y" in case.body.source()
                               for case in generated), 60)

    def test_semantics_and_exact_relation_cost(self) -> None:
        rng = random.Random(SEED ^ 0xA11CE)
        for index, case in enumerate(cases()):
            functional, direct = case.sources()
            with self.subTest(case=index):
                relation, _ = compile_text(functional)
                reference, _ = compile_text(direct)
                self.assertEqual(relation, reference,
                                 "source functions or if added nodes or changed bindings")
                self.assertTrue(all(node["op"] not in {"call", "lambda", "let", "if"}
                                    for node in relation["nodes"]))
                output = relation["public_outputs"][0]
                samples = ((0, 0), (1, P - 1), (P - 1, 1),
                           (rng.randrange(P), rng.randrange(P)))
                for choice in (0, 1):
                    for x, y in samples:
                        expected = case.value(choice, x, y)
                        assignment = {"public_inputs": {"b": [choice], "x": [x], "y": [y]},
                                      "private_inputs": {}, "public_outputs": {output: [expected]}}
                        self.assertEqual(evaluate_relation(relation, assignment),
                                         assignment["public_outputs"])
                        assignment["public_outputs"][output] = (expected + 1) % P
                        with self.assertRaises(OracleError):
                            evaluate_relation(relation, assignment)

    def test_malformed_mutations_have_located_diagnostics(self) -> None:
        rng = random.Random(SEED ^ 0xBAD)
        originals = [case.sources()[0] for case in cases()[:8]]
        alphabet = "[]{}();,:<>+*-_@#é"
        rejected = 0
        for source in originals:
            for _ in range(12):
                index = rng.randrange(len(source))
                operation = rng.randrange(3)
                mutant = (source[:index] +
                          ("" if operation == 0 else rng.choice(alphabet)) +
                          source[index + (operation != 1):])
                try:
                    compile_text(mutant, "<mutant>")
                except SourceError as exc:
                    rejected += 1
                    self.assertRegex(str(exc), r"^<mutant>:[0-9]+:[0-9]+:")
        self.assertGreaterEqual(rejected, 60)

    def test_deep_expressions_and_types_stop_at_located_limits(self) -> None:
        expression = "(" * 140 + "x" + ")" * 140
        source = ("circuit deep(public x: [m31; 1]) -> public [m31; 1] { "
                  + expression + " }")
        with self.assertRaisesRegex(SourceError,
                                    r"<deep-expr>:1:[0-9]+: expression nesting limit exceeded"):
            compile_text(source, "<deep-expr>")

        expression = " + ".join(["x"] * 140)
        source = ("circuit deep(public x: [m31; 1]) -> public [m31; 1] { "
                  + expression + " }")
        with self.assertRaisesRegex(SourceError,
                                    r"<deep-tree>:1:[0-9]+: expression tree depth limit exceeded"):
            compile_text(source, "<deep-tree>")

        nested_type = "Fn() -> " * 40 + "[m31; 1]"
        source = (f"fn unused(f: {nested_type}) -> [m31; 1] {{ splat<1>(0_m31) }}\n"
                  "circuit deep(public x: [m31; 1]) -> public [m31; 1] { x }")
        with self.assertRaisesRegex(SourceError,
                                    r"<deep-type>:1:[0-9]+: type nesting limit exceeded"):
            compile_text(source, "<deep-type>")


if __name__ == "__main__":
    unittest.main()
