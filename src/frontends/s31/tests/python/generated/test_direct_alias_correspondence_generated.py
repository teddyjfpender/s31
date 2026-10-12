"""Generated cross-check of the independently certified direct-gate fragment.

The generator owns a positional arithmetic DAG and independently spells it
with aliases and redundant parentheses. It does not ask either parser to
choose an expected relation. Both source spellings must have byte-identical
canonical IR and the exact same independently modeled native gate schedule.
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

from package.correspondence import (UnsupportedFragment, canonical_ir_bytes,
                                    parse_source)
from package.direct_gate_schedule import exact_direct_gate_schedule
from text_frontend import SourceError, compile_text


SEED = 0x531A11A5
CASES = 512
CORPUS_SHA256 = "ef20b2a05bd5d8b12657be40a598fa3eb68e51b11ad8eede59d17f0c50683e42"


@dataclass(frozen=True)
class Case:
    source: str
    direct: str
    gate_count: int
    alias_count: int
    add_count: int
    return_id: int


def _parenthesize(name: str, depth: int) -> str:
    return "(" * depth + name + ")" * depth


def generate(index: int, rng: random.Random) -> Case:
    """Choose distinct canonical SSA operations before spelling source text."""
    count = 1 + index % 16
    alias_limit = 2 if count <= 4 else 1 if count <= 8 else 0
    paren_choices = 3 if count <= 8 else 2
    aliases: dict[int, list[str]] = {0: ["x"]}
    statements: list[str] = []
    direct: list[str] = []
    seen: set[tuple[str, int, int]] = set()
    add_count = 0
    alias_count = 0

    def add_alias_chain(wire_id: int, limit: int) -> None:
        nonlocal alias_count
        for _ in range(rng.randrange(limit + 1)):
            target = aliases[wire_id][-1]
            name = f"alias_{alias_count}"
            rhs = _parenthesize(target, rng.randrange(paren_choices))
            statements.append(f"let {name} = {rhs};")
            aliases[wire_id].append(name)
            alias_count += 1

    add_alias_chain(0, alias_limit)
    for wire_id in range(1, count + 1):
        candidates = [(op, lhs, rhs)
                      for op in ("+", ".*")
                      for lhs in range(wire_id)
                      for rhs in range(lhs, wire_id)
                      if (op, lhs, rhs) not in seen]
        op, lhs, rhs = rng.choice(candidates)
        seen.add((op, lhs, rhs))
        add_count += op == "+"
        left = _parenthesize(rng.choice(aliases[lhs]), rng.randrange(paren_choices))
        right = _parenthesize(rng.choice(aliases[rhs]), rng.randrange(paren_choices))
        expression = _parenthesize(f"{left} {op} {right}", rng.randrange(paren_choices))
        producer = f"p{wire_id}"
        statements.append(f"let {producer} = {expression};")
        direct.append(f"let {producer} = "
                      f"{'x' if lhs == 0 else f'p{lhs}'} {op} "
                      f"{'x' if rhs == 0 else f'p{rhs}'};")
        aliases[wire_id] = [producer]
        add_alias_chain(wire_id, alias_limit)

    # Some sources return a producer before the end of the eager body. The
    # later producers still occupy native arithmetic rows and may consume the
    # returned wire, so source erasure must retain them in the same order.
    return_id = count // 2 if count > 2 and index % 3 == 0 else count
    output = aliases[return_id][-1]
    # The final alias is always a distinct name, even when random alias chains
    # happened to be empty. That makes output-alias retargeting testable.
    statements.append(f"let returned = {_parenthesize(output, rng.randrange(paren_choices))};")
    alias_count += 1
    returned = _parenthesize("returned", rng.randrange(paren_choices))
    suffix = ";" if rng.randrange(2) else ""
    prefix = (f"circuit case_{index}(public x: [m31; 4]) "
              "-> public [m31; 4] { ")
    return Case(prefix + " ".join(statements) + f" {returned}{suffix} }}",
                prefix + " ".join(direct) + f" p{return_id} }}",
                count, alias_count, add_count, return_id)


def corpus() -> list[Case]:
    rng = random.Random(SEED)
    return [generate(index, rng) for index in range(CASES)]


class GeneratedDirectAliasCorrespondenceTests(unittest.TestCase):
    def test_generated_source_relation_and_exact_gate_schedule(self) -> None:
        cases = corpus()
        source_bytes = b"\x00".join(
            case.source.encode() + b"\x01" + case.direct.encode()
            for case in cases)
        self.assertEqual(hashlib.sha256(source_bytes).hexdigest(), CORPUS_SHA256)
        self.assertEqual(len(cases), CASES)
        self.assertEqual({case.gate_count for case in cases}, set(range(1, 17)))
        self.assertGreater(sum(case.alias_count for case in cases), CASES)
        self.assertGreater(sum(case.add_count for case in cases), 100)
        self.assertGreater(sum(case.gate_count - case.add_count for case in cases), 100)
        self.assertGreater(sum(case.return_id < case.gate_count for case in cases), 100)
        self.assertTrue(any(case.gate_count == 16 and case.return_id < 16
                            for case in cases))

        for index, case in enumerate(cases):
            with self.subTest(case=index):
                independent, syntax = parse_source(case.source.encode())
                direct, direct_syntax = parse_source(case.direct.encode())
                produced, source_map = compile_text(case.source)
                produced_direct, direct_source_map = compile_text(case.direct)
                self.assertEqual(independent, produced)
                self.assertEqual(independent, direct)
                self.assertEqual(produced, produced_direct)
                # Source positions differ by construction; the producer
                # inventory must remain identical after alias erasure.
                self.assertEqual(set(source_map), set(direct_source_map))
                self.assertEqual(set(source_map),
                                 {node["name"] for node in independent["nodes"]})
                self.assertEqual(len(syntax["instructions"]), case.gate_count)
                self.assertEqual(syntax["output"], case.return_id)
                self.assertEqual(canonical_ir_bytes(syntax),
                                 canonical_ir_bytes(direct_syntax))
                self.assertEqual(exact_direct_gate_schedule(syntax),
                                 exact_direct_gate_schedule(direct_syntax))

    def test_mutations_change_identity_or_fail_closed(self) -> None:
        # Alias retargeting must affect both parsers and the public verifier
        # identity. Duplicate names and forward operands must be rejected by
        # the independent parser, not silently normalized into a new program.
        cases = corpus()
        for index in range(1, CASES, 17):
            case = cases[index]
            if case.gate_count == 1:
                continue
            original, syntax = parse_source(case.source.encode())
            head, _, _ = case.source.partition("let returned =")
            changed_id = 2 if case.return_id == 1 else 1
            changed = head + f"let returned = p{changed_id}; returned }}"
            # Keep the circuit header and all eager source bindings intact.
            mutated, mutated_syntax = parse_source(changed.encode())
            produced, _ = compile_text(changed)
            self.assertEqual(mutated, produced)
            self.assertNotEqual(mutated, original)
            self.assertNotEqual(canonical_ir_bytes(mutated_syntax),
                                canonical_ir_bytes(syntax))
            self.assertNotEqual(exact_direct_gate_schedule(mutated_syntax),
                                exact_direct_gate_schedule(syntax))

            duplicate = case.source.replace("let p1 =", "let x =", 1)
            forward = case.source.replace("let p1 =", "let p1 = p16 + p16; let unused =", 1)
            for invalid in (duplicate, forward):
                with self.subTest(case=index, invalid=invalid[:100]):
                    with self.assertRaises(UnsupportedFragment):
                        parse_source(invalid.encode())
                    with self.assertRaises(SourceError):
                        compile_text(invalid)


if __name__ == "__main__":
    unittest.main()
