"""Deterministic source mutation check of the bounded direct-gate certificate.

This owns a small positional DAG generator independent of either S31 parser.
Every source admitted by the certificate is compiled again by the production
front end; both the named relation and the canonical native schedule must
agree. Rejections are kept separate: S31 supports valid programs outside the
deliberately narrow certificate grammar.
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


SEED = 0x531C0A11
CASES = 64
# SHA256 over label, NUL, exact UTF-8 source, NUL for every case and variant.
CORPUS_SHA256 = "332b31c1cf5c85dc91378b7d2dbc2c5b3724601bf09ce9140a387bc12a8685c8"


@dataclass(frozen=True)
class Sample:
    label: str
    source: str
    gate_count: int
    return_id: int


def _spell(index: int, steps: list[tuple[str, int, int]], return_id: int,
           style: str) -> str:
    renamed = style == "alpha"
    def name(wire_id: int) -> str:
        # The public output's producer name is itself part of verifier
        # identity. Rename only internal, non-output producers.
        return f"{'n' if renamed and wire_id != return_id else 'p'}{wire_id}"

    lines: list[str] = []
    for wire_id, (op, lhs, rhs) in enumerate(steps, 1):
        left = "x" if lhs == 0 else name(lhs)
        right = "x" if rhs == 0 else name(rhs)
        if style == "parenthesized":
            left, right = f"({left})", f"({right})"
        if style == "aliases" and wire_id % 2 == 0:
            lines.append(f"let alias_{wire_id} = ({left});")
            left = f"alias_{wire_id}"
        expression = f"{left} {op} {right}"
        if style == "parenthesized":
            expression = f"({expression})"
        lines.append(f"let {name(wire_id)} = {expression};")
    result = name(return_id)
    if style == "aliases":
        lines.append(f"let returned = (({result}));")
        result = "returned"
    if style == "comments":
        # Comments terminate at LF; the same token stream reaches both parsers.
        body = "\n// after an eager binding\n\t".join(lines)
        body = body.replace(" + ", " // before addition\n + ", 1)
        body = body.replace(" .* ", " // before multiplication\n .* ", 1)
        body += f"\n// return an earlier or final gate\n{result}"
    elif style == "whitespace":
        body = "\v\n\t".join(lines) + f"\f\r\n{result};"
    else:
        body = " ".join(lines) + f" {result}"
    return (f"circuit mutation_{index}(public x: [m31; 4]) "
            f"-> public [m31; 4] {{ {body} }}")


def corpus() -> list[Sample]:
    rng = random.Random(SEED)
    samples: list[Sample] = []
    for index in range(CASES):
        count = 1 + index % 16
        steps: list[tuple[str, int, int]] = []
        seen: set[tuple[str, int, int]] = set()
        for wire_id in range(1, count + 1):
            available = [(op, lhs, rhs)
                         for op in ("+", ".*")
                         for lhs in range(wire_id)
                         for rhs in range(lhs, wire_id)
                         if (op, lhs, rhs) not in seen]
            selected = rng.choice(available)
            seen.add(selected)
            steps.append(selected)
        return_id = max(1, count // 2) if index % 2 else count
        for style in ("direct", "parenthesized", "aliases", "comments",
                      "whitespace", "alpha"):
            samples.append(Sample(f"{index:02d}:{style}",
                                  _spell(index, steps, return_id, style),
                                  count, return_id))
    return samples


def corpus_digest(samples: list[Sample]) -> str:
    packed = b"".join(sample.label.encode() + b"\0" +
                      sample.source.encode() + b"\0" for sample in samples)
    return hashlib.sha256(packed).hexdigest()


class SourceMutationCorrespondenceTests(unittest.TestCase):
    def test_admitted_mutations_match_production_and_exact_schedule(self) -> None:
        samples = corpus()
        self.assertEqual(len(samples), CASES * 6)
        self.assertEqual(corpus_digest(samples), CORPUS_SHA256)
        self.assertEqual({sample.gate_count for sample in samples}, set(range(1, 17)))
        self.assertGreater(sum(sample.return_id < sample.gate_count
                               for sample in samples), 100)
        by_case: dict[int, dict[str, tuple[dict, bytes, list]]] = {}
        for sample in samples:
            with self.subTest(source=sample.label):
                checked, syntax = parse_source(sample.source.encode())
                produced, source_map = compile_text(sample.source)
                self.assertEqual(checked, produced)
                self.assertEqual(len(checked["nodes"]), sample.gate_count)
                self.assertEqual(syntax["output"], sample.return_id)
                self.assertEqual(set(source_map),
                                 {node["name"] for node in checked["nodes"]})
                index_text, style = sample.label.split(":")
                by_case.setdefault(int(index_text), {})[style] = (
                    checked, canonical_ir_bytes(syntax),
                    exact_direct_gate_schedule(syntax))
        for index, variants in by_case.items():
            with self.subTest(case=index, equivalence="token-and-alias-erasure"):
                base = variants["direct"]
                for style in ("parenthesized", "aliases", "comments", "whitespace"):
                    self.assertEqual(variants[style], base)
                # Local producer names appear in the relation but not in the
                # canonical IR or positional native row schedule.
                if len(base[0]["nodes"]) > 1:
                    self.assertNotEqual(variants["alpha"][0], base[0])
                self.assertEqual(variants["alpha"][1], base[1])
                self.assertEqual(variants["alpha"][2], base[2])

    def test_rejection_boundary_is_explicit_and_fail_closed(self) -> None:
        base = ("circuit boundary(public x: [m31; 4]) -> public [m31; 4] "
                "{ let a = x .* x; let b = x + a; b }")
        both_reject = {
            "unbound": base.replace("x + a", "x + missing"),
            "duplicate-name": base.replace("let b =", "let a ="),
            "bad-operator": base.replace("x + a", "x / a"),
            "missing-brace": base[:-1],
            "double-final-semicolon": base.replace("b }", "b;; }"),
        }
        for label, source in both_reject.items():
            with self.subTest(boundary=label):
                with self.assertRaises(UnsupportedFragment):
                    parse_source(source.encode())
                with self.assertRaises(SourceError):
                    compile_text(source)
        # The production language accepts these, but neither can enter the
        # bounded direct-gate correspondence certificate.
        wider_language = {
            "nested-arithmetic": base.replace("x + a", "(x + a) .* a"),
            "noncanonical-operands": base.replace("x + a", "a + x"),
            "return-input": base.replace("b }", "x }"),
            "common-subexpression": base.replace("x + a; b", "x .* x; b"),
        }
        for label, source in wider_language.items():
            with self.subTest(boundary=label):
                with self.assertRaises(UnsupportedFragment):
                    parse_source(source.encode())
                compile_text(source)

    def test_resource_edges_do_not_expand_the_certificate(self) -> None:
        base = ("circuit boundary(public x: [m31; 4]) -> public [m31; 4] "
                "{ let a = x .* x; a }")
        at_byte_limit = base + " " * (16_384 - len(base.encode()))
        at_token_limit = ("circuit boundary(public x: [m31; 4]) -> public [m31; 4] { "
                          + " ".join(f"let a{i} = x;" for i in range(45))
                          + " let result = x .* x; (result) }")
        at_token_limit_plus_one = at_token_limit.replace("(result) }", "(result); }")
        self.assertEqual(len(at_byte_limit.encode()), 16_384)
        for label, source in (("bytes", at_byte_limit),
                              ("tokens", at_token_limit)):
            with self.subTest(resource=label):
                checked, _ = parse_source(source.encode())
                produced, _ = compile_text(source)
                self.assertEqual(checked, produced)
        too_long_name = base.replace("let a =", "let " + "a" * 129 + " =")
        for label, source in (("bytes", at_byte_limit + " "),
                              ("tokens", at_token_limit_plus_one),
                              ("producer-name", too_long_name)):
            with self.subTest(resource=label), self.assertRaises(UnsupportedFragment):
                parse_source(source.encode())
        # The byte and token limits are admission bounds, not production
        # language limits: both one-step-over sources remain valid S31.
        compile_text(at_byte_limit + " ")
        compile_text(at_token_limit_plus_one)
        with self.assertRaises(UnsupportedFragment):
            parse_source(b"\xff" + base.encode())

    def test_eager_dead_arithmetic_keeps_rows_after_return(self) -> None:
        head = ("circuit eager(public x: [m31; 4]) -> public [m31; 4] "
                "{ let first = x .* x; let second = x + first; "
                "let unused = first .* second; ")
        early = head + "second }"
        late = head + "unused }"
        early_relation, early_syntax = parse_source(early.encode())
        late_relation, late_syntax = parse_source(late.encode())
        self.assertEqual(early_relation, compile_text(early)[0])
        self.assertEqual(late_relation, compile_text(late)[0])
        self.assertEqual(early_relation["nodes"], late_relation["nodes"])
        self.assertEqual(len(early_relation["nodes"]), 3)
        self.assertNotEqual(early_relation["public_outputs"],
                            late_relation["public_outputs"])
        self.assertNotEqual(canonical_ir_bytes(early_syntax),
                            canonical_ir_bytes(late_syntax))
        self.assertNotEqual(exact_direct_gate_schedule(early_syntax),
                            exact_direct_gate_schedule(late_syntax))


if __name__ == "__main__":
    unittest.main()
