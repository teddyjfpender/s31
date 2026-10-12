"""Bounded pure-call specialization must preserve values and reuse live gates."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import (UnsupportedFragment, canonical_ir_bytes,
                                    parse_source, parse_source_optimized)  # noqa: E402
from package.direct_gate_main_correspondence import source_values  # noqa: E402
from text_frontend import compile_text  # noqa: E402

P = (1 << 31) - 1
WORDS = (0, 1, 2, 7)


def functional_source(count: int, reverse: bool, alias: bool) -> str:
    combination = "squared + doubled" if reverse else "doubled + squared"
    calls = [f"    let c{index} = {'saved' if alias else 'mix'}(x);"
             for index in range(count)]
    sums = []
    previous = "c0"
    for index in range(1, count):
        name = "out" if index == count - 1 else f"partial{index}"
        sums.append(f"    let {name} = {previous} + c{index};")
        previous = name
    return "\n".join([
        "fn double(a: [m31; 4]) -> [m31; 4] { a + a }",
        "fn square(a: [m31; 4]) -> [m31; 4] { a .* a }",
        "fn mix(a: [m31; 4]) -> [m31; 4] {",
        "    let doubled = double(a);",
        "    let squared = square(a);",
        f"    {combination}",
        "}",
        "circuit repeated(public x: [m31; 4]) -> public [m31; 4] {",
        *(["    let saved = mix;"] if alias else []),
        *calls, *sums, "    out", "}", "",
    ])


def manual_source(count: int) -> str:
    sums = []
    previous = "mixed"
    for index in range(1, count):
        name = "out" if index == count - 1 else f"partial{index}"
        sums.append(f"    let {name} = mixed + {previous};")
        previous = name
    return "\n".join([
        "circuit repeated(public x: [m31; 4]) -> public [m31; 4] {",
        "    let doubled = x + x;",
        "    let squared = x .* x;",
        "    let mixed = doubled + squared;",
        *sums, "    out", "}", "",
    ])


class OptimizedFunctionalCorrespondenceTests(unittest.TestCase):
    def test_repeated_helpers_reuse_all_live_gates(self) -> None:
        for count in (2, 3, 4):
            manual_relation, manual_syntax = parse_source(manual_source(count).encode())
            self.assertEqual(manual_relation, compile_text(manual_source(count))[0])
            for reverse in (False, True):
                for alias in (False, True):
                    with self.subTest(count=count, reverse=reverse, alias=alias):
                        source = functional_source(count, reverse, alias)
                        with self.assertRaises(UnsupportedFragment):
                            parse_source(source.encode())
                        relation, syntax = parse_source_optimized(source.encode())
                        self.assertEqual(relation, compile_text(source)[0])
                        self.assertEqual(len(relation["nodes"]), 4 * count - 1)
                        self.assertEqual(len(syntax["instructions"]), count + 2)
                        self.assertEqual(canonical_ir_bytes(syntax),
                                         canonical_ir_bytes(manual_syntax))
                        _, result = source_values(syntax, WORDS)
                        self.assertEqual(list(result),
                                         [(count * (2 * x + x * x)) % P for x in WORDS])


if __name__ == "__main__":
    unittest.main()
