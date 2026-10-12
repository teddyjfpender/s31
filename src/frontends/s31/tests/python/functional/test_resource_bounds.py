"""Compact source must not expand into unbounded abstract or relation work."""

from __future__ import annotations

import sys
import tracemalloc
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from text_frontend import SourceError, compile_text


def nested_records() -> str:
    return ("struct A0 { x: [m31; 1] };\n" + "".join(
        f"struct A{i} {{ l: A{i-1}, r: A{i-1} }};\n" for i in range(1, 11)))


class ResourceBoundTests(unittest.TestCase):
    def test_aggregate_input_words_rejected_before_relation_expansion(self) -> None:
        def program(count: int) -> str:
            params = ", ".join(f"private x{i}: [m31; 4096]" for i in range(count))
            return f"circuit c({params}) -> public [m31; 1] {{ splat<1>(0_m31) }}"

        admitted, _ = compile_text(program(16))
        self.assertEqual(sum(item["length"] for item in admitted["inputs"]), 65_536)
        with self.assertRaisesRegex(SourceError,
                                    r"aggregate relation inputs exceed 65536 words"):
            compile_text(program(17))

    def test_repeated_parameter_type_shares_abstract_effect_shape(self) -> None:
        source = (nested_records() + "fn unused(" + ", ".join(
            f"p{i}: A10" for i in range(500)) + ") -> [m31; 1] { splat<1>(0_m31) }\n"
            "circuit c(public x: [m31; 1]) -> public [m31; 1] { x }")
        tracemalloc.start()
        tracemalloc.reset_peak()
        try:
            relation, _ = compile_text(source)
            _, peak = tracemalloc.get_traced_memory()
        finally:
            tracemalloc.stop()
        self.assertEqual(relation["nodes"], [])
        self.assertLess(peak, 8 * 1024 * 1024,
                        "a repeated immutable source type expanded per parameter")

    def test_record_boundary_leaf_budget_precedes_input_expansion(self) -> None:
        # A10 has 1024 leaves. Even one result leaf exceeds the v2 ABI cap.
        rejected = (nested_records() + "circuit c(private p: A10) -> public [m31; 1] "
                    "{ splat<1>(0_m31) }")
        with self.assertRaisesRegex(SourceError,
                                    r"^<source>:[0-9]+:[0-9]+: public record v2 boundary exceeds 1024 leaves"):
            compile_text(rejected)

        # Stop at the first excess leaf even when a compact signature reuses
        # the same deep record type many times.
        repeated = (nested_records() + "circuit c(" + ", ".join(
            f"private p{i}: A10" for i in range(1000))
            + ") -> public [m31; 1] { splat<1>(0_m31) }")
        with self.assertRaisesRegex(SourceError, r"public record v2 boundary exceeds 1024 leaves"):
            compile_text(repeated)

        # 512+256+...+1 = 1023 private leaves; the result is leaf 1024.
        fields = ", ".join(f"f{i}: A{i}" for i in range(9, -1, -1))
        admitted = (nested_records() + f"struct Near {{ {fields} }};\n"
                    "circuit c(private p: Near) -> public [m31; 1] { splat<1>(0_m31) }")
        relation, _ = compile_text(admitted)
        self.assertEqual(len(relation["inputs"]), 1023)
        self.assertEqual(len(relation["public_abi"]["result"]["leaves"]), 1)

    def test_repeated_product_assertions_are_deduplicated_and_bounded(self) -> None:
        prelude = nested_records()
        accepted = (prelude + "circuit c(private a: A2, private b: A2) -> public [m31; 1] {\n"
                    + "assert_eq(a, b);\n" * 3 + "splat<1>(0_m31) }")
        relation, _ = compile_text(accepted)
        self.assertEqual(len(relation["assertions"]), 4)

        # A8 has 256 leaves, so 391 source assertions exceed the 100k
        # expansion budget even though repeated equality is idempotent.
        oversized = (prelude + "circuit c(private a: A8, private b: A8) -> public [m31; 1] {\n"
                     + "assert_eq(a, b);\n" * 391 + "splat<1>(0_m31) }")
        with self.assertRaisesRegex(SourceError,
                                    r"^<source>:[0-9]+:[0-9]+: assertion expansion limit exceeded"):
            compile_text(oversized)


if __name__ == "__main__":
    unittest.main()
