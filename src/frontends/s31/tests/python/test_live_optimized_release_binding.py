"""The Lean byte fixture must be the exact checked-in optimized release source."""

from __future__ import annotations

import json
import re
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.context import lower_text  # noqa: E402
from package.correspondence import canonical_ir_bytes, parse_source_optimized  # noqa: E402

SOURCE = S31 / "examples/functional/release_optimized4/functional.s31"
LEAN = ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/LiveOptimizedRelease.lean"


def lean_token(name: str) -> bytes:
    code = LEAN.read_text()
    match = re.search(
        rf"def {re.escape(name)} : SSATextBytes\.Token := SSATextBytes\.token\s*\n\s*(\"(?:[^\"\\]|\\.)*\")",
        code,
    )
    if match is None:
        raise AssertionError(f"missing exact Lean token {name}")
    return json.loads(match.group(1)).encode("ascii")


class LiveOptimizedReleaseBindingTests(unittest.TestCase):
    def test_source_relation_and_compact_ir_bytes_match_lean(self) -> None:
        source = SOURCE.read_bytes()
        _, normalized, _ = lower_text(SOURCE)
        _, syntax = parse_source_optimized(source)
        self.assertEqual(lean_token("sourceBytes"), source)
        self.assertEqual(lean_token("normalizedBytes"), normalized)
        self.assertEqual(lean_token("canonicalBytes"), canonical_ir_bytes(syntax))
        self.assertEqual(syntax["source_to_canonical"], [0, 1, 2, 3, 3, 4])


if __name__ == "__main__":
    unittest.main()
