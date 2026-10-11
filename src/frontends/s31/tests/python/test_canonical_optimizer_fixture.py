"""Connect the Lean optimized-byte example to the production text and Zig IR paths.

The focused Zig test checks that `canonical.build` emits the pinned compact
legacy bytes and hashes them. This test checks that its relation input is the
actual normalized output of the pinned Lean source spelling, and that the
Lean byte literals match both production normalization and the Zig fixture.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))

from text_frontend import compile_text


LEAN = ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/OptimizedTextBytes.lean"
ZIG = S31 / "language/canonical.zig"
ZIG_COMPILER = S31 / "language/relation_compiler.zig"


def lean_token(name: str) -> bytes:
    source = LEAN.read_text()
    pattern = rf'def {re.escape(name)} : Token := token\s+("(?:\\.|[^"\\])*")'
    found = re.search(pattern, source)
    if found is None:
        raise AssertionError(f"missing pinned Lean token {name}")
    return json.loads(found.group(1)).encode("ascii")


def zig_test_literal(name: str, *, path: Path = ZIG,
                     test_name: str = "canonical reversed CSE exact legacy bytes and digest") -> bytes:
    source = path.read_text()
    test = source.split(f'test "{test_name}" {{', 1)[1]
    test = test.split('\n}', 1)[0]
    pattern = rf'const {re.escape(name)} =\s*\\\\([^\n]+)'
    found = re.search(pattern, test)
    if found is None:
        raise AssertionError(f"missing pinned Zig literal {name}")
    return found.group(1).encode("ascii")


class CanonicalOptimizerFixtureTests(unittest.TestCase):
    def test_lean_source_normalization_and_zig_ir_literals_agree(self) -> None:
        source = lean_token("reversedAndRepeatedBytes")
        expected_normalized = lean_token("reversedAndRepeatedNormalized")
        expected_canonical = lean_token("reversedAndRepeatedCanonical")
        relation, _ = compile_text(source.decode("ascii"))
        actual_normalized = (json.dumps(relation, indent=2, sort_keys=True)
                             + "\n").encode("ascii")
        self.assertEqual(actual_normalized, expected_normalized)
        self.assertEqual(json.loads(zig_test_literal("source_text")), relation)
        self.assertEqual(json.loads(zig_test_literal(
            "source_text", path=ZIG_COMPILER,
            test_name="direct CSE source-map reuses the canonical circuit span")), relation)
        self.assertEqual(zig_test_literal("expected_bytes"), expected_canonical)
        self.assertEqual(hashlib.sha256(expected_canonical).hexdigest(),
                         "2088c1bad15f2ba5b52f0214e9d3d66744b9c84aa6218aa336d8b337157e7132")

        compact = json.loads(expected_canonical)
        self.assertEqual(len(relation["nodes"]), 4)
        self.assertEqual([node["tag"] for node in compact["nodes"]],
                         ["input", "add", "mul", "add"])
        self.assertEqual(compact["public_outputs"], [{"name": "d", "id": 3}])
        self.assertEqual(compact["nodes"][3]["lhs"], 1)
        self.assertEqual(compact["nodes"][3]["rhs"], 2)

        changed_source = source.decode("ascii").replace("let d = b + a", "let d = b .* a")
        changed_relation, _ = compile_text(changed_source)
        self.assertNotEqual(changed_relation, relation)
        changed_compact = expected_canonical.replace(b'"name":"d","id":3',
                                                      b'"name":"d","id":2')
        self.assertNotEqual(hashlib.sha256(changed_compact).digest(),
                            hashlib.sha256(expected_canonical).digest())


if __name__ == "__main__":
    unittest.main()
