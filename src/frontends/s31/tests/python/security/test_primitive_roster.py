"""Keep relation opcodes, canonical identities, Lean, and the oracle aligned.

Canonical Tag numbers are serialized into program identities. An inserted or
reordered opcode can silently change an existing program's identity, even if
both the compiler and verifier still build successfully.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))

import oracle  # noqa: E402


def zig_enum(path: Path, name: str) -> tuple[str, ...]:
    source = path.read_text()
    matches = re.findall(rf"pub const {name} = enum \{{([^}}]*)\}};", source)
    if len(matches) != 1:
        raise AssertionError(f"expected one {name} enum in {path}")
    names = tuple(part.strip() for part in matches[0].split(","))
    if not names or any(not re.fullmatch(r"[a-z][a-z0-9_]*", part) for part in names):
        raise AssertionError(f"malformed {name} enum in {path}")
    if len(names) != len(set(names)):
        raise AssertionError(f"duplicate {name} enum member in {path}")
    return names


class PrimitiveRosterTests(unittest.TestCase):
    def test_append_only_canonical_identity_and_all_consumers(self) -> None:
        language = S31 / "language"
        ops = zig_enum(language / "relation.zig", "Op")
        tags = zig_enum(language / "canonical.zig", "Tag")
        self.assertEqual(tags, ("input", *ops))

        # This is the shipped opcode prefix before the native M31 sub gate.
        # New operations must append after it to preserve all earlier tags.
        self.assertGreaterEqual(len(ops), 57)
        self.assertEqual(ops[56], "sub")
        self.assertEqual(hashlib.sha256("\0".join(ops[:56]).encode()).hexdigest(),
                         "72a34049afb668cd916fb32ef7fb54e9485519d15b8a363c39275100539d6882")

        formal = json.loads((ROOT / "formal/s31/source-bindings.json").read_text())
        self.assertEqual(tuple(formal["ops"]), ops)
        self.assertEqual(set(ops), oracle._OPS)


if __name__ == "__main__":
    unittest.main()
