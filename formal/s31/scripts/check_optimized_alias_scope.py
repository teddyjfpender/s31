#!/usr/bin/env python3
"""Show a v3 parser-admitted alias source outside the current Lean grammar."""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))
from package.correspondence import parse_source_optimized  # noqa: E402

FIXTURE = ROOT / "formal/s31/fixtures/correspondence/optimized_alias_gap.s31"
AUDIT = ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/OptimizedDecodedTraceAudit.lean"


def main() -> None:
    source = FIXTURE.read_bytes()
    relation, syntax = parse_source_optimized(source)
    assert [node["name"] for node in relation["nodes"]] == ["a", "b"]
    assert len(syntax["instructions"]) == 2
    assert syntax["output"] == 2
    assert syntax["source_to_canonical"] == [0, 1, 2]

    # Keep the executable Lean counterexample exactly paired with this fixture.
    lean = AUDIT.read_text()
    match = re.search(r'def aliasLetBytes : Token := token\s*"([^"\\]+)"', lean)
    assert match is not None, "Lean audit alias literal was not found"
    expected_tokens = source.decode("ascii").split()
    actual_tokens = match.group(1).split()
    assert expected_tokens == actual_tokens, "Lean alias literal differs from fixture"
    print("optimized Python alias source admitted; Lean audit literal matches fixture")


if __name__ == "__main__":
    main()
