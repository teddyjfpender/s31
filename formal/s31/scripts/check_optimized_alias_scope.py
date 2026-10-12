#!/usr/bin/env python3
"""Check optimized alias fixtures against independent and production parsers."""

from __future__ import annotations

import ast
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))
from package.correspondence import canonical_ir_bytes, parse_source_optimized  # noqa: E402
from text_frontend import compile_text  # noqa: E402

FIXTURE = ROOT / "formal/s31/fixtures/correspondence/optimized_alias_gap.s31"
AUDIT = ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/OptimizedDecodedTraceAudit.lean"
MODEL = ROOT / "formal/s31/S31/Gadgets/Functional/Correspondence/OptimizedTextBytes.lean"


def lean_literal(text: str, name: str) -> str:
    match = re.search(r'def ' + name + r' : Token := token\s+("(?:[^"\\]|\\.)*")', text)
    assert match is not None, f"Lean {name} literal was not found"
    return ast.literal_eval(match.group(1))


def main() -> None:
    source = FIXTURE.read_bytes()
    relation, syntax = parse_source_optimized(source)
    assert [node["name"] for node in relation["nodes"]] == ["a", "b"]
    assert len(syntax["instructions"]) == 2
    assert syntax["output"] == 2
    assert syntax["source_to_canonical"] == [0, 1, 2]
    compiled, _ = compile_text(source.decode("ascii"))
    assert compiled == relation

    # Keep the executable Lean counterexample exactly paired with this fixture.
    lean = AUDIT.read_text()
    expected_tokens = source.decode("ascii").split()
    actual_tokens = lean_literal(lean, "aliasLetBytes").split()
    assert expected_tokens == actual_tokens, "Lean alias literal differs from fixture"
    assert "theorem alias_let_inside_modeled_grammar" in lean
    assert "theorem optimized_alias_exact_byte_triple" in lean

    model = MODEL.read_text()
    optimized_source = lean_literal(model, "aliasedReversedSource")
    optimized_relation, optimized_syntax = parse_source_optimized(
        optimized_source.encode("ascii"))
    produced, _ = compile_text(optimized_source)
    assert optimized_relation == produced
    assert json.dumps(produced, sort_keys=True, indent=2) + "\n" == lean_literal(
        model, "reversedAndRepeatedNormalized")
    assert canonical_ir_bytes(optimized_syntax).decode("ascii") == lean_literal(
        model, "reversedAndRepeatedCanonical")
    print("optimized aliases admitted by Lean; Python and production bytes agree")


if __name__ == "__main__":
    main()
