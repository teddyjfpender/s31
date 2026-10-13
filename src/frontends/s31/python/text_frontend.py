"""Stable S31 text-front-end entry points.

The implementation lives in ``language/`` by compiler responsibility.
"""

from __future__ import annotations

import copy
import sys
from pathlib import Path
from typing import Any

S31_SOURCE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))

from language.parser import Parser, lex
from language.elaborate import Elaborator
from language.effects import TotalityChecker
from language.dead_code import prune_total_dead_nodes
from language.prune_certificate import PruneCertificateError, verify_pruning
from language.specialize import Compiler
from language.syntax import (Circuit, Expr, Function, FunctionType, SourceError,
                             StaticClosure, Statement, Token)


def _certified_prune(
    relation: dict[str, Any], source_map: dict[str, dict[str, int]],
) -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
    # Snapshot before invoking the optimizer. An accidental in-place rewrite
    # must not make its own before/after certificate vacuous.
    original = copy.deepcopy(relation)
    original_map = copy.deepcopy(source_map)
    pruned, locations = prune_total_dead_nodes(relation, source_map)
    verify_pruning(original, original_map, pruned, locations)
    return pruned, locations


def compile_text(source: str, filename: str = "<source>") -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
    try:
        parser = Parser(source, filename)
        functions, circuit = parser.parse()
        if circuit.name in functions:
            raise SourceError(f"{filename}: circuit name conflicts with a function")
        Elaborator(functions, circuit, filename).check()
        TotalityChecker(functions, circuit, filename).check()
        baseline = Compiler(functions, circuit, filename)
        relation, source_map = baseline.compile()
        # The independently certified direct-gate grammar reconstructs every
        # arithmetic let and excludes enum declarations. Keep that contract
        # byte-for-byte stable while erasing dead total work in enum and
        # static-power sources. Only pure, total field nodes can be erased.
        if parser.sums or baseline.builder.static_power_calls:
            relation, source_map = _certified_prune(relation, source_map)
        if not baseline.builder.static_power_opportunities:
            return relation, source_map

        # Compile an independent fused candidate and retain it only if the
        # complete reachable relation has fewer nodes. This accounts for
        # intermediate powers that remain live through another output or an
        # assertion; those cases must never pay for duplicated chains.
        try:
            fused = Compiler(functions, circuit, filename, fuse_static_powers=True)
            fused_relation, fused_map = fused.compile()
        except SourceError as exc:
            if "relation item expansion limit exceeded" not in str(exc):
                raise
            return relation, source_map
        fused_relation, fused_map = _certified_prune(fused_relation, fused_map)
        return ((fused_relation, fused_map) if len(fused_relation["nodes"]) < len(relation["nodes"])
                else (relation, source_map))
    except PruneCertificateError as exc:
        raise SourceError(f"{filename}: unsafe dead-code pruning: {exc}") from exc
    except RecursionError as exc:
        raise SourceError(f"{filename}: expression nesting limit exceeded") from exc


def compile_file(path: Path) -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
    return compile_text(path.read_text(), str(path))
