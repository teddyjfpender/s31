"""Stable S31 text-front-end entry points.

The implementation lives in ``language/`` by compiler responsibility.
"""

from __future__ import annotations

import sys
from pathlib import Path
from typing import Any

S31_SOURCE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))

from language.parser import Parser, lex
from language.elaborate import Elaborator
from language.effects import TotalityChecker
from language.dead_code import prune_total_dead_nodes
from language.specialize import Compiler
from language.syntax import (Circuit, Expr, Function, FunctionType, SourceError,
                             StaticClosure, Statement, Token)


def compile_text(source: str, filename: str = "<source>") -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
    try:
        parser = Parser(source, filename)
        functions, circuit = parser.parse()
        if circuit.name in functions:
            raise SourceError(f"{filename}: circuit name conflicts with a function")
        Elaborator(functions, circuit, filename).check()
        TotalityChecker(functions, circuit, filename).check()
        relation, source_map = Compiler(functions, circuit, filename).compile()
        # The independently certified direct-gate grammar reconstructs every
        # arithmetic let and excludes enum declarations. Keep that contract
        # byte-for-byte stable while erasing dead total work in enum sources.
        return prune_total_dead_nodes(relation, source_map) if parser.sums else (relation, source_map)
    except RecursionError as exc:
        raise SourceError(f"{filename}: expression nesting limit exceeded") from exc


def compile_file(path: Path) -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
    return compile_text(path.read_text(), str(path))
