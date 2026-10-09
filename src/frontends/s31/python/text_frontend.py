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
from language.specialize import Compiler
from language.syntax import (Circuit, Expr, Function, FunctionType, SourceError,
                             StaticClosure, Statement, Token)


def compile_text(source: str, filename: str = "<source>") -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
    try:
        functions, circuit = Parser(source, filename).parse()
        if circuit.name in functions:
            raise SourceError(f"{filename}: circuit name conflicts with a function")
        return Compiler(functions, circuit, filename).compile()
    except RecursionError as exc:
        raise SourceError(f"{filename}: expression nesting limit exceeded") from exc


def compile_file(path: Path) -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
    return compile_text(path.read_text(), str(path))
