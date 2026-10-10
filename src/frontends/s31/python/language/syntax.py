"""Location-carrying syntax and static function types."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from s31_stdlib import Type


class SourceError(ValueError):
    pass


@dataclass(frozen=True)
class Token:
    kind: str
    text: str
    line: int
    column: int


@dataclass(frozen=True)
class FunctionType:
    """A compile-time function type; no relation or AIR representation."""

    params: tuple[Type | FunctionType | TupleType, ...]
    result: Type | FunctionType | TupleType


@dataclass(frozen=True)
class TupleType:
    """A compile-time product of typed values, erased before AIR lowering."""

    elements: tuple[Type | FunctionType | TupleType, ...]


@dataclass(frozen=True)
class Expr:
    kind: str
    value: str
    args: tuple[Expr, ...]
    token: Token
    generic: int | None = None
    params: tuple[tuple[str, Type | FunctionType | TupleType], ...] = ()
    result_type: Type | FunctionType | TupleType | None = None


@dataclass(frozen=True)
class Statement:
    kind: str
    name: str
    args: tuple[Expr, ...]
    token: Token


@dataclass(frozen=True)
class Function:
    name: str
    params: tuple[tuple[str, Type | FunctionType | TupleType], ...]
    result: Type | FunctionType | TupleType
    statements: tuple[Statement, ...]
    body: Expr


@dataclass(frozen=True)
class Circuit:
    name: str
    params: tuple[tuple[str, Type, str], ...]
    result: Type
    statements: tuple[Statement, ...]
    body: Expr
    token: Token
    proof_mode: str = "transparent"


@dataclass(frozen=True)
class StaticClosure:
    """Lexically scoped source function erased by compile-time application."""

    signature: FunctionType
    names: tuple[str, ...]
    body: Expr
    captured: dict[str, Any]


@dataclass(frozen=True)
class StaticNamedFunction:
    """A top-level function reference erased by compile-time application."""

    name: str
    signature: FunctionType


@dataclass(frozen=True)
class StaticTuple:
    """Tuple of source values; components may still be circuit references."""

    signature: TupleType
    elements: tuple[Any, ...]
