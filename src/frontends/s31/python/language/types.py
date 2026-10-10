"""Source-only type terms erased before the normalized relation boundary."""

from __future__ import annotations

from dataclasses import dataclass

from s31_stdlib import Type
from language.syntax import FunctionType, TupleType


@dataclass(frozen=True)
class StaticArray:
    """A fixed source array; its elements are circuit types or nested arrays."""

    elements: tuple[SourceType, ...]


@dataclass(frozen=True)
class FieldLiteral:
    """A canonical M31 literal usable only at compile time, for example in splat."""

    value: int


SourceType = Type | FunctionType | TupleType | StaticArray | FieldLiteral


def is_circuit(typ: SourceType) -> bool:
    return isinstance(typ, Type)
