"""Exact straight-line static helper grammar for the v2 gate certificate.

This parser is independent of the production text parser. Its parameters are
compile-time names; a call selects existing wires and emits its additions or
pointwise multiplications in declaration order. No function value is carried
into the normalized relation or native AIR.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


class UnsupportedStaticHelper(ValueError):
    """The optional named function is outside the certified source fragment."""


@dataclass(frozen=True)
class StaticGate:
    name: str | None
    left: str
    operator: str
    right: str


@dataclass(frozen=True)
class StaticHelper:
    name: str
    params: tuple[str, ...]
    gates: tuple[StaticGate, ...]


def peel_static_helper(tokens: list[str], valid_name: Callable[[str], bool]) -> tuple[StaticHelper | None, list[str]]:
    """Consume one pure monomorphic helper, leaving the circuit token stream."""
    if not tokens or tokens[0] != "fn":
        return None, tokens
    cursor = 0

    def take(expected: str | None = None) -> str:
        nonlocal cursor
        if cursor >= len(tokens):
            raise UnsupportedStaticHelper("incomplete static helper declaration")
        found = tokens[cursor]
        cursor += 1
        if expected is not None and found != expected:
            raise UnsupportedStaticHelper(f"expected {expected!r} in static helper")
        return found

    def name() -> str:
        found = take()
        if not valid_name(found):
            raise UnsupportedStaticHelper("invalid static helper identifier")
        return found

    def lane_type() -> None:
        for expected in ("[", "m31", ";", "4", "]"):
            take(expected)

    take("fn")
    helper_name = name()
    take("(")
    params: list[str] = []
    while True:
        param = name()
        if param == helper_name or param in params:
            raise UnsupportedStaticHelper("duplicate or shadowed helper parameter")
        take(":")
        lane_type()
        params.append(param)
        if len(params) > 2:
            raise UnsupportedStaticHelper("helper accepts at most two parameters")
        if tokens[cursor:cursor + 1] != [","]:
            break
        take(",")
    take(")")
    take("->")
    lane_type()
    take("{")
    gates: list[StaticGate] = []
    available = set(params)

    def gate(result_name: str | None) -> None:
        left, operator, right = take(), take(), take()
        if left not in available or right not in available or operator not in {"+", ".*"}:
            raise UnsupportedStaticHelper("helper gate needs earlier wires and one binary operation")
        gates.append(StaticGate(result_name, left, operator, right))
        if len(gates) > 16:
            raise UnsupportedStaticHelper("helper exceeds 16 arithmetic operations")

    while tokens[cursor:cursor + 1] == ["let"]:
        take("let")
        local = name()
        if local in available or local == helper_name:
            raise UnsupportedStaticHelper("duplicate or shadowed helper local")
        take("=")
        gate(local)
        take(";")
        available.add(local)

    if (len(tokens) >= cursor + 2 and tokens[cursor + 1] == "}" and
            tokens[cursor] in available):
        returned = take()
        if not gates or gates[-1].name != returned:
            raise UnsupportedStaticHelper("helper must return its last operation")
    else:
        gate(None)
    take("}")
    return StaticHelper(helper_name, tuple(params), tuple(gates)), tokens[cursor:]
