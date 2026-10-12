"""Exact one-gate static helper grammar for the v2 direct-gate certificate.

This parser is independent of the production text parser. Its parameters are
compile-time names; a call selects existing circuit wires and emits exactly
one addition or pointwise multiplication node. No function value is carried
into the normalized relation or native AIR.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


class UnsupportedStaticHelper(ValueError):
    """The optional named function is outside the certified source fragment."""


@dataclass(frozen=True)
class StaticHelper:
    name: str
    params: tuple[str, ...]
    operator: str
    left_index: int
    right_index: int


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
    left = take()
    operator = take()
    right = take()
    take("}")
    if left not in params or right not in params or operator not in {"+", ".*"}:
        raise UnsupportedStaticHelper("helper body must be one binary parameter operation")
    return (StaticHelper(helper_name, tuple(params), operator,
                         params.index(left), params.index(right)), tokens[cursor:])
