"""Independent bounded parser for a unary, statically captured lambda.

The accepted body is one add or pointwise multiply over four M31 lanes.
Capture resolution happens when ``fun`` is evaluated, before later source
bindings exist. The resulting value has no relation node of its own.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


class UnsupportedStaticLambda(ValueError):
    """A lambda is outside the certified source fragment."""


@dataclass(frozen=True)
class StaticLambda:
    parameter: str
    left: str
    operator: str
    right: str
    captures: tuple[tuple[str, str], ...]


def parse_static_lambda(tokens: list[str], valid_name: Callable[[str], bool],
                        capture: Callable[[str], str]) -> StaticLambda | None:
    """Parse ``fun(v: [m31; 4]) -> [m31; 4] => v op captured`` exactly."""
    if not tokens or tokens[0] != "fun":
        return None
    cursor = 0

    def take(expected: str | None = None) -> str:
        nonlocal cursor
        if cursor == len(tokens):
            raise UnsupportedStaticLambda("incomplete static lambda")
        found = tokens[cursor]
        cursor += 1
        if expected is not None and found != expected:
            raise UnsupportedStaticLambda(f"expected {expected!r} in static lambda")
        return found

    take("fun")
    take("(")
    parameter = take()
    if not valid_name(parameter):
        raise UnsupportedStaticLambda("invalid static lambda parameter")
    take(":")
    for item in ("[", "m31", ";", "4", "]", ")", "->",
                 "[", "m31", ";", "4", "]", "=>"):
        take(item)
    body = tokens[cursor:]
    if len(body) != 3 or body[1] not in {"+", ".*"} or not all(
            valid_name(body[index]) for index in (0, 2)):
        raise UnsupportedStaticLambda("static lambda body must be one binary gate")
    captures: dict[str, str] = {}
    for operand in (body[0], body[2]):
        if operand != parameter and operand not in captures:
            captures[operand] = capture(operand)
    return StaticLambda(parameter, body[0], body[1], body[2],
                        tuple(captures.items()))
