"""Independent bounded syntax for a unary, statically captured lambda.

The body is a pure arithmetic expression over four M31 lanes. It may contain
lexical ``let … in`` bindings, parentheses, addition and pointwise multiply.
Free names are resolved when ``fun`` is evaluated. Function values and lexical
bindings have no relation node; only their evaluated arithmetic emits gates.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


class UnsupportedStaticLambda(ValueError):
    """A lambda is outside the certified source fragment."""


@dataclass(frozen=True)
class LambdaName:
    name: str


@dataclass(frozen=True)
class LambdaBinary:
    operator: str
    left: LambdaExpr
    right: LambdaExpr


@dataclass(frozen=True)
class LambdaLet:
    name: str
    bound: LambdaExpr
    body: LambdaExpr


LambdaExpr = LambdaName | LambdaBinary | LambdaLet


@dataclass(frozen=True)
class StaticLambda:
    parameter: str
    body: LambdaExpr
    captures: tuple[tuple[str, str], ...]


MAX_EXPRESSION_DEPTH = 16
MAX_BODY_GATES = 16
PRECEDENCE = {"+": 10, ".*": 20}


def parse_static_lambda(tokens: list[str], valid_name: Callable[[str], bool],
                        capture: Callable[[str], str]) -> StaticLambda | None:
    """Parse a typed unary lambda and bind its free wire names immediately."""
    if not tokens or tokens[0] != "fun":
        return None
    cursor = 0
    gates = 0

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

    def expression(min_power: int = 0, depth: int = 0) -> LambdaExpr:
        nonlocal gates
        if depth > MAX_EXPRESSION_DEPTH:
            raise UnsupportedStaticLambda("static lambda expression is too deep")
        if cursor == len(tokens):
            raise UnsupportedStaticLambda("missing static lambda expression")
        if tokens[cursor] == "let":
            take("let")
            binder = take()
            if not valid_name(binder):
                raise UnsupportedStaticLambda("invalid static lambda let binder")
            take("=")
            bound = expression(depth=depth + 1)
            take("in")
            body = expression(depth=depth + 1)
            lhs: LambdaExpr = LambdaLet(binder, bound, body)
        elif tokens[cursor] == "(":
            take("(")
            lhs = expression(depth=depth + 1)
            take(")")
        else:
            name = take()
            if not valid_name(name):
                raise UnsupportedStaticLambda("static lambda expects a wire name")
            lhs = LambdaName(name)
        while cursor < len(tokens) and tokens[cursor] in PRECEDENCE:
            operator = tokens[cursor]
            power = PRECEDENCE[operator]
            if power < min_power:
                break
            take(operator)
            right = expression(power + 1, depth + 1)
            gates += 1
            if gates > MAX_BODY_GATES:
                raise UnsupportedStaticLambda("static lambda body exceeds 16 gates")
            lhs = LambdaBinary(operator, lhs, right)
        return lhs

    body = expression()
    if cursor != len(tokens):
        raise UnsupportedStaticLambda("trailing tokens in static lambda")

    captures: dict[str, str] = {}

    def bind_free(expr: LambdaExpr, bound: frozenset[str]) -> None:
        if isinstance(expr, LambdaName):
            if expr.name not in bound and expr.name not in captures:
                captures[expr.name] = capture(expr.name)
        elif isinstance(expr, LambdaBinary):
            bind_free(expr.left, bound)
            bind_free(expr.right, bound)
        else:
            bind_free(expr.bound, bound)
            bind_free(expr.body, bound | {expr.name})

    bind_free(body, frozenset({parameter}))
    return StaticLambda(parameter, body, tuple(captures.items()))
