"""Independent static function grammar for the v2 gate certificate.

Functions are monomorphic. A parameter may be a four-lane field value or a
unary function over that value. Calls may target earlier declarations or a
function parameter; concrete named function values resolve at compile time.
The parser retains source binders; the package checker separately replays
applications as ordinary circuit gates.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


class UnsupportedStaticHelper(ValueError):
    """A function is outside the certified source fragment."""


@dataclass(frozen=True)
class StaticExpr:
    kind: str  # gate, call, or ref
    value: str  # arithmetic operator or called function name
    operands: tuple[str, ...]


@dataclass(frozen=True)
class StaticStep:
    name: str
    expression: StaticExpr


@dataclass(frozen=True)
class StaticParam:
    name: str
    kind: str  # array or unary_function


@dataclass(frozen=True)
class StaticHelper:
    name: str
    params: tuple[StaticParam, ...]
    statements: tuple[StaticStep, ...]
    body: StaticExpr


def peel_static_helpers(tokens: list[str], valid_name: Callable[[str], bool]) -> tuple[dict[str, StaticHelper], list[str]]:
    """Consume up to eight pure functions before the circuit token stream."""
    cursor = 0
    helpers: dict[str, StaticHelper] = {}

    def take(expected: str | None = None) -> str:
        nonlocal cursor
        if cursor >= len(tokens):
            raise UnsupportedStaticHelper("incomplete static function declaration")
        found = tokens[cursor]
        cursor += 1
        if expected is not None and found != expected:
            raise UnsupportedStaticHelper(f"expected {expected!r} in static function")
        return found

    def name() -> str:
        found = take()
        if not valid_name(found):
            raise UnsupportedStaticHelper("invalid static function identifier")
        return found

    def lane_type() -> None:
        for expected in ("[", "m31", ";", "4", "]"):
            take(expected)

    def parameter_type() -> str:
        if tokens[cursor:cursor + 1] != ["Fn"]:
            lane_type()
            return "array"
        take("Fn")
        take("(")
        lane_type()
        take(")")
        take("->")
        lane_type()
        return "unary_function"

    while tokens[cursor:cursor + 1] == ["fn"]:
        if len(helpers) >= 8:
            raise UnsupportedStaticHelper("more than eight static functions")
        take("fn")
        helper_name = name()
        if helper_name in helpers:
            raise UnsupportedStaticHelper("duplicate static function")
        take("(")
        params: list[StaticParam] = []
        while True:
            param = name()
            if param == helper_name or param in (item.name for item in params) or param in helpers:
                raise UnsupportedStaticHelper("duplicate or shadowed function parameter")
            take(":")
            params.append(StaticParam(param, parameter_type()))
            if len(params) > 2:
                raise UnsupportedStaticHelper("function accepts at most two parameters")
            if tokens[cursor:cursor + 1] != [","]:
                break
            take(",")
        take(")")
        take("->")
        lane_type()
        take("{")
        available = {param.name: param.kind for param in params}
        statements: list[StaticStep] = []

        def callable_signature(callee: str) -> tuple[str, ...]:
            if callee in helpers:
                return tuple(param.kind for param in helpers[callee].params)
            if available.get(callee) == "unary_function":
                return ("array",)
            raise UnsupportedStaticHelper("function call must target an earlier declaration or function parameter")

        def argument_kind(argument: str, expected: str) -> bool:
            if available.get(argument) == expected:
                return True
            return (expected == "unary_function" and argument in helpers and
                    len(helpers[argument].params) == 1 and
                    helpers[argument].params[0].kind == "array")

        def expression() -> StaticExpr:
            first = name()
            if tokens[cursor:cursor + 1] == ["("]:
                expected_kinds = callable_signature(first)
                take("(")
                args: list[str] = []
                while True:
                    argument = name()
                    args.append(argument)
                    if tokens[cursor:cursor + 1] != [","]:
                        break
                    take(",")
                take(")")
                if len(args) != len(expected_kinds):
                    raise UnsupportedStaticHelper("function call argument count differs")
                if any(not argument_kind(argument, kind)
                       for argument, kind in zip(args, expected_kinds)):
                    raise UnsupportedStaticHelper("function call argument type differs")
                return StaticExpr("call", first, tuple(args))
            if tokens[cursor:cursor + 1] in (["+"], [".*"]):
                operator = take()
                second = name()
                if available.get(first) != "array" or available.get(second) != "array":
                    raise UnsupportedStaticHelper("function gate needs earlier wires")
                return StaticExpr("gate", operator, (first, second))
            if available.get(first) != "array":
                raise UnsupportedStaticHelper("unbound function result")
            return StaticExpr("ref", "", (first,))

        while tokens[cursor:cursor + 1] == ["let"]:
            take("let")
            local = name()
            if local in available or local == helper_name or local in helpers:
                raise UnsupportedStaticHelper("duplicate or shadowed function local")
            take("=")
            bound = expression()
            if bound.kind == "ref":
                raise UnsupportedStaticHelper("function local must produce arithmetic")
            take(";")
            statements.append(StaticStep(local, bound))
            if len(statements) > 16:
                raise UnsupportedStaticHelper("helper exceeds 16 arithmetic operations")
            available[local] = "array"

        body = expression()
        if body.kind == "ref" and (not statements or body.operands[0] != statements[-1].name):
            raise UnsupportedStaticHelper("helper must return its last operation")
        take("}")
        helpers[helper_name] = StaticHelper(helper_name, tuple(params), tuple(statements), body)

    return helpers, tokens[cursor:]
