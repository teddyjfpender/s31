"""Independent static function grammar for the v2 gate certificate.

Functions are monomorphic. A parameter and result may be a four-lane field
value or a unary function over that value. Calls may target earlier
declarations or a function parameter; concrete named function values and
returned closures resolve at compile time.
The parser retains source binders; the package checker separately replays
applications as ordinary circuit gates.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable

from package.source_fragments.static_lambda import (StaticLambda, UnsupportedStaticLambda,
                                                    parse_static_lambda)


class UnsupportedStaticHelper(ValueError):
    """A function is outside the certified source fragment."""


@dataclass(frozen=True)
class StaticExpr:
    kind: str  # gate, call, ref, named_function, or lambda
    value: str  # arithmetic operator or called function name
    operands: tuple[str, ...]
    lambda_body: StaticLambda | None = None


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
    result_kind: str
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
        if tokens[cursor:cursor + 1] != [")"]:
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
        result_kind = parameter_type()
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
                    helpers[argument].params[0].kind == "array" and
                    helpers[argument].result_kind == "array")

        def expression_kind(expr: StaticExpr) -> str:
            if expr.kind == "gate":
                return "array"
            if expr.kind in {"lambda", "named_function"}:
                return "unary_function"
            if expr.kind == "call":
                return (helpers[expr.value].result_kind if expr.value in helpers
                        else "array")
            return available[expr.operands[0]]

        def expression() -> StaticExpr:
            if tokens[cursor:cursor + 1] == ["fun"]:
                start = cursor
                depth = 0
                while cursor < len(tokens):
                    upcoming = tokens[cursor]
                    if depth == 0 and upcoming in {";", "}"}:
                        break
                    token = take()
                    depth += (token in {"(", "[", "{"}) - (token in {")", "]", "}"})
                    if depth < 0:
                        raise UnsupportedStaticHelper("unbalanced static lambda in function")
                if depth != 0:
                    raise UnsupportedStaticHelper("unbalanced static lambda in function")
                def capture_array(captured: str) -> str:
                    if available.get(captured) != "array":
                        raise UnsupportedStaticHelper("lambda captures an unbound array")
                    return captured
                try:
                    parsed = parse_static_lambda(
                        tokens[start:cursor], valid_name, capture_array,
                    )
                except UnsupportedStaticLambda as exc:
                    raise UnsupportedStaticHelper(str(exc)) from exc
                assert parsed is not None
                return StaticExpr("lambda", "", (), parsed)
            first = name()
            if tokens[cursor:cursor + 1] == ["("]:
                expected_kinds = callable_signature(first)
                take("(")
                args: list[str] = []
                if tokens[cursor:cursor + 1] != [")"]:
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
            if first in helpers and argument_kind(first, "unary_function"):
                return StaticExpr("named_function", first, ())
            if first not in available:
                raise UnsupportedStaticHelper("unbound function result")
            return StaticExpr("ref", "", (first,))

        while tokens[cursor:cursor + 1] == ["let"]:
            take("let")
            local = name()
            if local in available or local == helper_name or local in helpers:
                raise UnsupportedStaticHelper("duplicate or shadowed function local")
            take("=")
            bound = expression()
            take(";")
            statements.append(StaticStep(local, bound))
            if len(statements) > 16:
                raise UnsupportedStaticHelper("helper exceeds 16 arithmetic operations")
            available[local] = expression_kind(bound)

        body = expression()
        if expression_kind(body) != result_kind:
            raise UnsupportedStaticHelper("function result type differs")
        if (result_kind == "array" and body.kind == "ref" and
                (not statements or body.operands[0] != statements[-1].name)):
            raise UnsupportedStaticHelper("helper must return its last operation")
        take("}")
        helpers[helper_name] = StaticHelper(helper_name, tuple(params), result_kind,
                                            tuple(statements), body)

    return helpers, tokens[cursor:]
