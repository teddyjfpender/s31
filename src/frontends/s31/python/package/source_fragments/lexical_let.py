"""Independent bounded parsing of expression-level ``let x = e in body``.

This is a source-only binder. The checker interprets the bound expression
eagerly, extends one lexical environment, and gives the body its caller's
desired result name. The parser does not import the production language AST.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable


class UnsupportedLexicalLet(ValueError):
    """The expression is outside the certified lexical-let fragment."""


@dataclass(frozen=True)
class Atom:
    tokens: tuple[str, ...]


@dataclass(frozen=True)
class Let:
    name: str
    bound: Atom | Let
    body: Atom | Let


Expression = Atom | Let
MAX_LET_DEPTH = 16


def _peel_parentheses(tokens: list[str]) -> list[str]:
    while len(tokens) >= 2 and tokens[0] == "(":
        depth = 0
        for index, token in enumerate(tokens):
            depth += (token == "(") - (token == ")")
            if depth < 0:
                raise UnsupportedLexicalLet("unbalanced lexical expression")
            if depth == 0:
                if index != len(tokens) - 1:
                    return tokens
                tokens = tokens[1:-1]
                break
        else:
            raise UnsupportedLexicalLet("unbalanced lexical expression")
    return tokens


def parse_expression(tokens: list[str], valid_name: Callable[[str], bool], depth: int = 0) -> Expression:
    """Parse right-associative lets with one direct gate, call or reference leaf."""
    if depth > MAX_LET_DEPTH:
        raise UnsupportedLexicalLet("lexical let nesting exceeds 16")
    tokens = _peel_parentheses(tokens)
    if not tokens:
        raise UnsupportedLexicalLet("empty lexical expression")
    if tokens[0] != "let":
        return Atom(tuple(tokens))
    if len(tokens) < 6 or not valid_name(tokens[1]) or tokens[2] != "=":
        raise UnsupportedLexicalLet("malformed lexical let binder")
    parentheses = 0
    nested_lets = 0
    separator = None
    for index in range(3, len(tokens)):
        token = tokens[index]
        parentheses += (token == "(") - (token == ")")
        if parentheses < 0:
            raise UnsupportedLexicalLet("unbalanced lexical expression")
        if parentheses != 0:
            continue
        if token == "let":
            nested_lets += 1
        elif token == "in":
            if nested_lets:
                nested_lets -= 1
            else:
                separator = index
                break
    if separator is None or separator == 3 or separator == len(tokens) - 1:
        raise UnsupportedLexicalLet("lexical let needs a bound value and an in body")
    return Let(tokens[1],
               parse_expression(tokens[3:separator], valid_name, depth + 1),
               parse_expression(tokens[separator + 1:], valid_name, depth + 1))
