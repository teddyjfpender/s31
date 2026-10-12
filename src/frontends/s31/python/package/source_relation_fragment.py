"""Independent source-to-normalized-relation check for a bounded S31 fragment.

Capability: ``source-to-relation-only``. This module does not certify the
canonical optimizer, generated circuit, AIR, private boundary, or proof.
It deliberately does not import the production lexer, elaborator, compiler,
relation validator, or package verifier.
"""

from __future__ import annotations

import hashlib
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from package.correspondence import (MAX_RELATION_NAME_CHARS, MAX_SOURCE_BYTES,
                                    M31_MODULUS, PLAIN_BUILTIN_NAMES,
                                    SOURCE_KEYWORDS, parse_canonical_json)

CAPABILITY = "source-to-relation-only"
TOKEN = re.compile(r"[ \t\n\v\f\r]+|//[^\n]*|->|\.\*|[()\[\];:{}=+,<>-]|[A-Za-z_][A-Za-z_0-9]*|[0-9]+_m31|[0-9]+")
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")
LITERAL = re.compile(r"(0|[1-9][0-9]*)_m31\Z")
MAX_TOKENS = 512
MAX_INPUTS = 4
MAX_LANES = 8
MAX_LETS = 32
MAX_NODES = 16
MAX_ASSERTIONS = 16
MAX_RELATION_BYTES = 65_536


class UnsupportedSourceRelationFragment(ValueError):
    """The exact text is outside this independent checker's grammar."""


@dataclass(frozen=True)
class _PureBinaryHelper:
    """Checked static operation and parameter order from one source function."""

    name: str
    operator: str
    left_index: int
    right_index: int
    length: int


def _same_json_shape(actual: Any, expected: Any) -> bool:
    """Python equality alone aliases JSON booleans/floats with integers."""
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return (actual.keys() == expected.keys() and
                all(_same_json_shape(actual[key], value) for key, value in expected.items()))
    if isinstance(expected, list):
        return (len(actual) == len(expected) and
                all(_same_json_shape(item, value) for item, value in zip(actual, expected)))
    return actual == expected


def _tokens(data: bytes) -> list[str]:
    if len(data) > MAX_SOURCE_BYTES:
        raise UnsupportedSourceRelationFragment("source exceeds byte bound")
    try:
        source = data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise UnsupportedSourceRelationFragment("source must be UTF-8") from exc
    result: list[str] = []
    cursor = 0
    while cursor < len(source):
        match = TOKEN.match(source, cursor)
        if match is None:
            raise UnsupportedSourceRelationFragment(f"unsupported token at character {cursor}")
        found = match.group()
        if not found.isspace() and not found.startswith("//"):
            result.append(found)
            if len(result) > MAX_TOKENS:
                raise UnsupportedSourceRelationFragment("source exceeds token bound")
        cursor = match.end()
    return result


def _unwrapped(parts: list[str]) -> list[str]:
    while len(parts) >= 2 and parts[0] == "(":
        depth = 0
        for index, token in enumerate(parts):
            depth += (token == "(") - (token == ")")
            if depth < 0:
                raise UnsupportedSourceRelationFragment("unbalanced parentheses")
            if depth == 0:
                if index != len(parts) - 1:
                    return parts
                parts = parts[1:-1]
                break
        else:
            raise UnsupportedSourceRelationFragment("unbalanced parentheses")
    return parts


def _literal(token: str) -> int:
    match = LITERAL.fullmatch(token)
    if match is None:
        raise UnsupportedSourceRelationFragment("expected canonical M31 literal")
    value = int(match.group(1))
    if value >= M31_MODULUS:
        raise UnsupportedSourceRelationFragment("M31 literal outside canonical range")
    return value


def parse_source_fragment(data: bytes) -> dict[str, Any]:
    """Derive exact version-1 relation JSON without calling the S31 compiler."""
    tokens = _tokens(data)
    cursor = 0

    def take(expected: str | None = None) -> str:
        nonlocal cursor
        if cursor == len(tokens):
            raise UnsupportedSourceRelationFragment("unexpected end of source")
        found = tokens[cursor]
        cursor += 1
        if expected is not None and found != expected:
            raise UnsupportedSourceRelationFragment(f"expected {expected!r}, got {found!r}")
        return found

    def peek() -> str | None:
        return tokens[cursor] if cursor < len(tokens) else None

    def identifier() -> str:
        found = take()
        if (NAME.fullmatch(found) is None or found in SOURCE_KEYWORDS or
                found in PLAIN_BUILTIN_NAMES or len(found) > MAX_RELATION_NAME_CHARS):
            raise UnsupportedSourceRelationFragment("expected unreserved bounded identifier")
        return found

    def lane_type() -> int:
        for expected in ("[", "m31", ";"):
            take(expected)
        count = take()
        if (re.fullmatch(r"(0|[1-9][0-9]*)", count) is None or
                not 1 <= int(count) <= MAX_LANES):
            raise UnsupportedSourceRelationFragment("expected canonical 1..8 M31 array length")
        take("]")
        return int(count)

    # One pure monomorphic helper is an independently checked static rewrite.
    # Its body can only select two parameters and apply one field operation.
    helper: _PureBinaryHelper | None = None
    if peek() == "fn":
        take("fn")
        helper_name = identifier()
        take("(")
        first = identifier()
        take(":")
        first_length = lane_type()
        take(",")
        second = identifier()
        if first == second:
            raise UnsupportedSourceRelationFragment("duplicate function parameter")
        if helper_name in {first, second}:
            raise UnsupportedSourceRelationFragment("function parameter shadows function name")
        take(":")
        second_length = lane_type()
        take(")")
        take("->")
        result_length = lane_type()
        if first_length != second_length or first_length != result_length:
            raise UnsupportedSourceRelationFragment("function array shapes differ")
        take("{")
        body: list[str] = []
        while peek() not in {"}", None}:
            body.append(take())
        take("}")
        body = _unwrapped(body)
        if (len(body) != 3 or body[0] not in {first, second} or
                body[2] not in {first, second} or body[1] not in {"+", "-", ".*"}):
            raise UnsupportedSourceRelationFragment("function body must be one binary parameter operation")
        helper = _PureBinaryHelper(
            name=helper_name, operator=body[1],
            left_index=0 if body[0] == first else 1,
            right_index=0 if body[2] == first else 1,
            length=first_length)

    # Env values are a producer name or a static canonical M31 integer.
    env: dict[str, str | int] = {}

    def atom(parts: list[str]) -> str | int:
        parts = _unwrapped(parts)
        if len(parts) == 1 and parts[0] in env:
            return env[parts[0]]
        if (len(parts) == 7 and parts[:5] == ["splat", "<", str(lane_length), ">", "("]
                and parts[-1] == ")"):
            return _literal(parts[5])
        raise UnsupportedSourceRelationFragment("expected earlier name or matching splat<N>(literal)")

    def expression(parts: list[str]) -> tuple[str | int, str | None, str | int | None]:
        parts = _unwrapped(parts)
        depth = 0
        operators: list[int] = []
        for index, token in enumerate(parts):
            depth += (token == "(") - (token == ")")
            if depth < 0:
                raise UnsupportedSourceRelationFragment("unbalanced parentheses")
            if depth == 0 and token in {"+", "-", ".*"}:
                operators.append(index)
        if depth != 0 or len(operators) > 1:
            raise UnsupportedSourceRelationFragment("only one binary operation per let")
        if not operators:
            return atom(parts), None, None
        position = operators[0]
        return atom(parts[:position]), parts[position], atom(parts[position + 1:])

    def before_semicolon() -> list[str]:
        parts: list[str] = []
        while peek() not in {";", None}:
            parts.append(take())
        take(";")
        return parts

    take("circuit")
    circuit = identifier()
    if helper is not None and circuit == helper.name:
        raise UnsupportedSourceRelationFragment("function and circuit names must differ")
    take("(")
    inputs: list[dict[str, Any]] = []
    if peek() == ")":
        raise UnsupportedSourceRelationFragment("at least one input required")
    lane_length: int | None = None
    while True:
        visibility = take()
        if visibility not in {"public", "private"}:
            raise UnsupportedSourceRelationFragment("expected public or private input")
        name = identifier()
        if name in env:
            raise UnsupportedSourceRelationFragment("duplicate input name")
        take(":")
        input_length = lane_type()
        if lane_length is None:
            lane_length = input_length
        elif input_length != lane_length:
            raise UnsupportedSourceRelationFragment("input array shapes differ")
        if helper is not None and name == helper.name:
            raise UnsupportedSourceRelationFragment("input shadows function name")
        env[name] = name
        inputs.append({"name": name, "kind": "m31", "length": input_length,
                       "visibility": visibility})
        if len(inputs) > MAX_INPUTS:
            raise UnsupportedSourceRelationFragment("too many inputs")
        if peek() != ",":
            break
        take(",")
    take(")")
    take("->")
    take("public")
    result_length = lane_type()
    if result_length != lane_length:
        raise UnsupportedSourceRelationFragment("result array shape differs")
    if result_length * (1 + sum(item["visibility"] == "public" for item in inputs)) > 8:
        raise UnsupportedSourceRelationFragment("public word ABI exceeds eight words")
    if helper is not None and helper.length != result_length:
        raise UnsupportedSourceRelationFragment("function and circuit array shapes differ")
    take("{")
    nodes: list[dict[str, Any]] = []
    assertions: list[dict[str, str]] = []
    seen_assertions: set[tuple[str, str]] = set()
    let_count = 0
    helper_used = False
    while peek() in {"let", "assert_eq"}:
        if peek() == "let":
            take("let")
            name = identifier()
            if name in env:
                raise UnsupportedSourceRelationFragment("duplicate local name")
            if helper is not None and name == helper.name:
                raise UnsupportedSourceRelationFragment("local name shadows function")
            take("=")
            parts = _unwrapped(before_semicolon())
            if (helper is not None and len(parts) == 6 and
                    parts[0] == helper.name and parts[1] == "(" and
                    parts[3] == "," and parts[5] == ")"):
                arguments = (atom([parts[2]]), atom([parts[4]]))
                if any(not isinstance(argument, str) for argument in arguments):
                    raise UnsupportedSourceRelationFragment("function arguments must be named wires")
                lhs, rhs = arguments[helper.left_index], arguments[helper.right_index]
                op = helper.operator
                helper_used = True
            else:
                lhs, op, rhs = expression(parts)
            let_count += 1
            if let_count > MAX_LETS:
                raise UnsupportedSourceRelationFragment("too many lets")
            if op is None:
                env[name] = lhs
                continue
            if isinstance(lhs, int) and isinstance(rhs, int):
                raise UnsupportedSourceRelationFragment("constant-only operation unsupported")
            if op == "-" and isinstance(lhs, int):
                raise UnsupportedSourceRelationFragment("constant-left subtraction is outside fragment")
            if isinstance(lhs, int):
                lhs, rhs = rhs, lhs
            if isinstance(lhs, int):
                raise UnsupportedSourceRelationFragment("operation needs a wire")
            node: dict[str, Any] = {"name": name, "lhs": lhs}
            if isinstance(rhs, int):
                if op == "-":
                    node.update({"op": "add_const", "constant": (-rhs) % M31_MODULUS})
                else:
                    node.update({"op": "add_const" if op == "+" else "mul_const",
                                 "constant": rhs})
            else:
                node.update({"op": {"+": "add", "-": "sub", ".*": "mul"}[op],
                             "rhs": rhs})
            nodes.append(node)
            if len(nodes) > MAX_NODES:
                raise UnsupportedSourceRelationFragment("too many arithmetic nodes")
            env[name] = name
            continue
        take("assert_eq")
        take("(")
        lhs = atom([take()])
        take(",")
        rhs = atom([take()])
        take(")")
        take(";")
        if not isinstance(lhs, str) or not isinstance(rhs, str):
            raise UnsupportedSourceRelationFragment("assertions require named wires")
        pair = tuple(sorted((lhs, rhs)))
        if pair in seen_assertions:
            raise UnsupportedSourceRelationFragment("repeated assertion is outside fragment")
        seen_assertions.add(pair)
        assertions.append({"lhs": lhs, "rhs": rhs})
        if len(assertions) > MAX_ASSERTIONS:
            raise UnsupportedSourceRelationFragment("too many assertions")
    result = atom([take()])
    if not isinstance(result, str):
        raise UnsupportedSourceRelationFragment("result must be a wire")
    if peek() == ";":
        take(";")
    take("}")
    if cursor != len(tokens):
        raise UnsupportedSourceRelationFragment("trailing source tokens")
    if not nodes:
        raise UnsupportedSourceRelationFragment("at least one arithmetic node required")
    if helper is not None and not helper_used:
        raise UnsupportedSourceRelationFragment("unused function is outside fragment")
    return {"version": 1, "name": circuit, "inputs": inputs, "nodes": nodes,
            "assertions": assertions, "public_outputs": [result]}


def check_source_relation(source_bytes: bytes, relation_bytes: bytes) -> dict[str, str]:
    expected = parse_source_fragment(source_bytes)
    if len(relation_bytes) > MAX_RELATION_BYTES:
        raise ValueError("normalized relation exceeds bounded fragment byte limit")
    actual = parse_canonical_json(relation_bytes, "source.s31.json")
    if not _same_json_shape(actual, expected):
        raise ValueError("normalized relation differs from independent source parse")
    return {"capability": CAPABILITY,
            "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
            "relation_sha256": hashlib.sha256(relation_bytes).hexdigest()}


def check_package_source_relation(package: Path) -> dict[str, str]:
    """Check text, relation, public ABI, and their untrusted package hashes.

    This intentionally does not return package admission or proof status.
    """
    source_bytes = (package / "source.s31").read_bytes()
    relation_bytes = (package / "source.s31.json").read_bytes()
    result = check_source_relation(source_bytes, relation_bytes)
    relation = parse_source_fragment(source_bytes)
    abi_bytes = (package / "public-abi.json").read_bytes()
    abi = parse_canonical_json(abi_bytes, "public-abi.json")
    expected_abi = {
        "schema": "s31-public-abi-v1",
        "encoding": "eight canonical M31 words, encoded little-endian u32; unused words are zero",
        "public_inputs": [{"name": item["name"], "kind": "m31", "length": item["length"]}
                          for item in relation["inputs"] if item["visibility"] == "public"],
        "public_outputs": [{"name": relation["public_outputs"][0], "kind": "m31",
                            "length": relation["inputs"][0]["length"]}],
    }
    if not _same_json_shape(abi, expected_abi):
        raise ValueError("public ABI differs from independently parsed source")
    manifest = parse_canonical_json((package / "manifest.json").read_bytes(), "manifest.json")
    artifacts = manifest.get("artifacts")
    if (manifest.get("schema") != "s31-package-v1" or
            manifest.get("lowering") != "direct-gate" or
            manifest.get("name") != relation["name"] or
            manifest.get("source_text_sha256") != result["source_sha256"] or
            manifest.get("program_sha256") != result["relation_sha256"] or
            type(artifacts) is not dict):
        raise ValueError("manifest source/relation identity differs from checked source")
    for name, data in (("source.s31", source_bytes),
                       ("source.s31.json", relation_bytes),
                       ("public-abi.json", abi_bytes)):
        if artifacts.get(name) != hashlib.sha256(data).hexdigest():
            raise ValueError(f"manifest artifact hash differs: {name}")
    return result
