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
                                    OPTIMIZED_SCHEMA, SOURCE_KEYWORDS,
                                    parse_canonical_json)

CAPABILITY = "source-to-relation-only"
CERTIFICATE_SCHEMA = "s31-source-relation-certificate-v1"
LEAN_SEMANTIC_PROFILE = "linear-ssa-m31-v1"
LEAN_EFFECTS_PROFILE = "linear-ssa-m31-effects-v1"
TOKEN = re.compile(r"[ \t\n\v\f\r]+|//[^\n]*|->|\.\*|[()\[\];:{}=+,.<>@-]|[A-Za-z_][A-Za-z_0-9]*|[0-9]+_m31|[0-9]+")
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")
LITERAL = re.compile(r"(0|[1-9][0-9]*)_m31\Z")
MAX_TOKENS = 512
MAX_INPUTS = 4
MAX_HELPERS = 8
MAX_LANES = 8
MAX_LETS = 32
MAX_NODES = 16
MAX_ASSERTIONS = 16
MAX_RELATION_BYTES = 65_536
MAX_CERTIFICATE_BYTES = 65_536


class UnsupportedSourceRelationFragment(ValueError):
    """The exact text is outside this independent checker's grammar."""


@dataclass(frozen=True)
class _PureBinaryHelper:
    """Checked static binary operation over one or two function parameters."""

    name: str
    operator: str
    left_index: int
    right_index: int
    length: int
    arity: int


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


def parse_source_fragment(data: bytes, *, _static_products: list[bool] | None = None,
                          _derivation: list[dict[str, Any]] | None = None,
                          _allow_helper_products: bool = False) -> dict[str, Any]:
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

    # A version-pinned import is source metadata for this fragment: none of
    # its accepted expressions can invoke a standard-library function.
    if peek() == "use":
        for expected in ("use", "std", "@", "1", ";"):
            take(expected)

    # Each pure monomorphic helper is an independently checked static rewrite.
    # Its body can only select two parameters and apply one field operation.
    helpers: dict[str, _PureBinaryHelper] = {}
    helper_derivations: list[dict[str, Any]] = []
    while peek() == "fn":
        take("fn")
        helper_name = identifier()
        if helper_name in helpers or len(helpers) >= MAX_HELPERS:
            raise UnsupportedSourceRelationFragment("duplicate or excessive helper declarations")
        take("(")
        first = identifier()
        take(":")
        first_length = lane_type()
        params = [first]
        second_length = first_length
        if peek() == ",":
            take(",")
            second = identifier()
            if first == second:
                raise UnsupportedSourceRelationFragment("duplicate function parameter")
            params.append(second)
            take(":")
            second_length = lane_type()
        if helper_name in params:
            raise UnsupportedSourceRelationFragment("function parameter shadows function name")
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
        if (len(body) != 3 or body[0] not in params or
                body[2] not in params or body[1] not in {"+", "-", ".*"}):
            raise UnsupportedSourceRelationFragment("function body must be one binary parameter operation")
        helpers[helper_name] = _PureBinaryHelper(
            name=helper_name, operator=body[1],
            left_index=params.index(body[0]),
            right_index=params.index(body[2]),
            length=first_length, arity=len(params))
        helper_derivations.append({"name": helper_name, "params": params,
                                   "body": {"kind": "binary", "op": body[1],
                                            "lhs": {"kind": "name", "name": body[0]},
                                            "rhs": {"kind": "name", "name": body[2]}}})

    def structural_atom(parts: list[str]) -> dict[str, Any]:
        parts = _unwrapped(parts)
        if len(parts) == 1:
            return {"kind": "name", "name": parts[0]}
        if len(parts) == 3 and parts[1] == ".":
            return {"kind": "project", "source": {"kind": "name", "name": parts[0]},
                    "field": parts[2]}
        if len(parts) == 7 and parts[:4] == ["splat", "<", str(lane_length), ">"]:
            return {"kind": "literal", "length": lane_length,
                    "value": _literal(parts[5])}
        raise UnsupportedSourceRelationFragment("unsupported structural atom")

    def structural_expr(raw_parts: list[str]) -> dict[str, Any]:
        parts = _unwrapped(raw_parts)
        if (len(parts) in {4, 6} and parts[0] in helpers and parts[1] == "(" and
                parts[-1] == ")"):
            arguments = [parts[2]] if len(parts) == 4 else [parts[2], parts[4]]
            return {"kind": "apply", "helper": parts[0],
                    "args": [{"kind": "name", "name": name} for name in arguments]}
        if len(raw_parts) >= 5 and raw_parts[0] == "(" and raw_parts[-1] == ")":
            inside = raw_parts[1:-1]
            if "," in inside:
                fields = []
                current: list[str] = []
                for part in inside:
                    if part == ",":
                        fields.append(current)
                        current = []
                    else:
                        current.append(part)
                fields.append(current)
                return {"kind": "construct", "type": "tuple",
                        "fields": [{"label": str(index), "value": structural_atom(field)}
                                   for index, field in enumerate(fields)]}
        depth = 0
        for index, part in enumerate(parts):
            depth += (part == "(") - (part == ")")
            if depth == 0 and part in {"+", "-", ".*"}:
                return {"kind": "binary", "op": part,
                        "lhs": structural_atom(parts[:index]),
                        "rhs": structural_atom(parts[index + 1:])}
        return structural_atom(parts)

    # A product is a compile-time tuple of already typed M31 lane arrays.
    # It has no normalized node or witness cell; projection selects a wire.
    env: dict[str, str | int | tuple[str, ...]] = {}
    static_product_used = False

    def atom(parts: list[str]) -> str | int:
        nonlocal static_product_used
        if static_product_used and parts and parts[0] == "(":
            raise UnsupportedSourceRelationFragment("grouped product operand is outside Lean byte grammar")
        parts = _unwrapped(parts)
        if len(parts) == 1 and parts[0] in env:
            found = env[parts[0]]
            if isinstance(found, tuple):
                raise UnsupportedSourceRelationFragment("tuple needs a static projection")
            return found
        if (len(parts) == 3 and parts[1] == "." and parts[0] in env and
                re.fullmatch(r"(0|[1-9][0-9]*)", parts[2])):
            found = env[parts[0]]
            index = int(parts[2])
            if not isinstance(found, tuple) or index >= len(found):
                raise UnsupportedSourceRelationFragment("invalid tuple projection")
            static_product_used = True
            return found[index]
        if (len(parts) == 7 and parts[:5] == ["splat", "<", str(lane_length), ">", "("]
                and parts[-1] == ")"):
            return _literal(parts[5])
        raise UnsupportedSourceRelationFragment("expected earlier name or matching splat<N>(literal)")

    def expression(parts: list[str]) -> tuple[str | int | tuple[str, ...], str | None,
                                             str | int | None]:
        nonlocal static_product_used
        # The grammar admits a flat product of 2..4 existing M31 arrays.
        # Source values are wires; nested products and runtime indexing are
        # outside this independently checked fragment.
        if len(parts) >= 5 and parts[0] == "(" and parts[-1] == ")":
            inside = parts[1:-1]
            depth = 0
            fields: list[list[str]] = [[]]
            for token in inside:
                depth += (token == "(") - (token == ")")
                if depth < 0:
                    raise UnsupportedSourceRelationFragment("unbalanced tuple constructor")
                if token == "," and depth == 0:
                    fields.append([])
                else:
                    fields[-1].append(token)
            if depth != 0:
                raise UnsupportedSourceRelationFragment("unbalanced tuple constructor")
            if len(fields) > 1:
                if not 2 <= len(fields) <= 4 or any(not field for field in fields):
                    raise UnsupportedSourceRelationFragment("tuple needs 2..4 fields")
                if any(not (len(field) == 1 or
                            (len(field) == 3 and field[1] == "." and
                             re.fullmatch(r"(0|[1-9][0-9]*)", field[2])))
                       for field in fields):
                    raise UnsupportedSourceRelationFragment("tuple field must be a direct wire or projection")
                values = tuple(atom(field) for field in fields)
                if not all(isinstance(value, str) for value in values):
                    raise UnsupportedSourceRelationFragment("tuple fields must be M31 wires")
                static_product_used = True
                return values, None, None
        if static_product_used and parts and parts[0] == "(":
            raise UnsupportedSourceRelationFragment("grouped product expression is outside Lean byte grammar")
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
            if len(parts) == 1 and isinstance(env.get(parts[0]), tuple):
                static_product_used = True
                return env[parts[0]], None, None
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
    if circuit in helpers:
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
        if name in helpers:
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
    if any(helper.length != result_length for helper in helpers.values()):
        raise UnsupportedSourceRelationFragment("function and circuit array shapes differ")
    take("{")
    nodes: list[dict[str, Any]] = []
    assertions: list[dict[str, str]] = []
    seen_assertions: set[tuple[str, str]] = set()
    let_count = 0
    structural_steps: list[dict[str, Any]] = []
    helpers_used: set[str] = set()
    while peek() in {"let", "assert_eq"}:
        if peek() == "let":
            take("let")
            name = identifier()
            if name in env:
                raise UnsupportedSourceRelationFragment("duplicate local name")
            if name in helpers:
                raise UnsupportedSourceRelationFragment("local name shadows function")
            take("=")
            raw_parts = before_semicolon()
            parts = _unwrapped(raw_parts)
            if (len(parts) in {4, 6} and parts[0] in helpers and parts[1] == "(" and
                    parts[-1] == ")" and
                    (len(parts) == 4 or parts[3] == ",") and
                    helpers[parts[0]].arity == (1 if len(parts) == 4 else 2)):
                helper = helpers[parts[0]]
                arguments = tuple(atom([parts[index]]) for index in
                                  ((2,) if helper.arity == 1 else (2, 4)))
                if any(not isinstance(argument, str) for argument in arguments):
                    raise UnsupportedSourceRelationFragment("function arguments must be named wires")
                lhs, rhs = arguments[helper.left_index], arguments[helper.right_index]
                op = helper.operator
                helpers_used.add(helper.name)
            else:
                lhs, op, rhs = expression(raw_parts)
            let_count += 1
            if let_count > MAX_LETS:
                raise UnsupportedSourceRelationFragment("too many lets")
            if _derivation is not None:
                structural_steps.append({"kind": "let", "name": name,
                                         "expr": structural_expr(raw_parts)})
            if op is None:
                env[name] = lhs
                continue
            if isinstance(lhs, tuple) or isinstance(rhs, tuple):
                raise UnsupportedSourceRelationFragment("arithmetic needs projected M31 wires")
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
        lhs_parts: list[str] = []
        while peek() not in {",", None}:
            lhs_parts.append(take())
        lhs = atom(lhs_parts)
        take(",")
        rhs_parts: list[str] = []
        while peek() not in {")", None}:
            rhs_parts.append(take())
        rhs = atom(rhs_parts)
        take(")")
        take(";")
        if not isinstance(lhs, str) or not isinstance(rhs, str):
            raise UnsupportedSourceRelationFragment("assertions require named wires")
        pair = tuple(sorted((lhs, rhs)))
        if pair in seen_assertions:
            raise UnsupportedSourceRelationFragment("repeated assertion is outside fragment")
        seen_assertions.add(pair)
        assertions.append({"lhs": lhs, "rhs": rhs})
        if _derivation is not None:
            structural_steps.append({"kind": "assert", "lhs": structural_atom(lhs_parts),
                                     "rhs": structural_atom(rhs_parts)})
        if len(assertions) > MAX_ASSERTIONS:
            raise UnsupportedSourceRelationFragment("too many assertions")
    result_parts: list[str] = []
    while peek() not in {";", "}", None}:
        result_parts.append(take())
    result = atom(result_parts)
    if not isinstance(result, str):
        raise UnsupportedSourceRelationFragment("result must be a wire")
    if peek() == ";":
        take(";")
    take("}")
    if cursor != len(tokens):
        raise UnsupportedSourceRelationFragment("trailing source tokens")
    if not nodes:
        raise UnsupportedSourceRelationFragment("at least one arithmetic node required")
    if set(helpers) != helpers_used:
        raise UnsupportedSourceRelationFragment("unused function is outside fragment")
    if static_product_used and helpers and not _allow_helper_products:
        raise UnsupportedSourceRelationFragment("product and static helper combination is outside Lean byte grammar")
    relation = {"version": 1, "name": circuit, "inputs": inputs, "nodes": nodes,
            "assertions": assertions, "public_outputs": [result]}
    if _static_products is not None:
        _static_products.append(static_product_used)
    if _derivation is not None:
        _derivation.append({"fragment": "m31-v1", "name": circuit,
                            "inputs": inputs, "helpers": helper_derivations,
                            "steps": structural_steps,
                            "result": structural_atom(result_parts)})
    return relation


def _lean_helper_product_shape(data: bytes) -> None:
    """Recognize a deliberately small token grammar shared with the Lean gate.

    The independent relation parser below still resolves every name and type.
    This pass excludes grouped expressions, extra helpers, and other Python
    syntax that the bounded Lean byte parser cannot yet interpret.
    """
    if any(byte >= 128 for byte in data):
        raise UnsupportedSourceRelationFragment("Lean helper/product source must be ASCII")
    tokens = _tokens(data)
    cursor = 0

    def take(expected: str | None = None) -> str:
        nonlocal cursor
        if cursor == len(tokens):
            raise UnsupportedSourceRelationFragment("incomplete Lean helper/product form")
        found = tokens[cursor]
        cursor += 1
        if expected is not None and found != expected:
            raise UnsupportedSourceRelationFragment("outside Lean helper/product token grammar")
        return found

    def peek() -> str | None:
        return tokens[cursor] if cursor < len(tokens) else None

    def ident() -> str:
        name = take()
        if (NAME.fullmatch(name) is None or name in SOURCE_KEYWORDS or
                name in PLAIN_BUILTIN_NAMES or len(name) > MAX_RELATION_NAME_CHARS):
            raise UnsupportedSourceRelationFragment("invalid Lean helper/product identifier")
        return name

    def lane_type(expected: int | None = None) -> int:
        for item in ("[", "m31", ";"):
            take(item)
        count = take()
        if count not in {str(n) for n in range(1, 9)}:
            raise UnsupportedSourceRelationFragment("invalid Lean M31 array length")
        take("]")
        length = int(count)
        if expected is not None and length != expected:
            raise UnsupportedSourceRelationFragment("helper/circuit array lengths differ")
        return length

    if peek() == "use":
        for item in ("use", "std", "@", "1", ";"):
            take(item)
    take("fn")
    helper = ident()
    take("(")
    first = ident()
    take(":")
    length = lane_type()
    take(",")
    second = ident()
    take(":")
    lane_type(length)
    take(")")
    take("->")
    lane_type(length)
    take("{")
    ident()
    if take() not in {"+", "-", ".*"}:
        raise UnsupportedSourceRelationFragment("helper body is not one binary operation")
    ident()
    take("}")
    take("circuit")
    ident()
    take("(")
    input_count = 0
    public_count = 0
    while True:
        visibility = take()
        if visibility not in {"public", "private"}:
            raise UnsupportedSourceRelationFragment("invalid input visibility")
        public_count += visibility == "public"
        ident()
        take(":")
        lane_type(length)
        input_count += 1
        if input_count > MAX_INPUTS:
            raise UnsupportedSourceRelationFragment("too many Lean inputs")
        if peek() != ",":
            break
        take(",")
    take(")")
    take("->")
    take("public")
    lane_type(length)
    if length * (public_count + 1) > 8:
        raise UnsupportedSourceRelationFragment("public ABI exceeds eight words")
    take("{")
    product = projection = call = False
    let_count = 0
    while peek() == "let":
        take("let")
        ident()
        take("=")
        if peek() == "(":
            take("(")
            ident()
            count = 1
            while peek() == ",":
                take(",")
                ident()
                count += 1
            if not 2 <= count <= 4:
                raise UnsupportedSourceRelationFragment("tuple field count outside Lean grammar")
            take(")")
            product = True
        else:
            name = ident()
            if name == helper and peek() == "(":
                take("(")
                ident()
                take(",")
                ident()
                take(")")
                call = True
            elif peek() == ".":
                take(".")
                if take() not in {"0", "1", "2", "3"}:
                    raise UnsupportedSourceRelationFragment("projection outside Lean tuple bound")
                projection = True
        take(";")
        let_count += 1
        if let_count > MAX_LETS:
            raise UnsupportedSourceRelationFragment("too many Lean lets")
    ident()
    if peek() == ";":
        take(";")
    take("}")
    if cursor != len(tokens) or not (product and projection and call):
        raise UnsupportedSourceRelationFragment("outside combined Lean helper/product grammar")


def parse_enrolled_source_fragment(data: bytes, *,
                                   _static_products: list[bool] | None = None) -> dict[str, Any]:
    """Default bounded relation, plus the separately restricted combined form."""
    try:
        return parse_source_fragment(data, _static_products=_static_products)
    except UnsupportedSourceRelationFragment:
        _lean_helper_product_shape(data)
        return parse_source_fragment(data, _static_products=_static_products,
                                     _allow_helper_products=True)


def check_source_relation(source_bytes: bytes, relation_bytes: bytes) -> dict[str, str]:
    expected = parse_enrolled_source_fragment(source_bytes)
    if len(relation_bytes) > MAX_RELATION_BYTES:
        raise ValueError("normalized relation exceeds bounded fragment byte limit")
    actual = parse_canonical_json(relation_bytes, "source.s31.json")
    if not _same_json_shape(actual, expected):
        raise ValueError("normalized relation differs from independent source parse")
    return {"capability": CAPABILITY,
            "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
            "relation_sha256": hashlib.sha256(relation_bytes).hexdigest()}


def _indexed_ssa(relation: dict[str, Any]) -> tuple[dict[str, Any], list[str]]:
    """Project a checked relation into a stable, source-derived SSA roster.

    This projection is deliberately complete for this parser's grammar. In
    particular, constants and assertions remain visible. Their presence
    selects the separate effectful semantic profile.
    """
    names: dict[str, int] = {}
    inputs: list[dict[str, Any]] = []
    for item in relation["inputs"]:
        identifier = len(names)
        names[item["name"]] = identifier
        inputs.append({"id": identifier, "name": item["name"],
                       "visibility": item["visibility"]})
    nodes: list[dict[str, Any]] = []
    effects: set[str] = set()
    for item in relation["nodes"]:
        identifier = len(names)
        op = item["op"]
        node = {"id": identifier, "name": item["name"], "op": op,
                "lhs": names[item["lhs"]]}
        if op in {"add", "sub", "mul"}:
            node["rhs"] = names[item["rhs"]]
        elif op in {"add_const", "mul_const"}:
            node["constant"] = item["constant"]
            effects.add("constant-arithmetic")
        else:
            raise ValueError(f"unreviewed source relation operation: {op}")
        names[item["name"]] = identifier
        nodes.append(node)
    assertions = [[names[item["lhs"]], names[item["rhs"]]]
                  for item in relation["assertions"]]
    if assertions:
        effects.add("assertions")
    return ({"lane_count": relation["inputs"][0]["length"],
             "inputs": inputs, "nodes": nodes, "assertions": assertions,
             "output": names[relation["public_outputs"][0]]}, sorted(effects))


def make_source_relation_certificate(source_bytes: bytes,
                                     relation_bytes: bytes) -> dict[str, Any]:
    """Reparse exact source bytes and bind the complete normalized relation.

    A digest is an identity check, not a proof that the production compiler
    implements this parser or that its native AIR faithfully executes the
    relation. Those remain separate trust obligations.
    """
    identity = check_source_relation(source_bytes, relation_bytes)
    static_products: list[bool] = []
    ssa, effects = _indexed_ssa(parse_enrolled_source_fragment(
        source_bytes, _static_products=static_products))
    if static_products == [True]:
        # The pure Lean source byte parser does not accept tuple syntax.
        # Select the effects parser, whose exact byte grammar includes the
        # static erasure, even when the graph has no arithmetic effects.
        effects.append("static-products")
    return {"schema": CERTIFICATE_SCHEMA, **identity, "ssa": ssa,
            "lean_semantic_profile": LEAN_EFFECTS_PROFILE if effects else LEAN_SEMANTIC_PROFILE,
            "unmodeled_features": []}


def check_source_relation_certificate(source_bytes: bytes, relation_bytes: bytes,
                                      certificate_bytes: bytes) -> dict[str, Any]:
    """Reject any certificate that differs from a fresh independent replay."""
    if len(certificate_bytes) > MAX_CERTIFICATE_BYTES:
        raise ValueError("source relation certificate exceeds byte bound")
    actual = parse_canonical_json(certificate_bytes, "source-relation-certificate.json")
    expected = make_source_relation_certificate(source_bytes, relation_bytes)
    if not _same_json_shape(actual, expected):
        raise ValueError("source relation certificate differs from source-derived SSA")
    return expected


def verify_source_relation_artifact(package: Path, manifest: dict[str, Any]) -> None:
    """Enforce exactly when a conservatively compiled text package carries this claim."""
    path = package / "source-relation-certificate.json"
    artifacts = manifest["artifacts"]
    listed = path.name in artifacts
    present = path.exists() or path.is_symlink()
    eligible = ("source_text_sha256" in manifest and
                manifest.get("correspondence_schema") != OPTIMIZED_SCHEMA)
    if not eligible:
        if listed or present:
            raise ValueError("source relation certificate requires conservative text source")
        return
    source_bytes = (package / "source.s31").read_bytes()
    try:
        parse_enrolled_source_fragment(source_bytes)
    except UnsupportedSourceRelationFragment:
        if listed or present:
            raise ValueError("unsupported source carries a source relation certificate")
        return
    if not listed or not present or path.is_symlink():
        raise ValueError("checked source requires a source relation certificate")
    if path.stat().st_size > MAX_CERTIFICATE_BYTES:
        raise ValueError("source relation certificate exceeds byte bound")
    data = path.read_bytes()
    if artifacts[path.name] != hashlib.sha256(data).hexdigest():
        raise ValueError("source relation certificate artifact hash differs")
    check_source_relation_certificate(source_bytes, (package / "source.s31.json").read_bytes(), data)


def check_package_source_relation(package: Path) -> dict[str, str]:
    """Check text, relation, public ABI, and their untrusted package hashes.

    This intentionally does not return package admission or proof status.
    """
    source_bytes = (package / "source.s31").read_bytes()
    relation_bytes = (package / "source.s31.json").read_bytes()
    result = check_source_relation(source_bytes, relation_bytes)
    relation = parse_enrolled_source_fragment(source_bytes)
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
