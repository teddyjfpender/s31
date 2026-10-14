"""Independent compositional source-to-relation checker for pure field control.

The exact source grammar is intentionally small: typed M31 array inputs,
straight-line named lets, aliases, field arithmetic, inverse, scalar zero
tests, and selection by a bit produced by a zero test. Each accepted let has
one typed rule; replaying those rules derives the complete normalized
relation. This makes no optimizer, native AIR, or PCS claim.
"""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from package.correspondence import (MAX_RELATION_NAME_CHARS, PLAIN_BUILTIN_NAMES,
                                    parse_canonical_json, same_json_shape)
from package.source_relation_fragment import NAME, SOURCE_KEYWORDS, _tokens

SCHEMA = "s31-pure-field-derivation-v1"
ARTIFACT = "pure-field-derivation.json"
CAPABILITY = "exact-source-to-normalized-relation-only"
MAX_STEPS = 64
MAX_NODES = 64
MAX_CERTIFICATE_BYTES = 131_072


class UnsupportedPureField(ValueError):
    """The source is outside the checked pure-field grammar."""


@dataclass(frozen=True)
class Value:
    wire: str
    kind: str
    length: int


def _hash(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _name(token: str) -> str:
    if (type(token) is not str or NAME.fullmatch(token) is None or
            token in SOURCE_KEYWORDS or
            token in PLAIN_BUILTIN_NAMES or
            len(token) > MAX_RELATION_NAME_CHARS):
        raise UnsupportedPureField("expected bounded unreserved identifier")
    return token


def _wrapped(parts: list[str]) -> list[str]:
    while len(parts) > 2 and parts[0] == "(":
        depth = 0
        for index, token in enumerate(parts):
            depth += (token == "(") - (token == ")")
            if depth < 0:
                raise UnsupportedPureField("unbalanced expression")
            if depth == 0:
                if index != len(parts) - 1:
                    return parts
                parts = parts[1:-1]
                break
        else:
            raise UnsupportedPureField("unbalanced expression")
    return parts


def _expression(parts: list[str]) -> tuple[str, list[str]]:
    parts = _wrapped(parts)
    if len(parts) == 1:
        return "alias", [_name(parts[0])]
    if len(parts) == 3 and parts[1] in {"+", "-", ".*"}:
        return {"+": "add", "-": "sub", ".*": "mul"}[parts[1]], [
            _name(parts[0]), _name(parts[2])]
    for prefix, op, arity in ((["std", ":", ":", "math", ":", ":", "inv"], "inv", 1),
                              (["std", ":", ":", "field", ":", ":", "is_zero"], "is_zero", 1),
                              (["std", ":", ":", "field", ":", ":", "select"], "select", 3),
                              (["select"], "select", 3)):
        if parts[:len(prefix) + 1] != prefix + ["("] or parts[-1:] != [")"]:
            continue
        arguments = parts[len(prefix) + 1:-1]
        if len(arguments) != 2 * arity - 1 or any(
                arguments[index] != "," for index in range(1, len(arguments), 2)):
            raise UnsupportedPureField("field call arguments must be named wires")
        return op, [_name(arguments[index]) for index in range(0, len(arguments), 2)]
    raise UnsupportedPureField("unsupported pure-field expression")


def derive(data: bytes) -> tuple[dict[str, Any], dict[str, Any]]:
    """Parse exact bytes, type each rule, and derive every relation node."""
    try:
        tokens = _tokens(data)
    except ValueError as exc:
        raise UnsupportedPureField(str(exc)) from exc
    cursor = 0

    def take(expected: str | None = None) -> str:
        nonlocal cursor
        if cursor == len(tokens):
            raise UnsupportedPureField("truncated pure-field source")
        found = tokens[cursor]
        cursor += 1
        if expected is not None and found != expected:
            raise UnsupportedPureField("outside pure-field source grammar")
        return found

    def peek() -> str | None:
        return tokens[cursor] if cursor < len(tokens) else None

    def lane_type() -> int:
        for item in ("[", "m31", ";"):
            take(item)
        count = take()
        if count not in {str(n) for n in range(1, 9)}:
            raise UnsupportedPureField("expected canonical M31 lane count 1..8")
        take("]")
        return int(count)

    explicit_std = peek() == "use"
    if explicit_std:
        for item in ("use", "std", "@", "1", ";"):
            take(item)
    take("circuit")
    circuit = _name(take())
    take("(")
    inputs: list[dict[str, Any]] = []
    env: dict[str, Value] = {}
    while True:
        visibility = take()
        if visibility not in {"public", "private"}:
            raise UnsupportedPureField("expected public or private M31 input")
        name = _name(take())
        take(":")
        length = lane_type()
        if name in env or name == circuit:
            raise UnsupportedPureField("duplicate input name")
        env[name] = Value(name, "m31", length)
        inputs.append({"name": name, "kind": "m31", "length": length,
                       "visibility": visibility})
        if len(inputs) > 8:
            raise UnsupportedPureField("too many pure-field inputs")
        if peek() != ",":
            break
        take(",")
    for item in (")", "->", "public"):
        take(item)
    output_length = lane_type()
    if output_length * 1 + sum(item["length"] for item in inputs
                               if item["visibility"] == "public") > 8:
        raise UnsupportedPureField("public M31 word ABI exceeds eight words")
    take("{")
    steps: list[dict[str, Any]] = []
    nodes: list[dict[str, Any]] = []
    inverse_sources: set[str] = set()
    control_used = False
    while peek() == "let":
        take("let")
        name = _name(take())
        if name in env or name == circuit:
            raise UnsupportedPureField("shadowed pure-field let")
        take("=")
        parts: list[str] = []
        while peek() not in {";", None}:
            parts.append(take())
        take(";")
        op, names = _expression(parts)
        if any(ref not in env for ref in names):
            raise UnsupportedPureField("unknown or future pure-field operand")
        args = [env[ref] for ref in names]
        node: dict[str, Any] | None = None
        if op == "alias":
            result = args[0]
        elif op in {"add", "sub", "mul"}:
            if (args[0].kind != "m31" or args[1].kind != "m31" or
                    args[0].length != args[1].length):
                raise UnsupportedPureField("binary M31 operand shape mismatch")
            result = Value(name, "m31", args[0].length)
            node = {"name": name, "op": op, "lhs": args[0].wire,
                    "rhs": args[1].wire}
        elif op == "inv":
            if not explicit_std or args[0].kind != "m31":
                raise UnsupportedPureField("inverse needs imported std and M31 input")
            if args[0].wire in inverse_sources:
                raise UnsupportedPureField("reused inverse is outside direct node derivation")
            inverse_sources.add(args[0].wire)
            result = Value(name, "m31", args[0].length)
            node = {"name": name, "op": op, "lhs": args[0].wire}
            control_used = True
        elif op == "is_zero":
            if not explicit_std or args[0].kind != "m31" or args[0].length != 1:
                raise UnsupportedPureField("zero test needs imported std and scalar M31 input")
            result = Value(name, "bit", 1)
            node = {"name": name, "op": op, "lhs": args[0].wire}
            control_used = True
        elif op == "select":
            if (args[0].kind != "bit" or args[1].kind != "m31" or
                    args[2].kind != "m31" or args[1].length != args[2].length):
                raise UnsupportedPureField("select needs computed bit and equal M31 arms")
            if parts[:1] == ["std"] and not explicit_std:
                raise UnsupportedPureField("qualified select needs imported std")
            result = Value(name, "m31", args[1].length)
            node = {"name": name, "op": op, "lhs": args[1].wire,
                    "rhs": args[2].wire, "selector": args[0].wire}
            control_used = True
        else:
            raise AssertionError("unhandled checked operation")
        if node is not None:
            nodes.append(node)
            if len(nodes) > MAX_NODES:
                raise UnsupportedPureField("too many emitted pure-field nodes")
        env[name] = result
        steps.append({"name": name, "rule": op, "source_operands": names,
                      "resolved_operands": [value.wire for value in args],
                      "result": {"wire": result.wire, "kind": result.kind,
                                 "length": result.length},
                      "node_index": len(nodes) - 1 if node is not None else None})
        if len(steps) > MAX_STEPS:
            raise UnsupportedPureField("too many pure-field steps")
    output_name = _name(take())
    if peek() == ";":
        take(";")
    take("}")
    if cursor != len(tokens) or output_name not in env:
        raise UnsupportedPureField("trailing source or unknown output")
    output = env[output_name]
    if (not control_used or not nodes or output.kind != "m31" or
            output.length != output_length):
        raise UnsupportedPureField("pure-field control fragment needs M31 result")
    relation = {"version": 1, "name": circuit, "inputs": inputs,
                "nodes": nodes, "assertions": [],
                "public_outputs": [output.wire]}
    derivation = {"name": circuit, "inputs": inputs, "steps": steps,
                  "output": {"source_name": output_name, "wire": output.wire,
                             "kind": output.kind, "length": output.length}}
    return relation, derivation


def admitted(source_bytes: bytes, relation_bytes: bytes) -> bool:
    try:
        relation, _ = derive(source_bytes)
        return same_json_shape(parse_canonical_json(relation_bytes, "source.s31.json"), relation)
    except (UnsupportedPureField, ValueError):
        return False


def replay_derivation(program: dict[str, Any]) -> dict[str, Any]:
    """Check certificate rules without reading source tokens or compiler IR.

    This second pass checks all operand resolutions, types, node indices, and
    the selected output before reconstructing the relation from the rule list.
    """
    if type(program) is not dict or set(program) != {"name", "inputs", "steps", "output"}:
        raise ValueError("invalid pure-field derivation shape")
    circuit = _name(program["name"])
    inputs, steps = program["inputs"], program["steps"]
    if (type(inputs) is not list or not 1 <= len(inputs) <= 8 or
            type(steps) is not list or not 1 <= len(steps) <= MAX_STEPS):
        raise ValueError("pure-field derivation exceeds input or step bound")
    env: dict[str, Value] = {}
    normalized_inputs: list[dict[str, Any]] = []
    for item in inputs:
        if type(item) is not dict or set(item) != {"name", "kind", "length", "visibility"}:
            raise ValueError("invalid pure-field input rule")
        name = _name(item["name"])
        length = item["length"]
        if (name in env or name == circuit or item["kind"] != "m31" or
                type(length) is not int or not 1 <= length <= 8 or
                type(item["visibility"]) is not str or
                item["visibility"] not in {"public", "private"}):
            raise ValueError("invalid pure-field input type")
        env[name] = Value(name, "m31", length)
        normalized_inputs.append(dict(item))
    nodes: list[dict[str, Any]] = []
    inverse_sources: set[str] = set()
    controls = 0
    for step in steps:
        if (type(step) is not dict or set(step) !=
                {"name", "rule", "source_operands", "resolved_operands",
                 "result", "node_index"}):
            raise ValueError("invalid pure-field step rule")
        name = _name(step["name"])
        op = step["rule"]
        operands = step["source_operands"]
        if (name in env or name == circuit or type(op) is not str or
                type(operands) is not list or
                any(type(ref) is not str or ref not in env for ref in operands)):
            raise ValueError("shadowed or future pure-field rule operand")
        arity = {"alias": 1, "add": 2, "sub": 2, "mul": 2,
                 "inv": 1, "is_zero": 1, "select": 3}.get(op)
        if arity is None or len(operands) != arity:
            raise ValueError("invalid pure-field rule arity")
        args = [env[ref] for ref in operands]
        if not same_json_shape(step["resolved_operands"], [arg.wire for arg in args]):
            raise ValueError("pure-field operand resolution differs")
        node: dict[str, Any] | None = None
        if op == "alias":
            result = args[0]
        elif op in {"add", "sub", "mul"}:
            if (args[0].kind != "m31" or args[1].kind != "m31" or
                    args[0].length != args[1].length):
                raise ValueError("binary pure-field rule shape differs")
            result = Value(name, "m31", args[0].length)
            node = {"name": name, "op": op, "lhs": args[0].wire,
                    "rhs": args[1].wire}
        elif op == "inv":
            if args[0].kind != "m31" or args[0].wire in inverse_sources:
                raise ValueError("inverse rule source differs")
            inverse_sources.add(args[0].wire)
            result = Value(name, "m31", args[0].length)
            node = {"name": name, "op": op, "lhs": args[0].wire}
            controls += 1
        elif op == "is_zero":
            if args[0].kind != "m31" or args[0].length != 1:
                raise ValueError("zero-test rule shape differs")
            result = Value(name, "bit", 1)
            node = {"name": name, "op": op, "lhs": args[0].wire}
            controls += 1
        else:
            if (args[0].kind != "bit" or args[1].kind != "m31" or
                    args[2].kind != "m31" or args[1].length != args[2].length):
                raise ValueError("select rule shape differs")
            result = Value(name, "m31", args[1].length)
            node = {"name": name, "op": op, "lhs": args[1].wire,
                    "rhs": args[2].wire, "selector": args[0].wire}
            controls += 1
        if node is not None:
            nodes.append(node)
        if (len(nodes) > MAX_NODES or
                not same_json_shape(step["node_index"],
                                    len(nodes) - 1 if node is not None else None) or
                not same_json_shape(step["result"],
                                    {"wire": result.wire, "kind": result.kind,
                                     "length": result.length})):
            raise ValueError("pure-field emitted node or result differs")
        env[name] = result
    output = program["output"]
    if type(output) is not dict or set(output) != {"source_name", "wire", "kind", "length"}:
        raise ValueError("invalid pure-field output rule")
    output_name = output["source_name"]
    if type(output_name) is not str or output_name not in env:
        raise ValueError("pure-field output names no source value")
    selected = env[output_name]
    if (controls == 0 or selected.kind != "m31" or
            not same_json_shape(output, {"source_name": output_name,
                                         "wire": selected.wire,
                                         "kind": selected.kind,
                                         "length": selected.length}) or
            selected.length + sum(item["length"] for item in normalized_inputs
                                  if item["visibility"] == "public") > 8):
        raise ValueError("pure-field result or public ABI differs")
    return {"version": 1, "name": circuit, "inputs": normalized_inputs,
            "nodes": nodes, "assertions": [], "public_outputs": [selected.wire]}


def make_certificate(source_bytes: bytes, relation_bytes: bytes) -> dict[str, Any]:
    relation, derivation = derive(source_bytes)
    if not same_json_shape(replay_derivation(derivation), relation):
        raise ValueError("pure-field typed rule replay differs from source derivation")
    if not same_json_shape(parse_canonical_json(relation_bytes, "source.s31.json"), relation):
        raise ValueError("pure-field normalized relation differs from exact source")
    return {"schema": SCHEMA, "capability": CAPABILITY,
            "source_sha256": _hash(source_bytes),
            "relation_sha256": _hash(relation_bytes),
            "derivation": derivation}


def verify_artifact(package: Path, manifest: dict[str, Any]) -> None:
    path = package / ARTIFACT
    artifacts = manifest["artifacts"]
    listed = ARTIFACT in artifacts
    present = path.exists() or path.is_symlink()
    eligible = ("source_text_sha256" in manifest and
                manifest.get("correspondence_schema") !=
                "s31-direct-gate-correspondence-v3")
    if not eligible:
        if listed or present:
            raise ValueError("unsupported package carries pure-field derivation")
        return
    source = (package / "source.s31").read_bytes()
    relation = (package / "source.s31.json").read_bytes()
    if not admitted(source, relation):
        if listed or present:
            raise ValueError("unsupported source carries pure-field derivation")
        return
    if (not listed or not path.is_file() or path.is_symlink() or
            path.stat().st_size > MAX_CERTIFICATE_BYTES):
        raise ValueError("admitted pure-field source lacks bounded derivation")
    raw = path.read_bytes()
    if artifacts[ARTIFACT] != _hash(raw):
        raise ValueError("pure-field artifact hash differs")
    actual = parse_canonical_json(raw, ARTIFACT)
    if not same_json_shape(replay_derivation(actual.get("derivation")),
                           parse_canonical_json(relation, "source.s31.json")):
        raise ValueError("pure-field certificate rules differ from normalized relation")
    if not same_json_shape(actual, make_certificate(source, relation)):
        raise ValueError("pure-field derivation differs from exact source replay")
