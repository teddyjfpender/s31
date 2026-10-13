"""Independent source-to-relation check for a bounded record ABI v2 fragment.

Capability: ``source-to-relation-only``. This checker deliberately does not
import the production S31 lexer, parser, elaborator, compiler, ABI builder,
relation validator, package verifier, or native circuit compiler. It derives
one small source grammar's exact relation and ABI from source bytes.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any

from package.correspondence import (MAX_RELATION_NAME_CHARS, MAX_SOURCE_BYTES,
                                    PLAIN_BUILTIN_NAMES, SOURCE_KEYWORDS,
                                    parse_canonical_json)

CAPABILITY = "source-to-relation-only"
TOKEN = re.compile(r"[ \t\n\v\f\r]+|//[^\n]*|->|\.\*|[()\[\];:{}=,+.]|[A-Za-z_][A-Za-z_0-9]*|[0-9]+")
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")
MAX_TOKENS = 512
MAX_FIELDS = 4
MAX_INPUTS = 2
MAX_LETS = 8
MAX_RELATION_BYTES = 65_536
ABI_DOMAIN = b"s31-public-record-boundary-v2\0"
ABI_ENCODING = "canonical typed-only JSON statement with named paths and aliased M31/bit/u8/u16/u32 leaves"
RESERVED_RECORD_TYPES = frozenset({
    "UInt256", "Bytes32", "BlockHash", "Target", "Work", "ChainWork",
    "Bytes80", "Digest", "Poseidon2", "Blake2sReduced",
})


class UnsupportedRecordSourceFragment(ValueError):
    """The exact text is outside this independently reviewed grammar."""


def _same_shape(actual: Any, expected: Any) -> bool:
    """Compare JSON recursively without Python's bool/int/float equivalence."""
    if type(actual) is not type(expected):
        return False
    if isinstance(expected, dict):
        return (actual.keys() == expected.keys() and
                all(_same_shape(actual[key], value) for key, value in expected.items()))
    if isinstance(expected, list):
        return (len(actual) == len(expected) and
                all(_same_shape(item, value) for item, value in zip(actual, expected)))
    return actual == expected


def _digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _tokens(data: bytes) -> list[str]:
    if len(data) > MAX_SOURCE_BYTES:
        raise UnsupportedRecordSourceFragment("source exceeds byte bound")
    try:
        source = data.decode("utf-8", errors="strict")
    except UnicodeDecodeError as exc:
        raise UnsupportedRecordSourceFragment("source must be UTF-8") from exc
    result: list[str] = []
    cursor = 0
    while cursor < len(source):
        match = TOKEN.match(source, cursor)
        if match is None:
            raise UnsupportedRecordSourceFragment(f"unsupported token at character {cursor}")
        found = match.group()
        if not found.isspace() and not found.startswith("//"):
            result.append(found)
            if len(result) > MAX_TOKENS:
                raise UnsupportedRecordSourceFragment("source exceeds token bound")
        cursor = match.end()
    return result


def parse_record_source_fragment(data: bytes, *,
                                 _derivation: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    """Reconstruct an exact v2 relation without calling the S31 compiler."""
    tokens = _tokens(data)
    cursor = 0

    def take(expected: str | None = None) -> str:
        nonlocal cursor
        if cursor == len(tokens):
            raise UnsupportedRecordSourceFragment("unexpected end of source")
        found = tokens[cursor]
        cursor += 1
        if expected is not None and found != expected:
            raise UnsupportedRecordSourceFragment(f"expected {expected!r}, got {found!r}")
        return found

    def peek() -> str | None:
        return tokens[cursor] if cursor < len(tokens) else None

    def identifier() -> str:
        found = take()
        if (NAME.fullmatch(found) is None or len(found) > MAX_RELATION_NAME_CHARS or
                found in SOURCE_KEYWORDS or found in PLAIN_BUILTIN_NAMES or
                found.startswith("_s31_abi_input_")):
            raise UnsupportedRecordSourceFragment("expected bounded unreserved identifier")
        return found

    def leaf_type() -> None:
        for expected in ("[", "m31", ";", "1", "]"):
            take(expected)

    take("struct")
    record_name = identifier()
    if not record_name[0].isupper() or record_name in RESERVED_RECORD_TYPES:
        raise UnsupportedRecordSourceFragment("reserved or non-nominal record name")
    take("{")
    fields: list[str] = []
    while True:
        field = identifier()
        if field in fields:
            raise UnsupportedRecordSourceFragment("duplicate record field")
        take(":")
        leaf_type()
        fields.append(field)
        if len(fields) > MAX_FIELDS:
            raise UnsupportedRecordSourceFragment("too many record fields")
        if peek() != ",":
            break
        take(",")
    take("}")
    tree = {"record": record_name,
            "fields": [{"name": field, "type": {"kind": "m31", "length": 1}}
                       for field in fields]}

    take("circuit")
    circuit_name = identifier()
    if circuit_name == record_name:
        raise UnsupportedRecordSourceFragment("circuit name conflicts with record declaration")
    take("(")
    inputs: list[dict[str, Any]] = []
    roots: dict[str, dict[str, str]] = {}
    structural_inputs: list[dict[str, Any]] = []
    relation_inputs: list[dict[str, Any]] = []
    public_input_words = 0
    while True:
        visibility = take()
        if visibility not in {"public", "private"}:
            raise UnsupportedRecordSourceFragment("expected public or private input")
        root_name = identifier()
        if root_name in roots or root_name in {"result", record_name, circuit_name}:
            raise UnsupportedRecordSourceFragment("duplicate or reserved input root")
        take(":")
        take(record_name)
        root_wires: dict[str, str] = {}
        leaves: list[dict[str, Any]] = []
        for field in fields:
            wire = f"_s31_abi_input_{len(relation_inputs)}"
            root_wires[field] = wire
            relation_inputs.append({"name": wire, "kind": "m31", "length": 1,
                                    "visibility": visibility})
            leaves.append({"path": [{"root": root_name}, {"field": field}],
                           "kind": "m31", "length": 1, "wire": wire})
        roots[root_name] = root_wires
        if _derivation is not None:
            structural_inputs.append({"name": root_name, "visibility": visibility,
                                      "fields": [{"name": field, "wire": root_wires[field]}
                                                 for field in fields]})
        inputs.append({"name": root_name, "type": tree, "visibility": visibility,
                       "leaves": leaves})
        if visibility == "public":
            public_input_words += len(fields)
        if len(inputs) > MAX_INPUTS:
            raise UnsupportedRecordSourceFragment("too many record inputs")
        if peek() != ",":
            break
        take(",")
    take(")")
    take("->")
    take("public")
    take(record_name)
    take("{")
    if public_input_words == 0:
        raise UnsupportedRecordSourceFragment("at least one public record input required")

    lets: dict[str, str] = {}

    def operand() -> tuple[str, dict[str, Any]]:
        name = identifier()
        if peek() == ".":
            take(".")
            field = identifier()
            if name not in roots or field not in roots[name]:
                raise UnsupportedRecordSourceFragment("unknown input field")
            return roots[name][field], {"kind": "project",
                                       "source": {"kind": "name", "name": name},
                                       "field": field}
        if name not in lets:
            raise UnsupportedRecordSourceFragment("unknown or future local wire")
        return lets[name], {"kind": "name", "name": name}

    nodes: list[dict[str, str]] = []
    structural_steps: list[dict[str, Any]] = []
    while peek() == "let":
        take("let")
        name = identifier()
        if name in lets or name in roots or name in {record_name, circuit_name, "result"}:
            raise UnsupportedRecordSourceFragment("duplicate or shadowing local")
        take("=")
        lhs, lhs_expr = operand()
        op = take()
        if op not in {"+", ".*"}:
            raise UnsupportedRecordSourceFragment("unsupported let operator")
        rhs, rhs_expr = operand()
        take(";")
        nodes.append({"name": name, "op": "add" if op == "+" else "mul",
                      "lhs": lhs, "rhs": rhs})
        if _derivation is not None:
            structural_steps.append({"kind": "let", "name": name,
                                     "expr": {"kind": "binary", "op": op,
                                              "lhs": lhs_expr, "rhs": rhs_expr}})
        lets[name] = name
        if len(nodes) > MAX_LETS:
            raise UnsupportedRecordSourceFragment("too many arithmetic lets")

    take(record_name)
    take("{")
    result_fields: dict[str, str] = {}
    structural_result_fields: dict[str, dict[str, Any]] = {}
    while True:
        field = identifier()
        if field not in fields or field in result_fields:
            raise UnsupportedRecordSourceFragment("unknown or duplicate constructor field")
        take(":")
        result_fields[field], structural_result_fields[field] = operand()
        if peek() != ",":
            break
        take(",")
    take("}")
    if set(result_fields) != set(fields):
        raise UnsupportedRecordSourceFragment("constructor omits a record field")
    if peek() == ";":
        take(";")
    take("}")
    if cursor != len(tokens):
        raise UnsupportedRecordSourceFragment("trailing source tokens")

    outputs = [{"path": [{"root": "result"}, {"field": field}],
                "kind": "m31", "length": 1, "wire": result_fields[field]}
               for field in fields]
    public_outputs = list(dict.fromkeys(item["wire"] for item in outputs))
    if public_input_words + len(public_outputs) > 8:
        raise UnsupportedRecordSourceFragment("public word ABI exceeds eight words")
    if _derivation is not None:
        _derivation.append({"fragment": "record-v2", "name": circuit_name,
                            "record": record_name, "fields": fields,
                            "inputs": structural_inputs, "steps": structural_steps,
                            "result": {"kind": "construct", "type": "record",
                                       "name": record_name,
                                       "fields": [{"label": field,
                                                   "value": structural_result_fields[field]}
                                                  for field in structural_result_fields]}})
    return {
        "version": 2, "name": circuit_name, "inputs": relation_inputs,
        "nodes": nodes, "assertions": [], "public_outputs": public_outputs,
        "public_abi": {"schema": "s31-public-record-boundary-v2", "inputs": inputs,
                       "result": {"name": "result", "type": tree, "leaves": outputs}},
    }


def expected_public_abi(relation: dict[str, Any]) -> dict[str, Any]:
    """Independently derive the canonical v2 ABI sidecar from this relation."""
    boundary = relation["public_abi"]
    compact = (json.dumps(boundary, sort_keys=True, separators=(",", ":"),
                          ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")
    return {"schema": "s31-public-abi-v2", "boundary": boundary,
            "boundary_sha256": _digest(ABI_DOMAIN + compact),
            "encoding": ABI_ENCODING}


def check_record_source_relation(source_bytes: bytes, relation_bytes: bytes) -> dict[str, str]:
    expected = parse_record_source_fragment(source_bytes)
    if len(relation_bytes) > MAX_RELATION_BYTES:
        raise ValueError("normalized relation exceeds bounded fragment byte limit")
    actual = parse_canonical_json(relation_bytes, "source.s31.json")
    if not _same_shape(actual, expected):
        raise ValueError("normalized record relation differs from independent source parse")
    return {"capability": CAPABILITY, "source_sha256": _digest(source_bytes),
            "relation_sha256": _digest(relation_bytes)}


def check_package_record_source_relation(package: Path) -> dict[str, str]:
    """Audit source, relation, v2 ABI artifact, and untrusted package hashes."""
    source_bytes = (package / "source.s31").read_bytes()
    relation_bytes = (package / "source.s31.json").read_bytes()
    report = check_record_source_relation(source_bytes, relation_bytes)
    expected = parse_record_source_fragment(source_bytes)
    abi_bytes = (package / "public-abi.json").read_bytes()
    abi = parse_canonical_json(abi_bytes, "public-abi.json")
    if not _same_shape(abi, expected_public_abi(expected)):
        raise ValueError("public record ABI artifact differs from independent source parse")
    manifest = parse_canonical_json((package / "manifest.json").read_bytes(), "manifest.json")
    artifacts = manifest.get("artifacts")
    if (manifest.get("schema") != "s31-package-v1" or
            manifest.get("lowering") != "direct-gate" or
            type(manifest.get("text_frontend_version")) is not int or
            manifest["text_frontend_version"] != 1 or
            manifest.get("name") != expected["name"] or
            manifest.get("source_text_sha256") != report["source_sha256"] or
            manifest.get("program_sha256") != report["relation_sha256"] or
            type(artifacts) is not dict):
        raise ValueError("manifest source/relation identity differs from checked record source")
    for name, data in (("source.s31", source_bytes),
                       ("source.s31.json", relation_bytes),
                       ("public-abi.json", abi_bytes)):
        if artifacts.get(name) != _digest(data):
            raise ValueError(f"manifest artifact hash differs: {name}")
    return report
