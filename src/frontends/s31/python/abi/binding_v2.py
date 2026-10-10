"""Reference validator and canonical statement encoder for public record ABI v2.

The native verifier independently binds the relation, key digest, named paths,
and aliased values before admitting the proof statement.
"""

from __future__ import annotations

import hashlib
import json
import re
from collections.abc import Mapping, Sequence
from typing import Any

from abi.record_v2 import AbiError, type_tree
from language.syntax import RecordType, TupleType
from oracle import OracleError, _validated_shapes
from s31_stdlib import Type

SCHEMA = "s31-public-record-boundary-v2"
DOMAIN = b"s31-public-record-boundary-v2\0"
_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")
_MAX_LEAVES = 1024
_MAX_STATEMENT_BYTES = 1_000_000


def _json_bytes(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True, allow_nan=False) + "\n").encode("ascii")


def _name(value: object) -> str:
    if type(value) is not str or len(value) > 128 or not _NAME.fullmatch(value):
        raise AbiError("invalid ABI name")
    return value


def _leaves(tree: object, path: list[dict[str, str | int]], names: dict[str, object],
            depth: int = 0) -> list[dict[str, Any]]:
    if depth > 32 or type(tree) is not dict:
        raise AbiError("invalid ABI type tree")
    if set(tree) == {"kind", "length"}:
        if tree["kind"] != "m31" or type(tree["length"]) is not int or not 1 <= tree["length"] <= 8:
            raise AbiError("v2 first release only supports 1..8 M31 words per leaf")
        return [{"path": path, "kind": "m31", "length": tree["length"]}]
    if set(tree) == {"tuple"}:
        elements = tree["tuple"]
        if type(elements) is not list or not 1 <= len(elements) <= 64:
            raise AbiError("invalid ABI tuple")
        return [leaf for index, element in enumerate(elements)
                for leaf in _leaves(element, path + [{"tuple": index}], names, depth + 1)]
    if set(tree) == {"record", "fields"}:
        record = _name(tree["record"])
        fields = tree["fields"]
        if type(fields) is not list or not 1 <= len(fields) <= 64:
            raise AbiError("invalid ABI record")
        seen: set[str] = set()
        result: list[dict[str, Any]] = []
        for item in fields:
            if type(item) is not dict or set(item) != {"name", "type"}:
                raise AbiError("invalid ABI record field")
            name = _name(item["name"])
            if name in seen:
                raise AbiError("duplicate ABI record field")
            seen.add(name)
            result.extend(_leaves(item["type"], path + [{"field": name}], names, depth + 1))
        prior = names.setdefault(record, tree)
        if prior != tree:
            raise AbiError("same nominal ABI name has different layouts")
        return result
    raise AbiError("invalid ABI type tree")


def _root(root: object, names: dict[str, object], *, input_root: bool) -> list[dict[str, Any]]:
    required = {"name", "type", "leaves", "visibility"} if input_root else {"name", "type", "leaves"}
    if type(root) is not dict or set(root) != required:
        raise AbiError("invalid ABI root descriptor")
    name = _name(root["name"])
    if input_root and root["visibility"] not in ("public", "private"):
        raise AbiError("invalid ABI visibility")
    expected = _leaves(root["type"], [{"root": name}], names)
    if len(expected) > _MAX_LEAVES or type(root["leaves"]) is not list or len(root["leaves"]) != len(expected):
        raise AbiError("ABI root has missing or excessive leaves")
    for actual, declared in zip(root["leaves"], expected):
        if type(actual) is not dict or set(actual) != {"path", "wire", "kind", "length"}:
            raise AbiError("invalid ABI leaf descriptor")
        if (type(actual["length"]) is not int or actual["kind"] != declared["kind"] or
                actual["length"] != declared["length"] or
                _json_bytes(actual["path"]) != _json_bytes(declared["path"])):
            raise AbiError("ABI leaf path or shape differs from the type tree")
        _name(actual["wire"])
    return root["leaves"]


def validate_binding(relation: Mapping[str, Any], binding: object) -> None:
    """Check typed paths, wire binding, aliases, visibility, and proof budget.

    This uses the independent v1 relation shape validator until relation v2
    exists. It cannot authenticate itself: only the future native verifier can
    bind a validated descriptor to a key and proof statement.
    """
    if type(binding) is not dict or set(binding) != {"schema", "inputs", "result"} or binding["schema"] != SCHEMA:
        raise AbiError("invalid ABI boundary descriptor")
    try:
        shapes, _ = _validated_shapes(relation)
    except OracleError as exc:
        raise AbiError("invalid underlying relation") from exc
    inputs = binding["inputs"]
    if type(inputs) is not list or len(inputs) > _MAX_LEAVES:
        raise AbiError("invalid ABI input roots")
    names: dict[str, object] = {}
    root_names: set[str] = set()
    input_wires: list[str] = []
    public_words = 0
    for root in inputs:
        leaves = _root(root, names, input_root=True)
        if root["name"] in root_names:
            raise AbiError("duplicate ABI root name")
        root_names.add(root["name"])
        for leaf in leaves:
            input_wires.append(leaf["wire"])
            if root["visibility"] == "public":
                public_words += leaf["length"]
    relation_inputs = relation["inputs"]
    if (len(input_wires) != len(relation_inputs) or len(set(input_wires)) != len(input_wires) or
            len(input_wires) > _MAX_LEAVES):
        raise AbiError("ABI input leaves do not cover relation inputs exactly")
    at = 0
    for root in inputs:
        for leaf in root["leaves"]:
            raw = relation_inputs[at]
            if (leaf["wire"] != raw["name"] or leaf["kind"] != raw["kind"] or
                    leaf["length"] != raw["length"] or root["visibility"] != raw["visibility"]):
                raise AbiError("ABI input wire, shape, or visibility differs from relation")
            at += 1
    outputs = _root(binding["result"], names, input_root=False)
    if binding["result"]["name"] in root_names:
        raise AbiError("duplicate ABI root name")
    if len(input_wires) + len(outputs) > _MAX_LEAVES:
        raise AbiError("ABI boundary has too many leaves")
    unique_outputs = list(dict.fromkeys(leaf["wire"] for leaf in outputs))
    if unique_outputs != relation["public_outputs"]:
        raise AbiError("ABI result wire order differs from relation public outputs")
    for leaf in outputs:
        if shapes.get(leaf["wire"]) != (leaf["kind"], leaf["length"]):
            raise AbiError("ABI result wire shape differs from relation")
    public_words += sum(shapes[name][1] for name in unique_outputs)
    if not 1 <= public_words <= 8:
        raise AbiError("ABI boundary exceeds eight distinct public words")


def binding_digest(relation: Mapping[str, Any], binding: object) -> str:
    """Hash only a fully validated canonical descriptor."""
    validate_binding(relation, binding)
    encoded = _json_bytes(binding)
    return hashlib.sha256(DOMAIN + encoded).hexdigest()


def _typed_leaves(typ: Type | RecordType | TupleType, root: str,
                  wires: Sequence[str]) -> list[dict[str, Any]]:
    tree = type_tree(typ)
    leaves = _leaves(tree, [{"root": _name(root)}], {})
    if len(wires) != len(leaves):
        raise AbiError("wire count differs from typed leaves")
    return [{**leaf, "wire": _name(wire)} for leaf, wire in zip(leaves, wires)]


def make_binding(
    relation: Mapping[str, Any],
    inputs: Sequence[tuple[str, Type | RecordType | TupleType, str, Sequence[str]]],
    result: tuple[str, Type | RecordType | TupleType, Sequence[str]],
) -> dict[str, Any]:
    """Construct a canonical candidate from elaborated types and wire refs."""
    descriptor = {
        "schema": SCHEMA,
        "inputs": [{"name": name, "type": type_tree(typ), "visibility": visibility,
                    "leaves": _typed_leaves(typ, name, wires)}
                   for name, typ, visibility, wires in inputs],
        "result": {"name": result[0], "type": type_tree(result[1]),
                   "leaves": _typed_leaves(result[1], result[0], result[2])},
    }
    validate_binding(relation, descriptor)
    return descriptor


def _public_leaves(binding: dict[str, Any]) -> list[dict[str, Any]]:
    return [leaf for root in binding["inputs"] if root["visibility"] == "public"
            for leaf in root["leaves"]] + binding["result"]["leaves"]


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for name, value in pairs:
        if name in result:
            raise AbiError("duplicate public statement JSON key")
        result[name] = value
    return result


def decode_public_statement(relation: Mapping[str, Any], binding: dict[str, Any],
                            encoded: bytes) -> list[int]:
    """Reference v2 verifier statement parser; return exactly eight proof words."""
    digest = binding_digest(relation, binding)
    if type(encoded) is not bytes or len(encoded) > _MAX_STATEMENT_BYTES:
        raise AbiError("invalid public statement size")
    try:
        statement = json.loads(encoded, object_pairs_hook=_unique_object)
    except AbiError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, ValueError, RecursionError) as exc:
        raise AbiError("invalid public statement JSON") from exc
    if _json_bytes(statement) != encoded:
        raise AbiError("noncanonical public statement bytes")
    if (type(statement) is not dict or set(statement) != {"version", "abi_sha256", "leaves"} or
            type(statement["version"]) is not int or statement["version"] != 2 or
            statement["abi_sha256"] != digest or type(statement["leaves"]) is not list):
        raise AbiError("invalid public statement envelope or ABI digest")
    expected = _public_leaves(binding)
    actual = statement["leaves"]
    if len(actual) != len(expected):
        raise AbiError("public statement leaf count differs from ABI")
    wire_values: dict[str, list[int]] = {}
    for leaf, declared in zip(actual, expected):
        if (type(leaf) is not dict or set(leaf) != {"path", "words"} or
                _json_bytes(leaf["path"]) != _json_bytes(declared["path"])):
            raise AbiError("public statement leaf path differs from ABI")
        words = leaf["words"]
        if (type(words) is not list or len(words) != declared["length"] or
                any(type(word) is not int or word < 0 or word >= 2**31 - 1 for word in words)):
            raise AbiError("noncanonical public M31 word")
        wire = declared["wire"]
        if wire in wire_values and wire_values[wire] != words:
            raise AbiError("aliased public fields disagree")
        wire_values[wire] = words
    flat = [word for item in relation["inputs"] if item["visibility"] == "public"
            for word in wire_values[item["name"]]]
    flat.extend(word for wire in relation["public_outputs"] for word in wire_values[wire])
    if not 1 <= len(flat) <= 8:
        raise AbiError("invalid public proof-word count")
    return flat + [0] * (8 - len(flat))


def encode_public_statement(relation: Mapping[str, Any], binding: dict[str, Any],
                            words: Sequence[Sequence[int]]) -> bytes:
    """Encode declared public leaves in order, then validate like a verifier."""
    digest = binding_digest(relation, binding)
    expected = _public_leaves(binding)
    if len(words) != len(expected):
        raise AbiError("public statement leaf count differs from ABI")
    encoded = _json_bytes({"version": 2, "abi_sha256": digest,
                           "leaves": [{"path": leaf["path"], "words": value}
                                      for leaf, value in zip(expected, words)]})
    decode_public_statement(relation, binding, encoded)
    return encoded


def statement_from_assignment(source: Mapping[str, Any], assignment: Mapping[str, Any]) -> bytes:
    """Derive the only v2 verifier statement from a prover's flat assignment."""
    if source.get("version") != 2 or type(source.get("public_abi")) is not dict:
        raise AbiError("expected a version 2 relation with a public record boundary")
    base = {**source, "version": 1}
    binding = base.pop("public_abi")
    words: list[list[int]] = []
    for root in binding["inputs"]:
        if root["visibility"] == "public":
            words.extend(assignment["public_inputs"][leaf["wire"]]
                         for leaf in root["leaves"])
    words.extend(assignment["public_outputs"][leaf["wire"]]
                 for leaf in binding["result"]["leaves"])
    return encode_public_statement(base, binding, words)
