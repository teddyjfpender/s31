"""Canonical typed record value and statement codec for public ABI v2.

Native key and relation binding lives in ``abi.binding_v2`` and the Zig
``record_abi`` validator; this module handles source-side value layouts.
"""

from __future__ import annotations

import hashlib
import json
import re
from typing import Any

from language.syntax import RecordType, TupleType
from s31_stdlib import Type

M31_MODULUS = 2**31 - 1
MAX_STATEMENT_BYTES = 1_000_000
MAX_PUBLIC_WORDS = 8
MAX_LAYOUT_LEAVES = 1024
_NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9]*\Z")


class AbiError(ValueError):
    """A value or statement violates record ABI v2."""


def _canonical_json(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode("ascii")


def _type_tree(typ: Type | RecordType | TupleType, depth: int,
               active: set[int], names: dict[str, dict[str, Any]],
               leaves: list[int]) -> dict[str, Any]:
    if depth > 32:
        raise AbiError("record layout depth exceeds 32")
    if isinstance(typ, Type):
        leaves[0] += 1
        if leaves[0] > MAX_LAYOUT_LEAVES:
            raise AbiError("public layout has too many leaves")
        return {"kind": typ.kind, "length": typ.length,
                **({"family": typ.family} if typ.family else {})}
    if isinstance(typ, TupleType):
        if not 1 <= len(typ.elements) <= 64:
            raise AbiError("tuple layout needs 1..64 elements")
        if id(typ) in active:
            raise AbiError("recursive public layout")
        active.add(id(typ))
        result = {"tuple": [_type_tree(item, depth + 1, active, names, leaves)
                            for item in typ.elements]}
        active.remove(id(typ))
        return result
    if isinstance(typ, RecordType):
        if not _NAME.fullmatch(typ.name) or not 1 <= len(typ.fields) <= 64:
            raise AbiError("invalid record name or field count")
        field_names = [name for name, _ in typ.fields]
        if any(not _NAME.fullmatch(name) for name in field_names) or len(set(field_names)) != len(field_names):
            raise AbiError("duplicate or invalid record field name")
        if id(typ) in active:
            raise AbiError("recursive public layout")
        active.add(id(typ))
        result = {"record": typ.name,
                  "fields": [{"name": name,
                              "type": _type_tree(field, depth + 1, active, names, leaves)}
                             for name, field in typ.fields]}
        active.remove(id(typ))
        prior = names.setdefault(typ.name, result)
        if prior != result:
            raise AbiError("same nominal record name has different layouts")
        return result
    raise AbiError("function values cannot cross a proof boundary")


def type_tree(typ: Type | RecordType | TupleType) -> dict[str, Any]:
    """Include nominal identity, declaration order, leaf type, and hash family."""
    return _type_tree(typ, 0, set(), {}, [0])


def _word_count(typ: Type | RecordType | TupleType) -> int:
    if isinstance(typ, Type):
        return typ.length
    if isinstance(typ, RecordType):
        return sum(_word_count(field) for _, field in typ.fields)
    return sum(_word_count(item) for item in typ.elements)


def layout_digest(typ: Type | RecordType | TupleType, root: str) -> str:
    """Domain-separated standalone layout digest for typed values."""
    if not _NAME.fullmatch(root):
        raise AbiError("invalid root name")
    layout = {"root": root, "type": type_tree(typ)}
    return hashlib.sha256(b"s31-public-record-abi-v2\0" +
                          _canonical_json(layout)).hexdigest()


def _checked_words(typ: Type, value: object) -> list[int]:
    if not isinstance(value, (list, tuple)) or len(value) != typ.length:
        raise AbiError(f"{typ.kind} value needs {typ.length} word(s)")
    relation_kind, _ = typ.relation_shape()
    limit = 65536 if relation_kind == "u16" else M31_MODULUS
    if typ.kind == "bit":
        limit = 2
    elif typ.kind in {"int_u8", "int_i8"}:
        limit = 256
    if any(type(word) is not int or word < 0 or word >= limit for word in value):
        raise AbiError(f"{typ.kind} has a noncanonical word")
    return list(value)


def _flatten_value(typ: Type | RecordType | TupleType, value: object,
                   path: tuple[tuple[str, str | int], ...]) -> list[dict[str, Any]]:
    if isinstance(typ, Type):
        return [{"path": [{tag: part} for tag, part in path],
                 "words": _checked_words(typ, value)}]
    if isinstance(typ, RecordType):
        names = [name for name, _ in typ.fields]
        if not isinstance(value, dict) or set(value) != set(names) or len(value) != len(names):
            raise AbiError(f"{typ.name} must supply every declared field exactly once")
        return [leaf for name, field_type in typ.fields
                for leaf in _flatten_value(field_type, value[name], path + (("field", name),))]
    if isinstance(typ, TupleType):
        if not isinstance(value, (list, tuple)) or len(value) != len(typ.elements):
            raise AbiError("tuple value has the wrong arity")
        return [leaf for index, field_type in enumerate(typ.elements)
                for leaf in _flatten_value(field_type, value[index], path + (("tuple", index),))]
    raise AbiError("function values cannot cross a proof boundary")


def flatten_value(typ: Type | RecordType | TupleType, value: object,
                  path: tuple[tuple[str, str | int], ...] = ()) -> list[dict[str, Any]]:
    """Flatten a typed value in declaration order with collision-free paths."""
    type_tree(typ)
    return _flatten_value(typ, value, path)


def _decode_tree(typ: Type | RecordType | TupleType, leaves: list[dict[str, Any]],
                 at: int, path: tuple[tuple[str, str | int], ...]) -> tuple[object, int]:
    if isinstance(typ, Type):
        if at >= len(leaves):
            raise AbiError("missing public leaf")
        leaf = leaves[at]
        expected_path = [{tag: part} for tag, part in path]
        if type(leaf) is not dict or set(leaf) != {"path", "words"} or leaf["path"] != expected_path:
            raise AbiError("public leaf path differs from the declared layout")
        return _checked_words(typ, leaf["words"]), at + 1
    if isinstance(typ, RecordType):
        result = {}
        for name, field_type in typ.fields:
            result[name], at = _decode_tree(field_type, leaves, at,
                                            path + (("field", name),))
        return result, at
    if isinstance(typ, TupleType):
        result = []
        for index, field_type in enumerate(typ.elements):
            item, at = _decode_tree(field_type, leaves, at,
                                    path + (("tuple", index),))
            result.append(item)
        return tuple(result), at
    raise AbiError("function values cannot cross a proof boundary")


def encode_statement(typ: Type | RecordType | TupleType, root: str,
                     value: object) -> bytes:
    digest = layout_digest(typ, root)
    if _word_count(typ) > MAX_PUBLIC_WORDS:
        raise AbiError("public statement exceeds eight words")
    leaves = flatten_value(typ, value, (("root", root),))
    encoded = _canonical_json({"version": 2, "layout_sha256": digest,
                               "leaves": leaves})
    if len(encoded) > MAX_STATEMENT_BYTES:
        raise AbiError("invalid public statement size")
    return encoded


def _unique_object(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result = {}
    for key, value in pairs:
        if key in result:
            raise AbiError(f"duplicate JSON key {key}")
        result[key] = value
    return result


def decode_statement(typ: Type | RecordType | TupleType, root: str,
                     encoded: bytes) -> object:
    """Reject noncanonical bytes, layout changes, path changes, and bad words."""
    if type(encoded) is not bytes or len(encoded) > MAX_STATEMENT_BYTES:
        raise AbiError("invalid public statement size")
    try:
        value = json.loads(encoded, object_pairs_hook=_unique_object)
    except AbiError:
        raise
    except (UnicodeDecodeError, json.JSONDecodeError, RecursionError, ValueError) as exc:
        raise AbiError("invalid public statement JSON") from exc
    if _canonical_json(value) != encoded:
        raise AbiError("noncanonical public statement encoding")
    if type(value) is not dict or set(value) != {"version", "layout_sha256", "leaves"}:
        raise AbiError("invalid public statement envelope")
    if type(value["version"]) is not int or value["version"] != 2:
        raise AbiError("wrong public statement version")
    if value["layout_sha256"] != layout_digest(typ, root):
        raise AbiError("public statement layout differs from the declared type")
    if _word_count(typ) > MAX_PUBLIC_WORDS:
        raise AbiError("public statement exceeds eight words")
    leaves = value["leaves"]
    if type(leaves) is not list:
        raise AbiError("public statement leaves must be a list")
    result, used = _decode_tree(typ, leaves, 0, (("root", root),))
    if used != len(leaves):
        raise AbiError("extra public leaf")
    return result
