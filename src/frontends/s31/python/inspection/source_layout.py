"""Auditable source-level layouts for static S31 records and function APIs."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from s31_stdlib import Type
from language.parser import Parser
from language.syntax import FunctionType, RecordType, TupleType
from text_frontend import compile_text


def describe_type(typ: Type | FunctionType | TupleType | RecordType) -> dict[str, Any]:
    if isinstance(typ, Type):
        kind = typ.kind[4:] if typ.kind.startswith("int_") else typ.kind
        return {"kind": kind, "length": typ.length,
                **({"family": typ.family} if typ.family else {})}
    if isinstance(typ, RecordType):
        return {"struct": typ.name}
    if isinstance(typ, TupleType):
        return {"tuple": [describe_type(item) for item in typ.elements]}
    return {"fn": {"params": [describe_type(item) for item in typ.params],
                   "result": describe_type(typ.result)}}


def flatten(typ: Type | TupleType | RecordType,
            path: tuple[str | int, ...] = ()) -> list[dict[str, Any]]:
    if isinstance(typ, Type):
        kind, length = typ.relation_shape()
        return [{"path": list(path), "type": describe_type(typ),
                 "relation_kind": kind, "relation_length": length}]
    if isinstance(typ, RecordType):
        return [leaf for name, field_type in typ.fields
                for leaf in flatten(field_type, path + (name,))]
    if isinstance(typ, TupleType):
        return [leaf for index, item in enumerate(typ.elements)
                for leaf in flatten(item, path + (index,))]
    raise TypeError("record layout contains a function field")


def source_layout(path: Path) -> dict[str, Any]:
    """Report one validated source snapshot without building a proof package."""
    data = path.read_bytes()
    source = data.decode("utf-8")
    relation, _ = compile_text(source, str(path))
    parser = Parser(source, str(path))
    functions, circuit = parser.parse()
    normalized = (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode()
    records = []
    for name, record in parser.records.items():
        depth, count = parser.record_layouts[name]
        records.append({
            "name": name,
            "fields": [{"name": field, "type": describe_type(typ)}
                       for field, typ in record.fields],
            "flattened_leaves": flatten(record),
            "flattened_leaf_count": count,
            "layout_depth": depth,
        })
    return {
        "schema": "s31-source-layout-v1",
        "source_sha256": hashlib.sha256(data).hexdigest(),
        "normalized_relation_sha256": hashlib.sha256(normalized).hexdigest(),
        "circuit": circuit.name,
        "records": records,
        "functions": [{
            "name": name,
            "params": [{"name": parameter, "type": describe_type(typ)}
                       for parameter, typ in fn.params],
            "result": describe_type(fn.result),
        } for name, fn in functions.items()],
    }
