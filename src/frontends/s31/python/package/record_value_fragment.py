"""Independent value semantics for the bounded record-source v2 fragment.

This module uses the separately parsed source relation, then evaluates only
its one-word M31 input fields and add/mul lets. It does not call the Zig
interpreter, production parser, compiler, or proof verifier.
"""

from __future__ import annotations

import json
from typing import Any

from package.record_source_fragment import parse_record_source_fragment

P = 2**31 - 1
MAX_ASSIGNMENT_BYTES = 65_536


class InvalidRecordValueFragment(ValueError):
    pass


def _strict_json(data: bytes) -> Any:
    if len(data) > MAX_ASSIGNMENT_BYTES:
        raise InvalidRecordValueFragment("assignment exceeds byte bound")

    def object_pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            if key in result:
                raise InvalidRecordValueFragment("duplicate assignment key")
            result[key] = value
        return result

    try:
        return json.loads(data, object_pairs_hook=object_pairs,
                          parse_constant=lambda _: (_ for _ in ()).throw(
                              InvalidRecordValueFragment("non-JSON number")))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise InvalidRecordValueFragment("invalid assignment JSON") from exc


def _word(value: Any) -> int:
    if (type(value) is not list or len(value) != 1 or
            type(value[0]) is not int or not 0 <= value[0] < P):
        raise InvalidRecordValueFragment("expected one canonical M31 word")
    return value[0]


def evaluate_record_source_assignment(source_bytes: bytes,
                                      assignment_bytes: bytes) -> dict[str, Any]:
    """Check exact flat assignment and compute source-derived public words.

    A mismatched claimed public result rejects, as `Program.evaluate` does.
    Returned leaves preserve the record declaration order and result aliases.
    """
    relation = parse_record_source_fragment(source_bytes)
    assigned = _strict_json(assignment_bytes)
    if type(assigned) is not dict or set(assigned) not in (
            {"public_inputs", "public_outputs"},
            {"public_inputs", "private_inputs", "public_outputs"}):
        raise InvalidRecordValueFragment("invalid assignment fields")
    public = assigned["public_inputs"]
    private = assigned.get("private_inputs", {})
    outputs = assigned["public_outputs"]
    if any(type(group) is not dict for group in (public, private, outputs)):
        raise InvalidRecordValueFragment("assignment groups must be objects")
    expected_public = {item["name"] for item in relation["inputs"]
                       if item["visibility"] == "public"}
    expected_private = {item["name"] for item in relation["inputs"]
                        if item["visibility"] == "private"}
    if (set(public) != expected_public or set(private) != expected_private or
            set(outputs) != set(relation["public_outputs"])):
        raise InvalidRecordValueFragment("assignment wire set differs from source")
    wires: dict[str, int] = {}
    for item in relation["inputs"]:
        group = public if item["visibility"] == "public" else private
        wires[item["name"]] = _word(group[item["name"]])
    for node in relation["nodes"]:
        a, b = wires[node["lhs"]], wires[node["rhs"]]
        wires[node["name"]] = (a + b if node["op"] == "add" else a * b) % P
    for name in relation["public_outputs"]:
        if _word(outputs[name]) != wires[name]:
            raise InvalidRecordValueFragment("claimed public result differs from source evaluation")
    words = [wires[item["name"]] for item in relation["inputs"]
             if item["visibility"] == "public"]
    words.extend(wires[name] for name in relation["public_outputs"])
    words.extend([0] * (8 - len(words)))
    boundary = relation["public_abi"]
    leaves = [leaf for root in boundary["inputs"]
              if root["visibility"] == "public" for leaf in root["leaves"]]
    leaves.extend(boundary["result"]["leaves"])
    return {"capability": "source-to-record-value-only",
            "proof_words": words,
            "leaves": [{"path": leaf["path"], "words": [wires[leaf["wire"]]]}
                       for leaf in leaves]}
