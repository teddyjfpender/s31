"""Typed source derivations for the independently parsed M31 fragments.

One construct/project rule handles tuple fields, helper arguments, and record
fields. Source parsers emit syntax trees; this module independently replays
their typing and erasure before comparing the complete relation and ABI. It
does not claim production-parser equivalence, native AIR custody, or PCS/FRI
soundness. The v1 Lean byte-run theorem remains a separate required gate.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from package.correspondence import M31_MODULUS, parse_canonical_json, same_json_shape
from package.record_source_fragment import (UnsupportedRecordSourceFragment,
                                            expected_public_abi,
                                            parse_record_source_fragment)
from package.source_relation_fragment import (UnsupportedSourceRelationFragment,
                                              parse_source_fragment)

SCHEMA = "s31-typed-structural-derivation-v1"
ARTIFACT = "typed-structural-derivation.json"
CAPABILITY = "exact-source-to-typed-erasure-and-value-only"
MAX_CERTIFICATE_BYTES = 131_072
MAX_ASSIGNMENT_BYTES = 65_536
DIRECT_ENCODING = "eight canonical M31 words, encoded little-endian u32; unused words are zero"
GATE_ENCODING = "eight little-endian u32 words; unused words are zero"


class UnsupportedStructuralDerivation(ValueError):
    """The source is outside the bounded structural derivation grammars."""


@dataclass(frozen=True)
class Wire:
    name: str
    length: int


@dataclass(frozen=True)
class Literal:
    value: int
    length: int


@dataclass(frozen=True)
class Product:
    kind: str
    name: str | None
    fields: tuple[tuple[str, Wire], ...]


@dataclass(frozen=True)
class Binary:
    op: str
    lhs: Wire | Literal
    rhs: Wire | Literal


Value = Wire | Literal | Product | Binary


def _digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _name(value: Any) -> str:
    if type(value) is not str or not value or len(value) > 128:
        raise ValueError("invalid structural name")
    return value


def _canonical_int(value: Any, minimum: int, maximum: int) -> int:
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError("noncanonical structural integer")
    return value


def _project(product: Product, label: str) -> Wire:
    """The sole elimination rule, shared by tuples, calls, and records."""
    for field, wire in product.fields:
        if field == label:
            return wire
    raise ValueError("projection names no field in the typed product")


def _expression(expr: Any, env: dict[str, Value], helpers: dict[str, dict[str, Any]],
                fragment: str, depth: int = 0) -> Value:
    if type(expr) is not dict or depth > 5:
        raise ValueError("invalid or excessive structural expression")
    kind = expr.get("kind")
    if kind == "name" and set(expr) == {"kind", "name"}:
        name = _name(expr["name"])
        if name not in env:
            raise ValueError("unknown or future structural name")
        return env[name]
    if kind == "literal" and set(expr) == {"kind", "length", "value"}:
        if fragment != "m31-v1":
            raise ValueError("record fragment has no scalar literal")
        return Literal(_canonical_int(expr["value"], 0, M31_MODULUS - 1),
                       _canonical_int(expr["length"], 1, 8))
    if kind == "construct" and set(expr) in (
            {"kind", "type", "fields"}, {"kind", "type", "name", "fields"}):
        form = expr["type"]
        if (form != ("tuple" if fragment == "m31-v1" else "record") or
                (form == "record") != ("name" in expr)):
            raise ValueError("wrong structural constructor type")
        fields = expr["fields"]
        if type(fields) is not list or not 1 <= len(fields) <= 4:
            raise ValueError("invalid structural field count")
        if form == "tuple" and len(fields) < 2:
            raise ValueError("tuple needs at least two fields")
        members: list[tuple[str, Wire]] = []
        for index, field in enumerate(fields):
            if type(field) is not dict or set(field) != {"label", "value"}:
                raise ValueError("invalid structural field")
            label = _name(field["label"])
            if (label in (seen for seen, _ in members) or
                    (form == "tuple" and label != str(index))):
                raise ValueError("duplicate or noncanonical structural field")
            selected = _expression(field["value"], env, helpers, fragment, depth + 1)
            if not isinstance(selected, Wire):
                raise ValueError("structural fields must select M31 wires")
            if members and selected.length != members[0][1].length:
                raise ValueError("structural field shapes differ")
            members.append((label, selected))
        return Product(form, _name(expr["name"]) if form == "record" else None,
                       tuple(members))
    if kind == "project" and set(expr) == {"kind", "source", "field"}:
        source = _expression(expr["source"], env, helpers, fragment, depth + 1)
        if not isinstance(source, Product):
            raise ValueError("projection source is not a product")
        return _project(source, _name(expr["field"]))
    if kind == "binary" and set(expr) == {"kind", "op", "lhs", "rhs"}:
        op = expr["op"]
        if (op not in ({"+", "-", ".*"} if fragment == "m31-v1" else {"+", ".*"})):
            raise ValueError("unsupported structural arithmetic")
        lhs = _expression(expr["lhs"], env, helpers, fragment, depth + 1)
        rhs = _expression(expr["rhs"], env, helpers, fragment, depth + 1)
        if not isinstance(lhs, (Wire, Literal)) or not isinstance(rhs, (Wire, Literal)):
            raise ValueError("arithmetic operands must be M31 values")
        if lhs.length != rhs.length:
            raise ValueError("arithmetic operand shapes differ")
        return Binary(op, lhs, rhs)
    if kind == "apply" and set(expr) == {"kind", "helper", "args"}:
        if fragment != "m31-v1" or expr["helper"] not in helpers:
            raise ValueError("unknown structural helper")
        helper = helpers[expr["helper"]]
        args = expr["args"]
        if type(args) is not list or len(args) != len(helper["params"]):
            raise ValueError("helper arity differs")
        values = [_expression(arg, env, helpers, fragment, depth + 1) for arg in args]
        if any(not isinstance(value, Wire) for value in values):
            raise ValueError("helper arguments must be M31 wires")
        product = Product("tuple", None, tuple((str(index), value)
                                                for index, value in enumerate(values)))
        bound = {param: _project(product, str(index))
                 for index, param in enumerate(helper["params"])}
        result = _expression(helper["body"], bound, {}, fragment, depth + 1)
        if not isinstance(result, Binary):
            raise ValueError("helper must return one arithmetic operation")
        return result
    raise ValueError("unsupported structural expression form")


def _node(name: str, operation: Binary) -> dict[str, Any]:
    lhs, rhs = operation.lhs, operation.rhs
    if isinstance(lhs, Literal) and isinstance(rhs, Literal):
        raise ValueError("constant-only operation is outside fragment")
    if isinstance(lhs, Literal):
        if operation.op == "-":
            raise ValueError("constant-left subtraction is outside fragment")
        lhs, rhs = rhs, lhs
    if not isinstance(lhs, Wire):
        raise ValueError("arithmetic requires a wire")
    if isinstance(rhs, Literal):
        op = "mul_const" if operation.op == ".*" else "add_const"
        constant = ((-rhs.value) % M31_MODULUS if operation.op == "-" else rhs.value)
        return {"name": name, "lhs": lhs.name, "op": op, "constant": constant}
    return {"name": name, "lhs": lhs.name,
            "op": {"+": "add", "-": "sub", ".*": "mul"}[operation.op],
            "rhs": rhs.name}


def derive_relation(program: dict[str, Any]) -> dict[str, Any]:
    """Replay the typed structural rules and derive the complete relation."""
    if type(program) is not dict or program.get("fragment") not in {"m31-v1", "record-v2"}:
        raise ValueError("unknown typed structural derivation fragment")
    fragment = program["fragment"]
    expected_keys = ({"fragment", "name", "inputs", "helpers", "steps", "result"}
                     if fragment == "m31-v1" else
                     {"fragment", "name", "record", "fields", "inputs", "steps", "result"})
    if set(program) != expected_keys:
        raise ValueError("incomplete typed structural derivation")
    name = _name(program["name"])
    source_inputs = program["inputs"]
    steps = program["steps"]
    if type(source_inputs) is not list or not 1 <= len(source_inputs) <= 4 or type(steps) is not list or len(steps) > 48:
        raise ValueError("structural input or step bound exceeded")
    env: dict[str, Value] = {}
    relation_inputs: list[dict[str, Any]] = []
    helpers: dict[str, dict[str, Any]] = {}
    record_name = None
    record_fields: list[str] = []
    if fragment == "m31-v1":
        for helper in program["helpers"]:
            if (type(helper) is not dict or set(helper) != {"name", "params", "body"} or
                    _name(helper["name"]) in helpers or type(helper["params"]) is not list or
                    not 1 <= len(helper["params"]) <= 2):
                raise ValueError("invalid structural helper")
            params = [_name(param) for param in helper["params"]]
            if len(set(params)) != len(params):
                raise ValueError("duplicate helper parameter")
            helpers[helper["name"]] = helper
        if len(helpers) > 8:
            raise ValueError("helper bound exceeded")
        lane_count = None
        for item in source_inputs:
            if type(item) is not dict or set(item) != {"name", "kind", "length", "visibility"}:
                raise ValueError("invalid M31 input declaration")
            input_name = _name(item["name"])
            length = _canonical_int(item["length"], 1, 8)
            if (input_name in env or input_name in helpers or item["kind"] != "m31" or
                    item["visibility"] not in {"public", "private"} or
                    (lane_count is not None and lane_count != length)):
                raise ValueError("M31 input shapes or names differ")
            lane_count = length
            env[input_name] = Wire(input_name, length)
            relation_inputs.append(dict(item))
    else:
        record_name = _name(program["record"])
        record_fields = [_name(field) for field in program["fields"]]
        if not 1 <= len(record_fields) <= 4 or len(set(record_fields)) != len(record_fields) or len(source_inputs) > 2:
            raise ValueError("invalid nominal record fields or input count")
        for root in source_inputs:
            if (type(root) is not dict or set(root) != {"name", "visibility", "fields"} or
                    root["visibility"] not in {"public", "private"} or
                    type(root["fields"]) is not list or
                    [field.get("name") for field in root["fields"]] != record_fields):
                raise ValueError("invalid record input declaration")
            root_name = _name(root["name"])
            if root_name in env:
                raise ValueError("duplicate record input root")
            members = []
            for field in root["fields"]:
                if type(field) is not dict or set(field) != {"name", "wire"}:
                    raise ValueError("invalid record input field")
                wire = _name(field["wire"])
                if wire in (item["name"] for item in relation_inputs):
                    raise ValueError("duplicate flattened record wire")
                relation_inputs.append({"name": wire, "kind": "m31", "length": 1,
                                        "visibility": root["visibility"]})
                members.append((field["name"], Wire(wire, 1)))
            env[root_name] = Product("record", record_name, tuple(members))
        if not any(item["visibility"] == "public" for item in relation_inputs):
            raise ValueError("record needs one public input")

    nodes: list[dict[str, Any]] = []
    assertions: list[dict[str, str]] = []
    for step in steps:
        if type(step) is not dict:
            raise ValueError("invalid structural step")
        if step.get("kind") == "let" and set(step) == {"kind", "name", "expr"}:
            local = _name(step["name"])
            if local in env or local in helpers:
                raise ValueError("duplicate structural local")
            value = _expression(step["expr"], env, helpers, fragment)
            if isinstance(value, Binary):
                nodes.append(_node(local, value))
                value = Wire(local, value.lhs.length)
            env[local] = value
            if len(nodes) > 16:
                raise ValueError("arithmetic node bound exceeded")
        elif step.get("kind") == "assert" and set(step) == {"kind", "lhs", "rhs"}:
            if fragment != "m31-v1":
                raise ValueError("record assertions are outside fragment")
            lhs = _expression(step["lhs"], env, helpers, fragment)
            rhs = _expression(step["rhs"], env, helpers, fragment)
            if not isinstance(lhs, Wire) or not isinstance(rhs, Wire):
                raise ValueError("assertion needs M31 wires")
            assertions.append({"lhs": lhs.name, "rhs": rhs.name})
            if len(assertions) > 16:
                raise ValueError("assertion bound exceeded")
        else:
            raise ValueError("unsupported structural step")
    if not nodes:
        raise ValueError("structural derivation needs arithmetic")
    result = _expression(program["result"], env, helpers, fragment)
    if fragment == "m31-v1":
        if not isinstance(result, Wire) or result.length != relation_inputs[0]["length"]:
            raise ValueError("M31 result shape differs")
        if result.length * (1 + sum(item["visibility"] == "public" for item in relation_inputs)) > 8:
            raise ValueError("M31 public ABI exceeds eight words")
        return {"version": 1, "name": name, "inputs": relation_inputs, "nodes": nodes,
                "assertions": assertions, "public_outputs": [result.name]}
    if (not isinstance(result, Product) or result.kind != "record" or
            result.name != record_name or
            set(field for field, _ in result.fields) != set(record_fields)):
        raise ValueError("record result does not reconstruct declared fields")
    ordered_result = [(field, _project(result, field)) for field in record_fields]
    outputs = list(dict.fromkeys(wire.name for _, wire in ordered_result))
    if sum(item["visibility"] == "public" for item in relation_inputs) + len(outputs) > 8:
        raise ValueError("record public ABI exceeds eight words")
    tree = {"record": record_name,
            "fields": [{"name": field, "type": {"kind": "m31", "length": 1}}
                       for field in record_fields]}
    boundary_inputs = []
    for root in source_inputs:
        leaves = [{"path": [{"root": root["name"]}, {"field": field["name"]}],
                   "kind": "m31", "length": 1, "wire": field["wire"]}
                  for field in root["fields"]]
        boundary_inputs.append({"name": root["name"], "type": tree,
                                "visibility": root["visibility"], "leaves": leaves})
    result_leaves = [{"path": [{"root": "result"}, {"field": field}],
                      "kind": "m31", "length": 1, "wire": wire.name}
                     for field, wire in ordered_result]
    return {"version": 2, "name": name, "inputs": relation_inputs, "nodes": nodes,
            "assertions": [], "public_outputs": outputs,
            "public_abi": {"schema": "s31-public-record-boundary-v2",
                           "inputs": boundary_inputs,
                           "result": {"name": "result", "type": tree,
                                      "leaves": result_leaves}}}


def _parsed_program(source_bytes: bytes) -> tuple[dict[str, Any], dict[str, Any]]:
    derivation: list[dict[str, Any]] = []
    try:
        relation = parse_source_fragment(source_bytes, _derivation=derivation,
                                         _allow_helper_products=True)
    except UnsupportedSourceRelationFragment:
        try:
            relation = parse_record_source_fragment(source_bytes, _derivation=derivation)
        except UnsupportedRecordSourceFragment as exc:
            raise UnsupportedStructuralDerivation("outside both bounded source grammars") from exc
    if len(derivation) != 1:
        raise ValueError("source parser did not emit one structural derivation")
    return relation, derivation[0]


def _expected_abi(relation: dict[str, Any], lowering: str) -> dict[str, Any]:
    if relation["version"] == 2:
        if lowering != "direct-gate":
            raise UnsupportedStructuralDerivation("record fragment requires direct-gate")
        return expected_public_abi(relation)
    if lowering not in {"gate", "direct-gate"}:
        raise UnsupportedStructuralDerivation("unsupported M31 structural lowering")
    length = relation["inputs"][0]["length"]
    return {"schema": "s31-public-abi-v1",
            "encoding": DIRECT_ENCODING if lowering == "direct-gate" else GATE_ENCODING,
            "public_inputs": [{"name": item["name"], "kind": "m31", "length": length}
                              for item in relation["inputs"] if item["visibility"] == "public"],
            "public_outputs": [{"name": relation["public_outputs"][0],
                                "kind": "m31", "length": length}]}


def make_certificate(source_bytes: bytes, relation_bytes: bytes,
                     abi_bytes: bytes, lowering: str) -> dict[str, Any]:
    """Check exact bytes and independently replay the complete typed erasure."""
    parsed_relation, program = _parsed_program(source_bytes)
    derived_relation = derive_relation(program)
    actual_relation = parse_canonical_json(relation_bytes, "source.s31.json")
    actual_abi = parse_canonical_json(abi_bytes, "public-abi.json")
    if (not same_json_shape(derived_relation, parsed_relation) or
            not same_json_shape(actual_relation, derived_relation)):
        raise ValueError("typed structural derivation differs from source relation")
    if not same_json_shape(actual_abi, _expected_abi(derived_relation, lowering)):
        raise ValueError("public ABI differs from typed structural derivation")
    return {"schema": SCHEMA, "capability": CAPABILITY,
            "source_sha256": _digest(source_bytes),
            "relation_sha256": _digest(relation_bytes),
            "public_abi_sha256": _digest(abi_bytes),
            "lowering": lowering, "program": program}


def check_certificate(source_bytes: bytes, relation_bytes: bytes, abi_bytes: bytes,
                      lowering: str, certificate_bytes: bytes) -> dict[str, Any]:
    if len(certificate_bytes) > MAX_CERTIFICATE_BYTES:
        raise ValueError("typed structural certificate exceeds byte bound")
    actual = parse_canonical_json(certificate_bytes, ARTIFACT)
    expected = make_certificate(source_bytes, relation_bytes, abi_bytes, lowering)
    if not same_json_shape(actual, expected):
        raise ValueError("typed structural certificate differs from exact source replay")
    return expected


def _strict_assignment(data: bytes) -> dict[str, Any]:
    if len(data) > MAX_ASSIGNMENT_BYTES:
        raise ValueError("structural assignment exceeds byte bound")

    def pairs(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            if key in result:
                raise ValueError("duplicate structural assignment key")
            result[key] = value
        return result

    try:
        parsed = json.loads(data, object_pairs_hook=pairs,
                            parse_constant=lambda _: (_ for _ in ()).throw(
                                ValueError("non-JSON structural assignment number")))
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("invalid structural assignment JSON") from exc
    if type(parsed) is not dict or set(parsed) != {"public_inputs", "private_inputs",
                                                 "public_outputs"}:
        raise ValueError("structural assignment groups differ")
    if any(type(parsed[key]) is not dict for key in parsed):
        raise ValueError("structural assignment group is not an object")
    return parsed


def evaluate_assignment(certificate: dict[str, Any], assignment_bytes: bytes) -> dict[str, Any]:
    """Compute admitted source values and check an exact flat typed assignment.

    This executable oracle is independent of the production evaluator. It
    gives no native witness-custody theorem; v2 additionally lacks the v1
    exact-byte Lean `Program.evaluate` theorem.
    """
    if certificate.get("schema") != SCHEMA:
        raise ValueError("wrong typed structural certificate schema")
    relation = derive_relation(certificate["program"])
    assigned = _strict_assignment(assignment_bytes)
    public, private, outputs = (assigned[key] for key in
                                ("public_inputs", "private_inputs", "public_outputs"))
    if (set(public) != {item["name"] for item in relation["inputs"]
                       if item["visibility"] == "public"} or
            set(private) != {item["name"] for item in relation["inputs"]
                            if item["visibility"] == "private"} or
            set(outputs) != set(relation["public_outputs"])):
        raise ValueError("structural assignment names differ from source")
    wires: dict[str, list[int]] = {}
    for item in relation["inputs"]:
        group = public if item["visibility"] == "public" else private
        words = group[item["name"]]
        if (type(words) is not list or len(words) != item["length"] or
                any(type(word) is not int or not 0 <= word < M31_MODULUS
                    for word in words)):
            raise ValueError("noncanonical structural M31 input")
        wires[item["name"]] = words
    for node in relation["nodes"]:
        lhs = wires[node["lhs"]]
        if node["op"] in {"add_const", "mul_const"}:
            rhs = [node["constant"]] * len(lhs)
        else:
            rhs = wires[node["rhs"]]
        wires[node["name"]] = [
            ((a + b) if node["op"] in {"add", "add_const"} else
             (a - b) if node["op"] == "sub" else a * b) % M31_MODULUS
            for a, b in zip(lhs, rhs, strict=True)]
    if any(wires[item["lhs"]] != wires[item["rhs"]] for item in relation["assertions"]):
        raise ValueError("source assertion is false")
    for name in relation["public_outputs"]:
        claimed = outputs[name]
        if (type(claimed) is not list or len(claimed) != len(wires[name]) or
                any(type(word) is not int or not 0 <= word < M31_MODULUS
                    for word in claimed) or claimed != wires[name]):
            raise ValueError("claimed public result differs from structural evaluation")
    words = [word for item in relation["inputs"] if item["visibility"] == "public"
             for word in wires[item["name"]]]
    words.extend(word for name in relation["public_outputs"] for word in wires[name])
    if len(words) > 8:
        raise ValueError("structural public words exceed ABI")
    return {"schema": "s31-typed-structural-value-v1",
            "public_words": words + [0] * (8 - len(words)),
            "source_outputs": {name: wires[name] for name in relation["public_outputs"]}}


def verify_artifact(package: Path, manifest: dict[str, Any]) -> bool:
    listed = ARTIFACT in manifest["artifacts"]
    path = package / ARTIFACT
    present = path.exists() or path.is_symlink()
    if "source_text_sha256" not in manifest or manifest.get("correspondence_schema") is not None:
        if listed or present:
            raise ValueError("typed structural artifact requires conservative text source")
        return False
    source_bytes = (package / "source.s31").read_bytes()
    relation_bytes = (package / "source.s31.json").read_bytes()
    abi_bytes = (package / "public-abi.json").read_bytes()
    try:
        expected = make_certificate(source_bytes, relation_bytes, abi_bytes,
                                    manifest["lowering"])
    except UnsupportedStructuralDerivation:
        if listed or present:
            raise ValueError("unsupported source carries typed structural artifact")
        return False
    if (not listed or not path.is_file() or path.is_symlink() or
            manifest["artifacts"][ARTIFACT] != _digest(path.read_bytes())):
        raise ValueError("admitted source lacks sealed typed structural artifact")
    if not same_json_shape(parse_canonical_json(path.read_bytes(), ARTIFACT), expected):
        raise ValueError("typed structural artifact differs from source replay")
    return True
