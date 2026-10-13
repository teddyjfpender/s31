"""Bounded source-to-generic-Gate fixed-row and public-pin admission.

This is an opt-in verifier-side check over an externally pinned package.  It
checks the exact compiler-exported gates against a separately parsed SSA graph
and hashes the actual dynamic fixed columns against the key-sealed roster.
The native verifier remains responsible for the fixed root and the proof;
the proof does not authenticate the supplied private assignment's identity.
"""

from __future__ import annotations

import hashlib
import json
import struct
import subprocess
from pathlib import Path
from typing import Any

from package.correspondence import parse_canonical_json, same_json_shape
from package.gate_component_roster import digest as roster_digest
from package.source_relation_fragment import (
    LEAN_EFFECTS_PROFILE, check_source_relation_certificate,
)

SCHEMA = "s31-generic-gate-topology-v1"
M31 = 2**31 - 1
MAX_TOPOLOGY_BYTES = 1 << 20
EXPECTED_DYNAMIC_IDS = frozenset((
    "eq_in0_address", "eq_in1_address", "m31_to_u32_input_addr",
    "m31_to_u32_output_addr", "m31_to_u32_multiplicity",
    "qm31_ops_add_flag", "qm31_ops_sub_flag", "qm31_ops_mul_flag",
    "qm31_ops_pointwise_mul_flag", "qm31_ops_in0_address",
    "qm31_ops_in1_address", "qm31_ops_out_address", "qm31_ops_mults",
))
BASIS = ((1, 0, 0, 0), (0, 1, 0, 0), (0, 0, 1, 0), (0, 0, 0, 1))
# Canonical inverses of the engine's i, u and iu basis elements.
BASIS_INV = ((0, M31 - 1, 0, 0),
             (0, 0, 1717986918, 1288490188),
             (0, 0, 1288490188, 429496729))


class UnsupportedEffectsGate(ValueError):
    """The graph has no reviewed four-lane generic Gate schedule."""


def _require(condition: bool, reason: str) -> None:
    if not condition:
        raise ValueError(reason)


def _hash(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _read(package: Path, name: str) -> dict[str, Any]:
    value = parse_canonical_json((package / name).read_bytes(), name)
    _require(type(value) is dict, f"{name} must be an object")
    return value


def _load_topology(prover: Path) -> dict[str, Any]:
    try:
        result = subprocess.run((str(prover), "inspect-gate-topology"),
                                capture_output=True, timeout=30, check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ValueError("pinned generic Gate inspector failed") from exc
    _require(result.returncode == 0 and not result.stdout and
             len(result.stderr) <= MAX_TOPOLOGY_BYTES,
             "bounded generic Gate inspector rejected source or output")

    def unique(items: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in items:
            _require(key not in result, "duplicate generic Gate topology field")
            result[key] = value
        return result

    try:
        value = json.loads(result.stderr, object_pairs_hook=unique)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ValueError("invalid generic Gate topology JSON") from exc
    _require(type(value) is dict and value.get("schema") == SCHEMA,
             "unknown generic Gate topology schema")
    return value


def admitted_ssa(cert: dict[str, Any]) -> bool:
    if (cert.get("lean_semantic_profile") != LEAN_EFFECTS_PROFILE or
            cert.get("unmodeled_features") != []):
        return False
    ssa = cert["ssa"]
    inputs, nodes = ssa["inputs"], ssa["nodes"]
    if (ssa["lane_count"] != 4 or not 1 <= len(inputs) <= 4 or
            sum(item["visibility"] == "public" for item in inputs) != 1 or
            not 1 <= len(nodes) <= 16 or len(ssa["assertions"]) > 16 or
            not len(inputs) <= ssa["output"] < len(inputs) + len(nodes)):
        return False
    # The independent source checker has already checked references.  Avoid
    # CSE and commutative canonicalization changing source IDs or row order.
    seen: set[tuple[Any, ...]] = set()
    for index, node in enumerate(nodes, len(inputs)):
        op, lhs = node["op"], node["lhs"]
        if node["id"] != index or op not in {"add", "sub", "mul", "add_const", "mul_const"}:
            return False
        if op.endswith("_const") and node["constant"] in (0, 1):
            return False
        if op in {"add", "mul"} and lhs > node["rhs"]:
            return False
        key = (op, lhs, node.get("rhs", node.get("constant")))
        if key in seen:
            return False
        seen.add(key)
    return True


def _gate_by_output(gates: list[dict[str, int]], wire: int) -> dict[str, int]:
    found = [gate for gate in gates if gate["out"] == wire]
    _require(len(found) == 1, f"wire {wire} lacks one unique producing Gate row")
    return found[0]


def _cm_mul(x: tuple[int, int], y: tuple[int, int]) -> tuple[int, int]:
    return ((x[0] * y[0] - x[1] * y[1]) % M31,
            (x[0] * y[1] + x[1] * y[0]) % M31)


def _qm_mul(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
    a, b = x[:2], x[2:]
    c, d = y[:2], y[2:]
    ac, bd = _cm_mul(a, c), _cm_mul(b, d)
    ad, bc = _cm_mul(a, d), _cm_mul(b, c)
    # u² = 2 + i and i² = -1.
    return ((ac[0] + 2 * bd[0] - bd[1]) % M31,
            (ac[1] + bd[0] + 2 * bd[1]) % M31,
            (ad[0] + bc[0]) % M31, (ad[1] + bc[1]) % M31)


def _check_constant_derivations(topology: dict[str, Any]) -> None:
    """Derive every interned constant from 0, 1 and u through fixed Gate rows."""
    producers: dict[int, list[tuple[str, dict[str, int]]]] = {}
    for kind in ("add", "sub", "mul", "pointwise_mul"):
        for gate in topology[kind]:
            producers.setdefault(gate["out"], []).append((kind, gate))
    known: dict[int, tuple[int, ...]] = {
        0: (0, 0, 0, 0), 1: (1, 0, 0, 0), 2: (0, 0, 1, 0),
    }
    active: set[int] = set()

    def value(wire: int) -> tuple[int, ...]:
        if wire in known:
            return known[wire]
        rows = producers.get(wire, [])
        _require(len(rows) == 1 and wire not in active,
                 "interned constant has no acyclic unique Gate derivation")
        active.add(wire)
        kind, gate = rows[0]
        lhs, rhs = value(gate["in0"]), value(gate["in1"])
        if kind == "add":
            result = tuple((a + b) % M31 for a, b in zip(lhs, rhs, strict=True))
        elif kind == "sub":
            result = tuple((a - b) % M31 for a, b in zip(lhs, rhs, strict=True))
        elif kind == "mul":
            result = _qm_mul(lhs, rhs)
        else:
            result = tuple((a * b) % M31 for a, b in zip(lhs, rhs, strict=True))
        active.remove(wire)
        known[wire] = result
        return result

    for item in topology["constants"]:
        _require(value(item["wire"]) == tuple(item["limbs"]),
                 "interned constant value differs from Gate derivation")


def _check_columns(topology: dict[str, Any], roster: dict[str, Any]) -> None:
    columns = topology["columns"]
    _require(type(columns) is list and len(columns) == len(EXPECTED_DYNAMIC_IDS) and
             {item["id"] for item in columns} == EXPECTED_DYNAMIC_IDS,
             "generic Gate dynamic column roster is incomplete")
    roster_columns = {item["id"]: item for item in roster["preprocessed_columns"]}
    _require(len(roster_columns) == len(roster["preprocessed_columns"]) == 45,
             "generic Gate roster column count or IDs differ")
    values: dict[str, list[int]] = {}
    for item in columns:
        _require(set(item) == {"id", "values"} and item["id"] in roster_columns,
                 "unexpected dynamic column")
        words = item["values"]
        _require(type(words) is list and 1 <= len(words) <= 1024 and
                 len(words) & (len(words) - 1) == 0 and
                 all(type(word) is int and 0 <= word < M31 for word in words),
                 "invalid generic Gate fixed word")
        column = roster_columns[item["id"]]
        _require(column["rows"] == len(words) and
                 column["log_size"] == len(words).bit_length() - 1 and
                 column["values_sha256"] == _hash(struct.pack(f"<{len(words)}I", *words)),
                 f"generic Gate fixed column {item['id']} differs from key-sealed roster")
        values[item["id"]] = words
    for kind, prefix in (("eq", "eq"), ("m31_to_u32", "m31_to_u32")):
        gates = topology[kind]
        for field, suffix in (("in0", "in0_address"), ("in1", "in1_address")) if kind == "eq" else (("input", "input_addr"), ("out", "output_addr")):
            _require(values[f"{prefix}_{suffix}"] == [gate[field] for gate in gates],
                     f"{kind} exported gates differ from fixed columns")
    kinds = ("add", "sub", "mul", "pointwise_mul")
    gates = [gate for kind in kinds for gate in topology[kind]]
    _require(topology["first_permutation_row"] == len(gates) and
             len(gates) == len(values["qm31_ops_in0_address"]),
             "unexpected generic Gate permutation or row count")
    for field, suffix in (("in0", "in0_address"), ("in1", "in1_address"), ("out", "out_address")):
        _require(values[f"qm31_ops_{suffix}"] == [gate[field] for gate in gates],
                 "generic Gate arithmetic rows differ from fixed columns")
    for kind in kinds:
        expected = [int(item == kind) for item in (
            item for item_kind in kinds for item in [item_kind] * len(topology[item_kind]))]
        _require(values[f"qm31_ops_{kind}_flag"] == expected,
                 "generic Gate operation flags differ from emitted gates")


def check_gate_ownership(package: Path, manifest: dict[str, Any]) -> dict[str, Any]:
    """Check source-derived nodes, assertions and ordered pins against Gate rows."""
    _require(manifest.get("lowering") == "gate" and
             "source_text_sha256" in manifest,
             "Gate ownership requires a text generic Gate package")
    source = (package / "source.s31").read_bytes()
    relation_bytes = (package / "source.s31.json").read_bytes()
    cert = check_source_relation_certificate(
        source, relation_bytes, (package / "source-relation-certificate.json").read_bytes())
    if not admitted_ssa(cert):
        raise UnsupportedEffectsGate("outside reviewed four-lane effectful Gate grammar")
    ssa = cert["ssa"]
    relation, key, report, roster, abi = (_read(package, name) for name in (
        "source.s31.json", "verification-key.json", "cost-report.json",
        "gate-component-roster.json", "public-abi.json"))
    _require(key.get("schema") == "s31-verification-key-gate-roster-v1" and
             key.get("profile") == report.get("profile") == roster.get("profile") == "circuit-v1" and
             key.get("chip") is None and
             key.get("name") == relation.get("name") == report.get("name") and
             key.get("program_sha256") == report.get("program_sha256") ==
             roster.get("program_sha256") == _hash(relation_bytes) and
             key.get("canonical_ir_sha256") == report.get("canonical_ir_sha256") ==
             roster.get("canonical_ir_sha256") and
             key.get("preprocessed_root") == report.get("preprocessed_root") ==
             roster.get("preprocessed_root") and
             key.get("circuit_hash") == report.get("circuit_hash") ==
             roster.get("circuit_hash") and
             key.get("gate_component_roster_sha256") == report.get("gate_component_roster_sha256") and
             key.get("gate_component_roster_sha256") == roster_digest(roster) and
             same_json_shape(roster, report.get("gate_component_roster")) and
             roster.get("schema") == "s31-component-roster-gate-v1" and
             roster.get("air_bundle_sha256") == key.get("air_bundle_sha256"),
             "generic Gate key, cost report or sealed roster differs")
    expected_abi = {
        "schema": "s31-public-abi-v1",
        "encoding": "eight little-endian u32 words; unused words are zero",
        "public_inputs": [{"name": item["name"], "kind": "m31", "length": 4}
                          for item in ssa["inputs"] if item["visibility"] == "public"],
        "public_outputs": [{"name": relation["public_outputs"][0], "kind": "m31", "length": 4}],
    }
    _require(same_json_shape(abi, expected_abi), "generic Gate public ABI differs from source")
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    topology = _load_topology(prover)
    _require(set(topology) == {"schema", "program_sha256", "canonical_ir_sha256",
                               "preprocessed_root", "n_vars", "first_permutation_row",
                               "node_wires", "constants", "output", "add", "sub", "mul",
                               "pointwise_mul", "eq", "m31_to_u32", "columns"} and
             topology["program_sha256"] == _hash(relation_bytes) and
             topology["canonical_ir_sha256"] == key["canonical_ir_sha256"] and
             topology["preprocessed_root"] == key["preprocessed_root"],
             "native topology identity differs from sealed key")
    _check_columns(topology, roster)
    n_vars = topology["n_vars"]
    _require(type(n_vars) is int and 10 < n_vars < M31 and
             all(type(gate) is dict and set(gate) == {"in0", "in1", "out"} and
                 all(type(value) is int and 0 <= value < n_vars for value in gate.values())
                 for kind in ("add", "sub", "mul", "pointwise_mul")
                 for gate in topology[kind]),
             "invalid generic Gate addresses")
    wires = topology["node_wires"]
    _require(len(wires) == len(ssa["inputs"]) + len(ssa["nodes"]) and
             all(set(item) == {"id", "wires"} and item["id"] == index and
                 type(item["wires"]) is list and len(item["wires"]) == 1 and
                 type(item["wires"][0]) is int and 0 <= item["wires"][0] < n_vars
                 for index, item in enumerate(wires)),
             "generic Gate source packed wires differ from SSA")
    node_wire = [item["wires"][0] for item in wires]
    _require(len(set(node_wire)) == len(node_wire) and
             all(wire > 10 for wire in node_wire),
             "source inputs or arithmetic nodes alias a reserved or prior wire")
    constants = topology["constants"]
    _require(all(set(item) == {"wire", "limbs"} and type(item["wire"]) is int and
                 0 <= item["wire"] < n_vars and type(item["limbs"]) is list and
                 len(item["limbs"]) == 4 and
                 all(type(limb) is int and 0 <= limb < M31 for limb in item["limbs"])
                 for item in constants), "invalid generic Gate constants")
    _check_constant_derivations(topology)

    def constant(limbs: tuple[int, int, int, int]) -> int:
        found = [item["wire"] for item in constants if item["limbs"] == list(limbs)]
        _require(len(found) == 1, f"constant {limbs} has no unique native wire")
        return found[0]

    constant_wires = {item["wire"] for item in constants}
    _require(not constant_wires.intersection(node_wire),
             "source node aliases an interned constant wire")

    # A private four-lane input is one unconstrained packed guess whose
    # finalization producer is the canonical self-yield.  Reject aliases to
    # public nodes or arithmetic outputs even if later rows would agree.
    for item in ssa["inputs"]:
        if item["visibility"] != "private":
            continue
        wire = node_wire[item["id"]]
        producers = [(kind, gate) for kind in ("add", "sub", "mul", "pointwise_mul")
                     for gate in topology[kind] if gate["out"] == wire]
        _require(producers == [("add", {"in0": wire, "in1": 0, "out": wire})],
                 "private input lacks its unique packed guess yield")

    # Every source node has one newly produced packed wire and exactly the
    # corresponding operation, with ordered operands for subtraction.
    for node in ssa["nodes"]:
        op = node["op"]
        kind = "pointwise_mul" if op in ("mul", "mul_const") else (
            "add" if op == "add_const" else op)
        gate = _gate_by_output(topology[kind], node_wire[node["id"]])
        rhs = (constant((node["constant"],) * 4) if op.endswith("_const")
               else node_wire[node["rhs"]])
        _require(same_json_shape(gate, {"in0": node_wire[node["lhs"]],
                                        "in1": rhs, "out": node_wire[node["id"]]}),
                 f"source node {node['id']} differs from emitted Gate row")
    spans = report["source_map"]
    _require(len(spans) == len(wires), "source span count differs from SSA")
    cursor = 0
    for index, (item, source_item) in enumerate(zip(spans, [*ssa["inputs"], *ssa["nodes"]], strict=True)):
        expected_rows = (6 if index < len(ssa["inputs"]) and source_item["visibility"] == "public"
                         else 0 if index < len(ssa["inputs"]) else 1)
        _require(item["canonical_id"] == index and item["name"] == source_item["name"] and
                 item["qm31_start"] == cursor and item["qm31_end"] == cursor + expected_rows and
                 item["eq_start"] == item["eq_end"] == 0 and
                 all(item[f"{field}_start"] == item[f"{field}_end"] == 0
                     for field in ("triple_xor", "m31_to_u32", "blake_g")),
                 "source Gate spans differ from four-lane lowering")
        cursor += expected_rows
    _require(same_json_shape(report["input_packing"], [
        {"name": item["name"], "lanes": 4, "qm31_wires": 1}
        for item in ssa["inputs"]]), "generic Gate input packing differs from source")
    assertions = report["assertion_map"]
    _require(len(assertions) == len(ssa["assertions"]), "assertion span count differs")
    for index, ((lhs, rhs), span) in enumerate(zip(ssa["assertions"], assertions, strict=True)):
        _require(same_json_shape(span, {"index": index, "qm31_start": cursor,
                                          "qm31_end": cursor, "eq_start": index,
                                          "eq_end": index + 1}) and
                 same_json_shape(topology["eq"][index],
                                 {"in0": node_wire[lhs], "in1": node_wire[rhs]}),
                 "source assertion differs from emitted Eq row")
    # Reconstruct public scalar input pins from the exact 4-lane pack tree.
    public_id = next(item["id"] for item in ssa["inputs"] if item["visibility"] == "public")
    tail = _gate_by_output(topology["add"], node_wire[public_id])
    middle = _gate_by_output(topology["add"], tail["in0"])
    first = _gate_by_output(topology["add"], middle["in0"])
    raw = [first["in0"]]
    for index, term in enumerate((first["in1"], middle["in1"], tail["in1"]), 1):
        product = _gate_by_output(topology["mul"], term)
        _require(product["in0"] == constant(BASIS[index]),
                 "public input pack basis differs")
        raw.append(product["in1"])
    _require(len(set(raw)) == 4, "public input pack repeats a scalar wire")
    for wire in raw:
        _require(any(gate == {"in0": wire, "in1": constant(BASIS[0]), "out": wire}
                     for gate in topology["pointwise_mul"]),
                 "public input scalar wire lacks an M31 range Gate")
    # Reconstruct output lane extraction from its source packed wire.
    output_wire = node_wire[ssa["output"]]
    extracted = []
    for index, basis in enumerate(BASIS):
        masked = [gate["out"] for gate in topology["pointwise_mul"]
                  if gate["in0"] == output_wire and gate["in1"] == constant(basis)]
        _require(len(masked) == 1, "public output lane lacks unique extraction")
        if index:
            scaled = [gate["out"] for gate in topology["mul"]
                      if gate["in0"] == masked[0] and
                      gate["in1"] == constant(BASIS_INV[index - 1])]
            _require(len(scaled) == 1, "public output lane lacks inverse-basis scaling")
            extracted.append(scaled[0])
        else:
            extracted.append(masked[0])
    _require(len(topology["output"]) == 9 and topology["output"] == list(range(2, 11)),
             "native public output pins differ from eight-word Gate ABI")
    bindings = report["public_binding"]
    _require(len(bindings) == 2, "generic Gate requires one input and one output binding")
    for binding_index, (name, bases) in enumerate(((ssa["inputs"][public_id]["name"], raw),
                                                   (relation["public_outputs"][0], extracted))):
        binding = bindings[binding_index]
        word_start = 4 * binding_index
        _require(binding["name"] == name and binding["word_start"] == word_start and
                 binding["word_count"] == 4 and
                 binding["conversion_m31_to_u32_start"] == word_start and
                 binding["conversion_m31_to_u32_end"] == word_start + 4 and
                 binding["binding_qm31_end"] == binding["binding_qm31_start"] + 4 and
                 (binding["conversion_qm31_end"] - binding["conversion_qm31_start"] ==
                  (0 if binding_index == 0 else 7)),
                 "ordered public binding spans differ from source")
        for lane, base in enumerate(bases):
            position = word_start + lane
            conversion = topology["m31_to_u32"][position]
            _require(conversion["input"] == base and
                     same_json_shape(_gate_by_output(topology["add"], topology["output"][position + 1]),
                                     {"in0": conversion["out"], "in1": 0,
                                      "out": topology["output"][position + 1]}),
                     "public word pin differs from source lane or conversion Gate")
    _require(bindings[0]["conversion_qm31_start"] == cursor and
             bindings[0]["conversion_qm31_end"] == cursor and
             bindings[1]["conversion_qm31_start"] == cursor and
             bindings[1]["conversion_qm31_end"] == cursor + 7 and
             bindings[0]["binding_qm31_start"] == cursor + 7 and
             bindings[1]["binding_qm31_start"] == cursor + 11 and
             report["finalization"]["qm31_start"] == cursor + 15 and
             report["finalization"]["m31_to_u32_start"] == 8 and
             report["raw"]["eq"] == len(ssa["assertions"]) and
             report["raw"]["m31_to_u32"] == 8 and
             key["padded"]["eq"] == len(topology["eq"]) and
             key["padded"]["m31_to_u32"] == len(topology["m31_to_u32"]) and
             key["padded"]["qm31_ops"] == topology["first_permutation_row"],
             "native Gate component sizes differ from inspected rows")
    return {"schema": "s31-effects-generic-gate-ownership-v1",
            "source_sha256": _hash(source), "relation_sha256": _hash(relation_bytes),
            "preprocessed_root": key["preprocessed_root"],
            "node_count": len(ssa["nodes"]), "assertion_count": len(ssa["assertions"]),
            "public_words": 8}
