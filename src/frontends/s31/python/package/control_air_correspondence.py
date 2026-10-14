"""Source-bound local AIR audit for scalar zero-test, selection, and inverse.

This opt-in checker handles one transparent v1 three-node relation. It checks
the installed native Gate inspector's exact gadget graph and key-sealed fixed
columns. The Lean ControlGadgetAir theorems supply all-input local algebra.
The result does not authenticate private witness cells or prove PCS/FRI.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any

from package.effects_gate_ownership import (
    _check_columns, _check_constant_derivations, _load_topology,
)
from package.gate_component_roster import digest as roster_digest
from package.optimizer_receipt import ARTIFACT as OPTIMIZER_ARTIFACT
from package.optimizer_receipt import SCHEMA as OPTIMIZER_SCHEMA
from package.correspondence import parse_canonical_json

SCHEMA = "s31-control-gadget-air-correspondence-v1"
M31 = 2**31 - 1
KINDS = ("add", "sub", "mul", "pointwise_mul")


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _read(package: Path, name: str) -> dict[str, Any]:
    value = parse_canonical_json((package / name).read_bytes(), name)
    _require(type(value) is dict, f"{name} is not an object")
    return value


class _Graph:
    def __init__(self, topology: dict[str, Any]) -> None:
        self.by_output: dict[int, list[tuple[str, dict[str, int]]]] = {}
        for kind in KINDS:
            for gate in topology[kind]:
                _require(type(gate) is dict and set(gate) == {"in0", "in1", "out"} and
                         all(type(value) is int and 0 <= value < topology["n_vars"]
                             for value in gate.values()),
                         "invalid Gate row address")
                self.by_output.setdefault(gate["out"], []).append((kind, gate))

    def output(self, wire: int, kind: str, lhs: int, rhs: int) -> None:
        _require(self.by_output.get(wire) == [
            (kind, {"in0": lhs, "in1": rhs, "out": wire})],
            f"wire {wire} has the wrong unique {kind} producer")

    def many(self, kind: str, lhs: int, rhs: int) -> list[int]:
        return [wire for wire, rows in self.by_output.items()
                if rows == [(kind, {"in0": lhs, "in1": rhs, "out": wire})]]

    def one(self, kind: str, lhs: int, rhs: int) -> int:
        matches = self.many(kind, lhs, rhs)
        _require(len(matches) == 1,
                 f"expected one uniquely owned {kind}({lhs},{rhs}) row")
        return matches[0]

    def anchor(self, difference: int) -> int:
        matches = [wire for wire, rows in self.by_output.items()
                   if rows == [("add", {"in0": wire, "in1": difference,
                                        "out": wire})]]
        _require(len(matches) == 1,
                 f"expected one self-add zero anchor for wire {difference}")
        return matches[0]


def check_control_air(package: Path, topology: dict[str, Any] | None = None) -> dict[str, Any]:
    """Check one source/IR-bound emitted control graph, without a witness."""
    manifest = _read(package, "manifest.json")
    relation = _read(package, "source.s31.json")
    optimizer = _read(package, OPTIMIZER_ARTIFACT)
    key = _read(package, "verification-key.json")
    roster = _read(package, "gate-component-roster.json")
    relation_bytes = (package / "source.s31.json").read_bytes()
    digest = hashlib.sha256(relation_bytes).hexdigest()
    source_digest = hashlib.sha256((package / "source.s31").read_bytes()).hexdigest()
    _require(manifest.get("lowering") == "gate" and
             manifest.get("source_text_sha256") == source_digest and
             manifest.get("optimizer_correspondence_schema") == OPTIMIZER_SCHEMA and
             manifest.get("program_sha256") == key.get("program_sha256") == digest and
             manifest.get("canonical_ir_sha256") == key.get("canonical_ir_sha256") ==
             optimizer.get("canonical_ir_sha256") and
             optimizer.get("program_sha256") == digest and
             optimizer.get("schema") == OPTIMIZER_SCHEMA and
             optimizer.get("aliases") == 0 and
             key.get("preprocessed_root") == roster.get("preprocessed_root") and
             key.get("gate_component_roster_sha256") == roster_digest(roster),
             "source, optimizer, key or fixed roster identity differs")

    inputs = relation.get("inputs")
    nodes = relation.get("nodes")
    _require(relation.get("version") == 1 and
             relation.get("proof_mode", "transparent") == "transparent" and
             type(inputs) is list and len(inputs) == 3 and
             type(nodes) is list and len(nodes) == 3 and
             relation.get("assertions") == [] and
             relation.get("public_outputs") == [nodes[2].get("name")] and
             [item.get("kind") for item in inputs] == ["m31"] * 3 and
             [item.get("length") for item in inputs] == [1, 4, 4] and
             [item.get("visibility") for item in inputs] == ["public", "private", "private"] and
             [item.get("op") for item in nodes] == ["is_zero", "select", "inv"] and
             nodes[0].get("lhs") == inputs[0].get("name") and
             nodes[1].get("selector") == nodes[0].get("name") and
             nodes[1].get("lhs") == inputs[1].get("name") and
             nodes[1].get("rhs") == inputs[2].get("name") and
             nodes[2].get("lhs") == nodes[1].get("name") and
             optimizer.get("source_nodes") == 3 and
             optimizer.get("canonical_nodes") == 6,
             "relation is outside the no-alias control AIR fragment")

    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    if topology is None:
        topology = _load_topology(prover)
    _require(topology.get("schema") == "s31-generic-gate-topology-v1" and
             topology.get("program_sha256") == digest and
             topology.get("canonical_ir_sha256") == key["canonical_ir_sha256"] and
             topology.get("preprocessed_root") == key["preprocessed_root"] and
             type(topology.get("n_vars")) is int and 10 < topology["n_vars"] < M31,
             "native Gate topology is not bound to the sealed source and key")
    _check_columns(topology, roster)
    _check_constant_derivations(topology)
    wires = topology.get("node_wires")
    _require(type(wires) is list and len(wires) == 6 and
             all(type(item) is dict and set(item) == {"id", "wires"} and
                 item["id"] == index and type(item["wires"]) is list and
                 len(item["wires"]) == 1 and type(item["wires"][0]) is int and
                 10 < item["wires"][0] < topology["n_vars"]
                 for index, item in enumerate(wires)),
             "canonical node-wire mapping is incomplete")
    x, a, b, z, picked, inverse = (item["wires"][0] for item in wires)
    graph = _Graph(topology)

    # Finalization proves the public one-word input is a base-field scalar:
    # x .* (1,0,0,0) = x. The reserved wire 1 has that exact value.
    graph.output(x, "pointwise_mul", x, 1)
    one = next((item for item in topology["constants"]
                if item == {"wire": 1, "limbs": [1, 0, 0, 0]}), None)
    _require(one is not None, "reserved one wire lacks the canonical base value")

    # x*u=1-z and x*z=0; each equation is forced by a distinct self-add row.
    complements = graph.many("sub", 1, z)
    _require(len(complements) == 2, "expected distinct zero-test and select complements")
    product_candidates = [(wire, rows[0][1]["in1"])
                          for wire, rows in graph.by_output.items()
                          if len(rows) == 1 and rows[0][0] == "mul" and
                          rows[0][1]["in0"] == x and
                          rows[0][1]["in1"] != z]
    zero_rows = []
    for complement in complements:
        for product, inverse_hint in product_candidates:
            try:
                difference = graph.one("sub", product, complement)
                zero_product = graph.one("mul", x, z)
                graph.anchor(difference)
                graph.anchor(zero_product)
            except ValueError:
                continue
            zero_rows.append((complement, product, inverse_hint, difference, zero_product))
    _require(len(zero_rows) == 1, "zero-test gadget has no unique owned AIR chain")

    # Selection is by the proven scalar z, with full QM31 scalar products.
    select_complement = next(item for item in complements if item != zero_rows[0][0])
    left = graph.one("mul", a, select_complement)
    right = graph.one("mul", b, z)
    graph.output(picked, "add", left, right)

    # All four active inverse lanes are constrained by the exact [1,1,1,1]
    # constant, pointwise product, subtraction, and self-add zero anchor.
    masks = [item["wire"] for item in topology["constants"]
             if item["limbs"] == [1, 1, 1, 1]]
    _require(len(masks) == 1, "inverse has no unique active-one mask")
    product = graph.one("pointwise_mul", picked, inverse)
    inverse_difference = graph.one("sub", product, masks[0])
    graph.anchor(inverse_difference)

    return {
        "schema": SCHEMA,
        "program_sha256": digest,
        "canonical_ir_sha256": key["canonical_ir_sha256"],
        "preprocessed_root": key["preprocessed_root"],
        "source_text_sha256": source_digest,
        "control_nodes": [item["name"] for item in nodes],
        "checked_arithmetic_rows": 13,
        "active_inverse_lanes": 4,
    }
