"""Conservatively erase unobserved, total M31 work from enum-bearing sources.

Source specialization remains strict. This pass sees its completed normalized
relation and removes only nodes known to be total for every well-typed input.
All other operations remain observable roots, including partial operations,
range checks, Boolean constraints, hashes, and chip calls.
"""

from __future__ import annotations

from typing import Any

from abi.binding_v2 import validate_binding


ERASABLE_FIELDS = {
    "constant": frozenset({"name", "op", "constant", "length"}),
    "add": frozenset({"name", "op", "lhs", "rhs"}),
    "mul": frozenset({"name", "op", "lhs", "rhs"}),
    "add_const": frozenset({"name", "op", "lhs", "constant"}),
    "mul_const": frozenset({"name", "op", "lhs", "constant"}),
}
NODE_FIELDS = frozenset({"name", "op", "lhs", "rhs", "selector",
                         "index", "constant", "length", "rounds", "body"})
WIRE_FIELDS = ("lhs", "rhs", "selector")
NUMBER_FIELDS = ("index", "constant", "length", "rounds")
STEP_OPS = frozenset({"square", "mix4", "add_const", "mul_const"})
RELATION_FIELDS = frozenset({"version", "name", "proof_mode", "inputs",
                             "nodes", "assertions", "public_outputs", "public_abi"})


def _reviewed_shape(node: Any) -> bool:
    """Unknown metadata can introduce unknown edges; leave its graph alone."""
    if (type(node) is not dict or not set(node) <= NODE_FIELDS or
            type(node.get("name")) is not str or type(node.get("op")) is not str or
            any(field in node and type(node[field]) is not str for field in WIRE_FIELDS) or
            any(field in node and type(node[field]) is not int for field in NUMBER_FIELDS)):
        return False
    body = node.get("body")
    if body is not None:
        if node["op"] != "repeat" or type(body) is not list:
            return False
        for step in body:
            if (type(step) is not dict or not set(step) <= {"op", "constant"} or
                    step.get("op") not in STEP_OPS or
                    ("constant" in step and type(step["constant"]) is not int)):
                return False
            if (step["op"] in {"square", "mix4"}) == ("constant" in step):
                return False
    elif "body" in node:
        return False
    if node["op"] in ERASABLE_FIELDS and set(node) != ERASABLE_FIELDS[node["op"]]:
        return False
    return True


def _abi_wires(relation: dict[str, Any]) -> set[str] | None:
    if relation.get("version") == 1:
        return set() if "public_abi" not in relation else None
    if relation.get("version") != 2:
        return None
    descriptor = relation.get("public_abi")
    if type(descriptor) is not dict or type(descriptor.get("inputs")) is not list:
        return None
    roots = [*descriptor["inputs"], descriptor.get("result")]
    wires: set[str] = set()
    for root in roots:
        if type(root) is not dict or type(root.get("leaves")) is not list:
            return None
        for leaf in root["leaves"]:
            if type(leaf) is not dict or type(leaf.get("wire")) is not str:
                return None
            wires.add(leaf["wire"])
    return wires


def prune_total_dead_nodes(
    relation: dict[str, Any], source_map: dict[str, dict[str, int]],
) -> tuple[dict[str, Any], dict[str, dict[str, int]]]:
    """Preserve all roots and their ancestors; fail closed on unknown shapes."""
    nodes = relation.get("nodes")
    assertions = relation.get("assertions")
    outputs = relation.get("public_outputs")
    abi_wires = _abi_wires(relation)
    if (type(relation) is not dict or not set(relation) <= RELATION_FIELDS or
            type(nodes) is not list or type(assertions) is not list or
            type(outputs) is not list or abi_wires is None or
            any(not _reviewed_shape(node) for node in nodes) or
            any(type(item) is not dict or set(item) != {"lhs", "rhs"} or
                type(item["lhs"]) is not str or type(item["rhs"]) is not str
                for item in assertions) or
            any(type(name) is not str for name in outputs)):
        return relation, source_map

    live = set(outputs) | abi_wires
    live.update(name for item in assertions for name in (item["lhs"], item["rhs"]))
    kept: list[dict[str, Any]] = []
    for node in reversed(nodes):
        if node["name"] in live or node["op"] not in ERASABLE_FIELDS:
            kept.append(node)
            live.update(node[field] for field in WIRE_FIELDS if field in node)
    kept.reverse()
    if len(kept) == len(nodes):
        return relation, source_map

    # The native relation requires topological references. Fail closed if an
    # unreviewed path or future schema change would leave a dangling wire.
    inputs = relation.get("inputs")
    if type(inputs) is not list or any(type(item) is not dict or
                                        type(item.get("name")) is not str for item in inputs):
        return relation, source_map
    known = {item["name"] for item in inputs}
    for node in kept:
        if any(node[field] not in known for field in WIRE_FIELDS if field in node):
            return relation, source_map
        known.add(node["name"])
    if any(name not in known for name in live):
        return relation, source_map

    pruned = {**relation, "nodes": kept}
    if relation.get("version") == 2:
        base = {**pruned, "version": 1}
        descriptor = base.pop("public_abi")
        validate_binding(base, descriptor)
    names = {node["name"] for node in kept}
    return pruned, {name: span for name, span in source_map.items() if name in names}
