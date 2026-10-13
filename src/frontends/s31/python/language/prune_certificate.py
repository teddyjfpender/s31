"""Independently check the obligations of conservative relation pruning.

This checker consumes the *before* and *after* normalized relations. It does
not trust the optimizer's liveness walk: every retained node must be an exact
subsequence, every removed node must be a reviewed total M31 operation, and
all public, assertion, ABI, and effect roots must remain reachable. The
corresponding semantic argument is modeled in Lean's ConservativeDeadCode.
"""

from __future__ import annotations

from typing import Any


class PruneCertificateError(ValueError):
    """An optimized relation failed a semantic preservation obligation."""


_RELATION_KEYS = frozenset({
    "version", "name", "proof_mode", "inputs", "nodes", "assertions",
    "public_outputs", "public_abi",
})
_NODE_KEYS = frozenset({
    "name", "op", "lhs", "rhs", "selector", "index", "constant",
    "length", "rounds", "body",
})
_WIRE_KEYS = ("lhs", "rhs", "selector")
_INT_KEYS = ("index", "constant", "length", "rounds")
_TOTAL_SHAPES = {
    "constant": frozenset({"name", "op", "constant", "length"}),
    "add": frozenset({"name", "op", "lhs", "rhs"}),
    "sub": frozenset({"name", "op", "lhs", "rhs"}),
    "mul": frozenset({"name", "op", "lhs", "rhs"}),
    "add_const": frozenset({"name", "op", "lhs", "constant"}),
    "mul_const": frozenset({"name", "op", "lhs", "constant"}),
}
_REPEAT_STEPS = frozenset({"square", "mix4", "add_const", "mul_const"})


def _fail(reason: str) -> None:
    raise PruneCertificateError(reason)


def _review_node(node: Any) -> None:
    if (type(node) is not dict or not set(node) <= _NODE_KEYS or
            type(node.get("name")) is not str or type(node.get("op")) is not str or
            any(key in node and type(node[key]) is not str for key in _WIRE_KEYS) or
            any(key in node and type(node[key]) is not int for key in _INT_KEYS)):
        _fail("unreviewed node shape")
    if "body" in node:
        body = node["body"]
        if node["op"] != "repeat" or type(body) is not list:
            _fail("unreviewed node body")
        for step in body:
            if (type(step) is not dict or not set(step) <= {"op", "constant"} or
                    step.get("op") not in _REPEAT_STEPS or
                    ("constant" in step and type(step["constant"]) is not int) or
                    ((step["op"] in {"square", "mix4"}) == ("constant" in step))):
                _fail("unreviewed repeat step")


def _roots(relation: dict[str, Any]) -> set[str]:
    outputs = relation.get("public_outputs")
    assertions = relation.get("assertions")
    if (type(outputs) is not list or any(type(name) is not str for name in outputs) or
            type(assertions) is not list):
        _fail("invalid public outputs or assertions")
    roots = set(outputs)
    for item in assertions:
        if (type(item) is not dict or set(item) != {"lhs", "rhs"} or
                any(type(item[key]) is not str for key in ("lhs", "rhs"))):
            _fail("invalid assertion")
        roots.update((item["lhs"], item["rhs"]))
    version = relation.get("version")
    if version == 1:
        if "public_abi" in relation:
            _fail("v1 relation has a public ABI")
    elif version == 2:
        abi = relation.get("public_abi")
        if type(abi) is not dict or type(abi.get("inputs")) is not list:
            _fail("invalid v2 public ABI")
        for entry in [*abi["inputs"], abi.get("result")]:
            if type(entry) is not dict or type(entry.get("leaves")) is not list:
                _fail("invalid v2 public ABI root")
            for leaf in entry["leaves"]:
                if type(leaf) is not dict or type(leaf.get("wire")) is not str:
                    _fail("invalid v2 public ABI leaf")
                roots.add(leaf["wire"])
    else:
        _fail("unknown relation version")
    return roots


def verify_pruning(before: Any, before_map: Any,
                   after: Any, after_map: Any) -> tuple[str, ...]:
    """Return removed node names only if the pruned relation is safe.

    An unchanged relation is accepted without interpreting future schemas:
    the optimizer made no semantic transformation in that case. For a changed
    relation, this check fails closed on unknown fields and node shapes.
    """
    if before == after:
        if before_map != after_map:
            _fail("source locations changed without a relation change")
        return ()
    if (type(before) is not dict or type(after) is not dict or
            set(before) != set(after) or not set(before) <= _RELATION_KEYS or
            any(before[key] != after[key] for key in before if key != "nodes")):
        _fail("non-node relation data changed")
    original = before.get("nodes")
    retained = after.get("nodes")
    inputs = before.get("inputs")
    if (type(original) is not list or type(retained) is not list or
            type(inputs) is not list or type(before_map) is not dict or
            type(after_map) is not dict):
        _fail("invalid relation or source-map container")
    input_names: list[str] = []
    for item in inputs:
        if type(item) is not dict or type(item.get("name")) is not str:
            _fail("invalid input")
        input_names.append(item["name"])
    if len(input_names) != len(set(input_names)):
        _fail("duplicate input name")
    known_original = set(input_names)
    for node in original:
        _review_node(node)
        if node["name"] in known_original:
            _fail("duplicate relation name")
        if any(node[key] not in known_original for key in _WIRE_KEYS if key in node):
            _fail("original relation is not topological")
        known_original.add(node["name"])
    roots = _roots(before)
    if not roots <= known_original:
        _fail("original observation has a missing wire")

    # Match exact node dictionaries in order. A renamed or rewritten kept
    # node is never certified as a mere liveness optimization.
    cursor = 0
    removed: list[dict[str, Any]] = []
    for node in original:
        if cursor < len(retained) and retained[cursor] == node:
            cursor += 1
        else:
            removed.append(node)
    if cursor != len(retained) or not removed:
        _fail("retained nodes are not an exact proper subsequence")
    for node in removed:
        if set(node) != _TOTAL_SHAPES.get(node["op"]):
            _fail(f"removed non-total or unreviewed node: {node['name']}")

    known_retained = set(input_names)
    for node in retained:
        if any(node[key] not in known_retained for key in _WIRE_KEYS if key in node):
            _fail(f"retained node has a missing dependency: {node['name']}")
        known_retained.add(node["name"])
    if not roots <= known_retained:
        _fail("public, assertion, or ABI root was removed")
    names = {node["name"] for node in retained}
    expected_map = {name: span for name, span in before_map.items() if name in names}
    if after_map != expected_map:
        _fail("source locations do not match retained nodes")
    return tuple(node["name"] for node in removed)
