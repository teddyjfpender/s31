#!/usr/bin/env python3
"""Fast Zig-backed structural M31 source-node graph replay controls."""

from __future__ import annotations

import copy
import json
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch

FORMAL = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(FORMAL / "tests/audit"))
sys.path.insert(0, str(FORMAL))
from general_structural_native_witness import (  # noqa: E402
    CASES, case_bytes, rebuild_padded, shift_allocated_addresses,
)
from scripts.general_structural_native_witness import (  # noqa: E402
    checked_words, native_check,
)
from scripts.native_finalization_certificate import Replay  # noqa: E402
from scripts.native_graph_certificate import check_graph  # noqa: E402
from scripts.native_source_node_certificate import packed_broadcast  # noqa: E402


def finalization_suffix(graph: dict, raw: dict[str, bytes], inputs: list[dict]) -> tuple[dict, int]:
    """Construct a coherent finalization tail for an adversarial graph."""
    replay = Replay(graph)
    replay.constants()
    generated = replay.next_fresh - graph["n_vars"]
    start_var = graph["n_vars"] - generated
    for gates in replay.expected.values():
        for gate in gates:
            for field in ("in0", "in1", "out"):
                if gate[field] >= graph["n_vars"]:
                    gate[field] = gate[field] - graph["n_vars"] + start_var
    specs = json.loads(raw["certificate"])["ssa"]["inputs"]
    public_count = 0
    for item, spec in zip(inputs, specs, strict=True):
        if spec["visibility"] == "public":
            public_count += len(item["words"])
        else:
            canonical_id = graph["source_map"][item["id"]]["id"]
            at = graph["node_wires"][canonical_id]["wires"][0]
            replay.expected["add"].append({"in0": at, "in1": 0, "out": at})
    if public_count:
        replay.expected["pointwise_mul"].extend(
            copy.deepcopy(graph["pointwise_mul"][-public_count:]))
    return replay.expected, generated


def coherent_extra_source_constant(exported: dict, raw: dict[str, bytes],
                                   inputs: list[dict]) -> dict:
    """Insert unused but fully finalized broadcast 42 in a source-node span."""
    old_suffix, old_fresh = finalization_suffix(exported, raw, inputs)
    graph = copy.deepcopy(exported)
    first = graph["node_spans"][len(inputs)]["var_start"]
    shift_allocated_addresses(graph, first)
    graph["constant_keys"].append(packed_broadcast(42))
    graph["constant_vars"].append({"idx": first})
    graph["values"][first] = [42] * 4
    for span in graph["node_spans"][len(inputs):]:
        if span["id"] != len(inputs):
            span["var_start"] += 1
        span["var_end"] += 1
    for span in graph["assertion_spans"]:
        span["var_start"] += 1
        span["var_end"] += 1
    for binding in graph["bindings"]:
        binding["conversion_var_start"] += 1
        binding["conversion_var_end"] += 1
    new_suffix, new_fresh = finalization_suffix(graph, raw, inputs)
    assert old_fresh == new_fresh  # the radix chain already constructs 42
    for op in old_suffix:
        cut = len(old_suffix[op])
        graph[op] = (graph[op][:-cut] if cut else graph[op]) + new_suffix[op]
    graph["finalization"]["qm31_end"] += sum(
        len(new_suffix[op]) - len(old_suffix[op]) for op in old_suffix)
    rebuild_padded(graph)
    return graph


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-native-source-node-focus-") as temp:
        work = Path(temp)
        selected = None
        for label, source, assignment in CASES:
            raw = case_bytes(source, assignment)
            inputs, nodes = checked_words(raw)
            graph = native_check(raw, inputs, nodes, work, export_graph=True)
            check_graph(graph, raw, inputs, nodes)
            if label == "three_inputs":
                selected = raw, inputs, nodes, graph
        assert selected is not None
        raw, inputs, nodes, graph = selected
        changed = copy.deepcopy(graph)
        assert changed["canonical_nodes"][3]["tag"] == "add"
        changed["canonical_nodes"][3]["tag"] = "sub"
        # All gate equations, values, phase spans, and padded rows remain
        # untouched. The old audit checked the emitted Add gate against the
        # source expression but trusted this separate canonical tag field.
        with patch("scripts.native_graph_certificate.check_source_nodes", lambda *_: None):
            check_graph(changed, raw, inputs, nodes)
        try:
            check_graph(changed, raw, inputs, nodes)
        except ValueError as exc:
            if "native source node: canonical tag, kind or width differs" not in str(exc):
                raise AssertionError(f"wrong rejection boundary: {exc}") from exc
        else:
            raise AssertionError("forged canonical source opcode was accepted")
        changed = coherent_extra_source_constant(graph, raw, inputs)
        # This is a full satisfying graph: broadcast 42 is interned at a
        # fresh source address and produced by the exact finalization pass;
        # all later addresses, phase spans and padded AIR rows are updated.
        with patch("scripts.native_graph_certificate.check_source_nodes", lambda *_: None):
            check_graph(changed, raw, inputs, nodes)
        try:
            check_graph(changed, raw, inputs, nodes)
        except ValueError as exc:
            if "native source node:" not in str(exc):
                raise AssertionError(f"wrong source allocation rejection: {exc}") from exc
        else:
            raise AssertionError("coherent extra source constant was accepted")
    print(json.dumps({"honest_cases": len(CASES),
                      "forged_canonical_opcode_rejected": True,
                      "coherent_extra_source_constant_rejected": True}, sort_keys=True))


if __name__ == "__main__":
    main()
