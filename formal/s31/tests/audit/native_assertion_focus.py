#!/usr/bin/env python3
"""Focused native graph audit for structural M31 assertion lowering.

The Lean byte gate is exercised by general_structural_native_witness.py; this
fast graph-only runner checks actual Zig exports and the independent assertion
replay, including an old-checker-accepted always-true Eq mutation.
"""

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
    CASES, case_bytes, rebuild_padded,
)
from scripts.general_structural_native_witness import (  # noqa: E402
    checked_words, native_check,
)
from scripts.native_graph_certificate import check_graph  # noqa: E402


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-native-assertion-focus-") as temp:
        work = Path(temp)
        selected = None
        for label, source, assignment in CASES:
            raw = case_bytes(source, assignment)
            inputs, nodes = checked_words(raw)
            graph = native_check(raw, inputs, nodes, work, export_graph=True)
            check_graph(graph, raw, inputs, nodes)
            if label == "two_public":
                selected = raw, inputs, nodes, graph
        assert selected is not None
        raw, inputs, nodes, graph = selected
        changed = copy.deepcopy(graph)
        changed["eq"][0] = {"in0": 0, "in1": 0}
        rebuild_padded(changed)
        with patch("scripts.native_graph_certificate.check_assertions", lambda *_: None):
            check_graph(changed, raw, inputs, nodes)
        try:
            check_graph(changed, raw, inputs, nodes)
        except ValueError as exc:
            if "native assertion: assertion Eq gate does not bind source wires" not in str(exc):
                raise AssertionError(f"wrong rejection boundary: {exc}") from exc
        else:
            raise AssertionError("always-true Eq graph mutation was accepted")
    print(json.dumps({"honest_cases": len(CASES),
                      "coherent_false_assertion_rejected": True}, sort_keys=True))


if __name__ == "__main__":
    main()
