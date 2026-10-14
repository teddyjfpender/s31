#!/usr/bin/env python3
"""Actual Zig export and missing-owner control for the Lean AIR gate join."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(FORMAL / "tests/audit"))
sys.path.insert(0, str(FORMAL))

from general_structural_native_witness import CASES, case_bytes  # noqa: E402
from scripts.general_structural_native_witness import checked_words, native_check  # noqa: E402
from scripts.native_graph_certificate import check_graph  # noqa: E402

OWNER = FORMAL / ".lake/build/bin/s31-structural-native-gate-ownership-check"
VALUE = FORMAL / ".lake/build/bin/s31-structural-native-trace-check"


def lean_check(checker: Path, paths: list[Path], accepted: bool) -> str:
    result = subprocess.run([str(checker), *(str(path) for path in paths)],
                            cwd=FORMAL, capture_output=True, text=True,
                            check=False, timeout=30)
    if (result.returncode == 0) != accepted:
        raise AssertionError(f"{checker.name}: expected accepted={accepted}, got "
                             f"{result.returncode}: {result.stdout} {result.stderr}")
    return result.stderr


def main() -> None:
    if not OWNER.is_file() or not VALUE.is_file():
        raise RuntimeError("build both structural native Lean checkers first")
    _, source, assignment = next(c for c in CASES if c[0] == "commutative_cse")
    raw = case_bytes(source, assignment)
    inputs, nodes = checked_words(raw)
    with tempfile.TemporaryDirectory(prefix="s31-owned-native-gate-") as temp:
        work = Path(temp)
        graph, exact_bytes = native_check(raw, inputs, nodes, work,
                                          export_graph=True)
        check_graph(graph, raw, inputs, nodes)
        words = {
            "inputs": [assignment["public_inputs"]["x"],
                       assignment["private_inputs"]["y"]],
            "claimed": assignment["public_outputs"]["z"],
        }
        paths = [work / name for name in ("source.s31", "certificate.json",
                                           "graph.json", "words.json")]
        for path, content in zip(paths, (source, raw["certificate"], exact_bytes,
                                         json.dumps(words).encode()), strict=True):
            path.write_bytes(content)
        lean_check(VALUE, paths, True)
        lean_check(OWNER, paths, True)

        # Both source SSA nodes a=x+y and b=y+x map to one canonical wire.
        # Removing its single owning Add gate leaves all supplied wire values
        # and the other gate equations intact. The older value-only checker
        # accepts it, while AIR-derived source ownership must fail.
        first_source_node = graph["source_map"][2]["id"]
        owned_address = graph["node_wires"][first_source_node]["wires"][0]
        left = graph["node_wires"][graph["source_map"][0]["id"]]["wires"][0]
        right = graph["node_wires"][graph["source_map"][1]["id"]]["wires"][0]
        owning = [gate for gate in graph["add"]
                  if gate["out"] == owned_address and
                  {gate["in0"], gate["in1"]} == {left, right}]
        if len(owning) != 1:
            raise AssertionError(f"expected one Zig-owned CSE gate, found {owning}")
        graph["add"].remove(owning[0])
        paths[2].write_text(json.dumps(graph, separators=(",", ":")))
        lean_check(VALUE, paths, True)
        reason = lean_check(OWNER, paths, False)
        if "lacks a direct owning native gate" not in reason:
            raise AssertionError(f"missing-owner mutation failed elsewhere: {reason}")
        print("Zig CSE graph accepted; missing owner passes value check and fails AIR ownership")

        # An honest ordered subtraction is exported with both inputs zero.
        # Reversing only the native Sub operands preserves this one assignment's
        # values and gate equation, but changes the operation for other inputs.
        _, sub_source, _ = next(c for c in CASES if c[0] == "one_lane_private_first")
        sub_assignment = {
            "public_inputs": {"y": [0]},
            "private_inputs": {"x": [0]},
            "public_outputs": {"z": [0]},
        }
        sub_raw = case_bytes(sub_source, sub_assignment)
        sub_inputs, sub_nodes = checked_words(sub_raw)
        sub_graph, sub_bytes = native_check(sub_raw, sub_inputs, sub_nodes, work,
                                            export_graph=True)
        check_graph(sub_graph, sub_raw, sub_inputs, sub_nodes)
        for path, content in zip(paths, (sub_source, sub_raw["certificate"], sub_bytes,
                                         json.dumps({"inputs": [[0], [0]],
                                                     "claimed": [0]}).encode()), strict=True):
            path.write_bytes(content)
        lean_check(VALUE, paths, True)
        lean_check(OWNER, paths, True)
        sub_address = sub_graph["node_wires"][sub_graph["source_map"][2]["id"]]["wires"][0]
        left = sub_graph["node_wires"][sub_graph["source_map"][1]["id"]]["wires"][0]
        right = sub_graph["node_wires"][sub_graph["source_map"][0]["id"]]["wires"][0]
        owning_sub = [gate for gate in sub_graph["sub"] if
                      (gate["in0"], gate["in1"], gate["out"]) ==
                      (left, right, sub_address)]
        if len(owning_sub) != 1 or left == right:
            raise AssertionError("ordered native Sub owner is ambiguous")
        owning_sub[0]["in0"], owning_sub[0]["in1"] = right, left
        paths[2].write_text(json.dumps(sub_graph, separators=(",", ":")))
        lean_check(VALUE, paths, True)
        reason = lean_check(OWNER, paths, False)
        if "lacks a direct owning native gate" not in reason:
            raise AssertionError(f"reversed Sub failed elsewhere: {reason}")
        print("Zig Sub graph accepted; reversed zero-input gate fails ordered ownership")


if __name__ == "__main__":
    main()
