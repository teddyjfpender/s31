#!/usr/bin/env python3
"""Real Zig-export controls for the universal Lean source/graph composition."""

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

CHECKER = FORMAL / ".lake/build/bin/s31-structural-native-trace-check"


def lean_check(work: Path, source: bytes, certificate: bytes, graph: bytes,
               input_words: list[list[int]], claim: list[int], accepted: bool) -> str:
    paths = [work / name for name in ("source.s31", "certificate.json",
                                       "graph.json", "words.json")]
    for path, content in zip(paths, (source, certificate, graph,
                                     json.dumps({"inputs": input_words,
                                                 "claimed": claim}).encode()), strict=True):
        path.write_bytes(content)
    result = subprocess.run([str(CHECKER), *(str(path) for path in paths)],
                            cwd=FORMAL, capture_output=True, text=True,
                            check=False, timeout=30)
    if (result.returncode == 0) != accepted:
        raise AssertionError(f"Lean accepted={result.returncode == 0}, expected={accepted}: "
                             f"{result.stdout} {result.stderr}")
    return result.stderr


def main() -> None:
    if not CHECKER.is_file():
        raise RuntimeError("build s31-structural-native-trace-check first")
    with tempfile.TemporaryDirectory(prefix="s31-lean-native-graph-") as temp:
        work = Path(temp)
        for label in ("commutative_cse", "erased_identities"):
            _, source, assignment = next(case for case in CASES if case[0] == label)
            raw = case_bytes(source, assignment)
            inputs, nodes = checked_words(raw)
            graph, exact_bytes = native_check(raw, inputs, nodes, work,
                                              export_graph=True)
            check_graph(graph, raw, inputs, nodes)
            ssa = json.loads(raw["certificate"])["ssa"]
            names = [item["name"] for item in ssa["inputs"] + ssa["nodes"]]
            if [item["name"] for item in graph["source_map"]] != names:
                raise AssertionError(f"{label}: Zig source-map name order differs")
            input_words = [assignment["public_inputs" if item["visibility"] == "public"
                                      else "private_inputs"][item["name"]]
                           for item in ssa["inputs"]]
            claim = assignment["public_outputs"][nodes[-1]["name"]]
            lean_check(work, source, raw["certificate"], exact_bytes,
                       input_words, claim, True)

            # The JSON stays well formed, all IDs/addresses/values stay intact,
            # and names keep the same byte lengths. The old projection checker
            # discarded names; the composed checker must reject their ownership.
            forged = json.loads(exact_bytes)
            forged["source_map"][0]["name"], forged["source_map"][1]["name"] = (
                forged["source_map"][1]["name"], forged["source_map"][0]["name"])
            changed = json.dumps(forged, separators=(",", ":")).encode()
            reason = lean_check(work, source, raw["certificate"], changed,
                                input_words, claim, False)
            if "source-map names differ" not in reason:
                raise AssertionError(f"{label}: wrong rejection boundary: {reason}")
            print(f"{label}: Zig graph accepted; name permutation rejected")


if __name__ == "__main__":
    main()
