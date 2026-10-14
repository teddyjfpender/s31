#!/usr/bin/env python3
"""Fresh Zig finalization path and adversarial controls for folded seven."""

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

FIXED = FORMAL / ".lake/build/bin/s31-structural-native-fixed-constant-check"
VALUE = FORMAL / ".lake/build/bin/s31-structural-native-trace-check"


def check(checker: Path, paths: list[Path], accepted: bool) -> str:
    result = subprocess.run([str(checker), *(str(path) for path in paths)],
                            cwd=FORMAL, capture_output=True, text=True,
                            check=False, timeout=30)
    if (result.returncode == 0) != accepted:
        raise AssertionError(f"{checker.name}: expected accepted={accepted}, "
                             f"got {result.returncode}: {result.stdout} {result.stderr}")
    return result.stderr


def path_from_graph(graph: dict) -> dict[str, int]:
    def output(kind: str, left: int, right: int) -> int:
        matches = [gate["out"] for gate in graph[kind]
                   if gate["in0"] == left and gate["in1"] == right]
        if len(matches) != 1:
            raise AssertionError(f"expected one Zig {kind}({left},{right}), found {matches}")
        return matches[0]

    path: dict[str, int] = {}
    path["base2"] = output("add", 1, 1)
    for value in range(3, 8):
        path[f"base{value}"] = output("add", path[f"base{value-1}"], 1)
    path["uSquare"] = output("mul", 2, 2)
    path["i"] = output("sub", path["uSquare"], path["base2"])
    path["iPlusOne"] = output("add", path["i"], 1)
    path["uPlusIu"] = output("mul", path["iPlusOne"], 2)
    path["ones"] = output("add", path["iPlusOne"], path["uPlusIu"])
    path["broadcast7"] = output("mul", path["base7"], path["ones"])
    if output("mul", 2, 1) != 2 or [0, 0, 1, 0] != graph["values"][2] or \
            not graph["output"] or graph["output"][0] != 2:
        raise AssertionError("Zig public u anchor is not present")
    return path


def main() -> None:
    if not FIXED.is_file() or not VALUE.is_file():
        raise RuntimeError("build fixed-constant and value-only Lean checkers first")
    _, source, assignment = next(case for case in CASES
                                 if case[0] == "folded_constants")
    raw = case_bytes(source, assignment)
    inputs, nodes = checked_words(raw)
    with tempfile.TemporaryDirectory(prefix="s31-fixed-seven-") as temp:
        work = Path(temp)
        graph, exact_bytes = native_check(raw, inputs, nodes, work,
                                          export_graph=True)
        check_graph(graph, raw, inputs, nodes)
        path = path_from_graph(graph)
        source_address = graph["node_wires"][graph["source_map"][3]["id"]]["wires"][0]
        if source_address != path["broadcast7"]:
            raise AssertionError("Zig source z does not own final broadcast-seven wire")
        words = {"inputs": [assignment["public_inputs"]["x"],
                            assignment["private_inputs"]["y"]],
                 "claimed": assignment["public_outputs"]["z"]}
        paths = [work / name for name in ("source.s31", "certificate.json",
                                          "graph.json", "words.json", "path.json")]
        for file, content in zip(paths, (source, raw["certificate"], exact_bytes,
                                         json.dumps(words).encode(),
                                         json.dumps(path).encode()), strict=True):
            file.write_bytes(content)
        check(VALUE, paths[:4], True)
        check(FIXED, paths, True)

        # A different private input has the same sampled value [7,7], but is
        # not a descendant of the finalization chain for literal seven.
        forged = json.loads(exact_bytes)
        forged["source_map"][3]["id"] = forged["source_map"][1]["id"]
        paths[2].write_text(json.dumps(forged, separators=(",", ":")))
        check(VALUE, paths[:4], True)
        reason = check(FIXED, paths, False)
        if "lacks native fixed-chain ownership" not in reason:
            raise AssertionError(f"wrong-origin mutation failed elsewhere: {reason}")

        # The same stored seven words survive removal of the final Mul row.
        forged = json.loads(exact_bytes)
        final_gate = {"in0": path["base7"], "in1": path["ones"],
                      "out": path["broadcast7"]}
        forged["mul"].remove(final_gate)
        paths[2].write_text(json.dumps(forged, separators=(",", ":")))
        check(VALUE, paths[:4], True)
        reason = check(FIXED, paths, False)
        if "fixed-seven path lacks an exact native gate" not in reason:
            raise AssertionError(f"removed broadcast row failed elsewhere: {reason}")

        # The public u output is the only nonzero root. A value-only source
        # check cannot distinguish a forged root with the same source words.
        forged = json.loads(exact_bytes)
        forged["values"][2] = [0, 0, 0, 0]
        paths[2].write_text(json.dumps(forged, separators=(",", ":")))
        check(VALUE, paths[:4], True)
        reason = check(FIXED, paths, False)
        if "native public u anchor differs" not in reason:
            raise AssertionError(f"mutated u anchor failed elsewhere: {reason}")

        forged = json.loads(exact_bytes)
        forged["output"][0] = 1
        paths[2].write_text(json.dumps(forged, separators=(",", ":")))
        check(VALUE, paths[:4], True)
        reason = check(FIXED, paths, False)
        if "native public u anchor differs" not in reason:
            raise AssertionError(f"mutated u output slot failed elsewhere: {reason}")
    print("Zig folded seven accepted; wrong origin, missing Mul, and u-anchor mutants rejected")


if __name__ == "__main__":
    main()
