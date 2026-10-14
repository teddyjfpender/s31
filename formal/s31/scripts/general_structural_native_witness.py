#!/usr/bin/env python3
"""Check one bounded M31 source and assignment through Lean and native wires.

The Lean statement gate independently parses the exact source, typed tree,
SSA certificate, normalized relation, ABI, assignment and public statement.
After that gate succeeds, this script replays the accepted SSA over canonical
M31 words and checks every native direct-Gate source input, arithmetic node,
gate opcode/operands, and public word. This is a conditional executable
correspondence check for one supplied assignment, not proof verification.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

from scripts.native_graph_certificate import check_graph

FORMAL = Path(__file__).resolve().parents[1]
ROOT = FORMAL.parents[1]
S31 = ROOT / "src/frontends/s31"
CHECKER_SOURCE = FORMAL / "S31/Audit/GeneralLinearSSAStructuralDerivationCheck.lean"
P = 2**31 - 1
MAXIMUM = {"source": 16384, "tree": 131072, "certificate": 65536,
           "relation": 65536, "abi": 65536, "assignment": 65536,
           "statement": 65536}


def read_snapshots(paths: list[Path]) -> dict[str, bytes]:
    result = {}
    for name, path in zip(MAXIMUM, paths, strict=True):
        raw = path.read_bytes()
        if len(raw) > MAXIMUM[name]:
            raise ValueError(f"{name} exceeds bounded byte limit")
        result[name] = raw
    return result


def pin_hashes(raw: dict[str, bytes]) -> None:
    """The Lean parser checks digest syntax; this recomputes their values."""
    tree = json.loads(raw["tree"])
    certificate = json.loads(raw["certificate"])
    for item, name in ((tree, "source"), (tree, "relation"), (tree, "abi"),
                       (certificate, "source"), (certificate, "relation")):
        field = "public_abi_sha256" if name == "abi" else name + "_sha256"
        if item[field] != hashlib.sha256(raw[name]).hexdigest():
            raise ValueError(f"{field} differs from snapshotted {name} bytes")


def lean_check(paths: dict[str, Path]) -> None:
    command = ["lake", "env", "lean", "--run", str(CHECKER_SOURCE)]
    command += ["statement", *(str(paths[name]) for name in MAXIMUM)]
    result = subprocess.run(command, cwd=FORMAL, capture_output=True, text=True,
                            check=False, timeout=60)
    if result.returncode:
        raise ValueError("Lean structural statement gate rejected: " +
                         result.stderr.strip()[-2000:])


def checked_words(raw: dict[str, bytes]) -> tuple[list[dict], list[dict]]:
    ssa = json.loads(raw["certificate"])["ssa"]
    assignment = json.loads(raw["assignment"])
    lanes = ssa["lane_count"]
    if not 1 <= lanes <= 4:
        raise ValueError("native direct-Gate audit admits one to four M31 lanes")
    values: list[list[int]] = []
    inputs: list[dict] = []
    canonical: list[tuple] = []
    source_to_canonical: list[int] = []
    expressions: dict[tuple, int] = {}

    def intern(expression: tuple) -> int:
        if expression not in expressions:
            expressions[expression] = len(canonical)
            canonical.append(expression)
        return expressions[expression]

    for expected_id, item in enumerate(ssa["inputs"]):
        if item["id"] != expected_id:
            raise ValueError("source input IDs are not consecutive")
        key = "public_inputs" if item["visibility"] == "public" else "private_inputs"
        words = assignment[key][item["name"]]
        if (type(words) is not list or len(words) != lanes or
                any(type(word) is not int or not 0 <= word < P for word in words)):
            raise ValueError("source input is not canonical M31")
        values.append(words)
        canonical_id = intern(("input", item["name"]))
        source_to_canonical.append(canonical_id)
        inputs.append({"id": expected_id, "name": item["name"], "words": words,
                       "canonical_id": canonical_id})
    nodes: list[dict] = []
    for step in ssa["nodes"]:
        id_ = step["id"]
        if id_ != len(values):
            raise ValueError("source SSA node IDs are not consecutive")
        lhs = values[step["lhs"]]
        rhs = values[step["rhs"]] if step.get("rhs") is not None else [step["constant"]] * lanes
        op = step["op"]
        if op in ("add", "add_const"):
            words = [(a + b) % P for a, b in zip(lhs, rhs, strict=True)]
        elif op == "sub":
            words = [(a - b) % P for a, b in zip(lhs, rhs, strict=True)]
        elif op in ("mul", "mul_const"):
            words = [(a * b) % P for a, b in zip(lhs, rhs, strict=True)]
        else:
            raise ValueError(f"unsupported native SSA opcode: {op}")
        values.append(words)
        lhs_id = source_to_canonical[step["lhs"]]
        rhs_id = (source_to_canonical[step["rhs"]]
                  if step.get("rhs") is not None else None)
        constant = step.get("constant")
        if (op == "add_const" and constant == 0) or (op == "mul_const" and constant == 1):
            canonical_id = lhs_id
        else:
            if op == "mul_const" and constant == 0:
                expression = ("constant", 0)
            elif canonical[lhs_id][0] == "constant" and op in ("add_const", "mul_const"):
                lhs_constant = canonical[lhs_id][1]
                expression = ("constant", (lhs_constant + constant if op == "add_const"
                                           else lhs_constant * constant) % P)
            elif (rhs_id is not None and canonical[lhs_id][0] == "constant" and
                  canonical[rhs_id][0] == "constant"):
                a, b = canonical[lhs_id][1], canonical[rhs_id][1]
                value = ((a + b) if op == "add" else
                         (a - b) if op == "sub" else a * b) % P
                expression = ("constant", value)
            else:
                if op in ("add", "mul") and lhs_id > rhs_id:
                    lhs_id, rhs_id = rhs_id, lhs_id
                expression = (op, lhs_id, rhs_id, constant)
            canonical_id = intern(expression)
        source_to_canonical.append(canonical_id)
        nodes.append({"id": id_, "name": step["name"], "words": words,
                      "op": op, "lhs": step["lhs"],
                      "rhs": step.get("rhs"), "constant": constant,
                      "canonical_id": canonical_id})
    for left, right in ssa["assertions"]:
        if values[left] != values[right]:
            raise ValueError("source assertion fails for assignment")
    output = values[ssa["output"]]
    relation = json.loads(raw["relation"])
    if assignment["public_outputs"][relation["public_outputs"][0]] != output:
        raise ValueError("source output differs from assigned public claim")
    public_words = [word for item in ssa["inputs"] if item["visibility"] == "public"
                    for word in values[item["id"]]] + output
    if not 1 <= len(public_words) <= 8:
        raise ValueError("native public word width exceeds eight")
    return inputs, nodes


def native_check(raw: dict[str, bytes], inputs: list[dict], nodes: list[dict],
                 work: Path, *, tamper_extra_gate_for_test: bool = False,
                 tamper_changed_gate_for_test: bool = False,
                 export_graph: bool = False) -> dict | None:
    corpus = {"schema": "s31-structural-m31-native-witness-corpus-v1",
              "cases": [{"label": "source-derived-generic", "relation": raw["relation"].decode(),
                         "assignment": raw["assignment"].decode(),
                         "expected_inputs": inputs, "expected_nodes": nodes,
                         "expected_output_source_id": json.loads(raw["certificate"])["ssa"]["output"],
                         "expected_valid": True, "expected_circuit_valid": True,
                         "expected_public_match": True,
                         "tamper_extra_gate_for_test": tamper_extra_gate_for_test,
                         "tamper_changed_gate_for_test": tamper_changed_gate_for_test}]}
    if export_graph:
        corpus["export_graph_path"] = str(work / "native-graph.json")
    path = work / "native-corpus.json"
    path.write_text(json.dumps(corpus, sort_keys=True, separators=(",", ":")) + "\n")
    result = subprocess.run([
        "zig", "build", "--build-file", str(S31 / "build.zig"),
        "structural-native-witness-corpus", "-j1", "--", str(path),
    ], cwd=ROOT, capture_output=True, text=True, check=False, timeout=240)
    if result.returncode or json.loads(result.stdout) != {"checked": 1}:
        raise ValueError("native source-node/witness check rejected: " +
                         result.stderr.strip()[-2000:])
    if export_graph:
        path = work / "native-graph.json"
        if path.stat().st_size > 8 << 20:
            raise ValueError("native graph artifact exceeds bounded byte limit")
        return json.loads(path.read_bytes())
    return None


def check(paths: list[Path], graph_out: Path | None = None) -> dict[str, int | str]:
    raw = read_snapshots(paths)
    pin_hashes(raw)
    with tempfile.TemporaryDirectory(prefix="s31-general-native-structural-") as temp:
        work = Path(temp)
        captured = {}
        for name, value in raw.items():
            path = work / name
            path.write_bytes(value)
            captured[name] = path
        lean_check(captured)
        inputs, nodes = checked_words(raw)
        graph = native_check(raw, inputs, nodes, work, export_graph=True)
        summary = check_graph(graph, raw, inputs, nodes)
        graph_bytes = (work / "native-graph.json").read_bytes()
        if graph_out is not None:
            # The graph contains every private witness value. Never replace an
            # existing path or follow its final symlink; create it mode 0600.
            fd = os.open(graph_out, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
            with os.fdopen(fd, "wb") as out:
                out.write(graph_bytes)
    return {"status": "accepted", "inputs": len(inputs), "nodes": len(nodes),
            "source_sha256": hashlib.sha256(raw["source"]).hexdigest(),
            "graph_sha256": hashlib.sha256(graph_bytes).hexdigest(), **summary}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in MAXIMUM:
        parser.add_argument(name, type=Path)
    parser.add_argument("--graph-out", type=Path,
                        help="write sensitive private-witness graph JSON to a new mode-0600 file")
    args = parser.parse_args()
    try:
        print(json.dumps(check([getattr(args, name) for name in MAXIMUM], args.graph_out),
                         sort_keys=True))
    except (ValueError, KeyError, IndexError, TypeError, OSError,
            subprocess.TimeoutExpired) as exc:
        print(f"rejected: {exc}", file=sys.stderr)
        raise SystemExit(1) from exc


if __name__ == "__main__":
    main()
