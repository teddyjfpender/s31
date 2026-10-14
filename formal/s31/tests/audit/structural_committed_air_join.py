#!/usr/bin/env python3
"""Join one Lean-checked source graph to a verified direct-Gate proof root.

The finite all-public example checks every fixed/base cell, including the
source multiplication row. It uses the installed verifier as an oracle, not as
a proof of native PCS/FRI soundness or of arbitrary private trace openings.
"""

from __future__ import annotations

import argparse
import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

FORMAL = Path(__file__).resolve().parents[2]
ROOT = FORMAL.parents[1]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(FORMAL))
sys.path.insert(0, str(S31 / "python"))

from scripts.general_structural_native_witness import check as check_graph_source  # noqa: E402
from scripts.structural_committed_air_join import check_columns  # noqa: E402
from structural_derivation_lean import artifacts, canonical  # noqa: E402
from package.fixed_root_join import proof_roots  # noqa: E402
import s31  # noqa: E402

SOURCE = (b"circuit square(public x: [m31; 4]) -> public [m31; 4] { "
          b"let pair = (x, x); let y = pair.0 .* pair.1; y }\n")
ASSIGNMENT = {"public_inputs": {"x": [0, 1, 2, 7]},
              "private_inputs": {}, "public_outputs": {"y": [0, 1, 4, 49]}}


def invoke(binary: Path, *args: Path | str) -> dict:
    return json.loads(s31.invoke(str(binary), *(str(arg) for arg in args)))


def denied(binary: Path, proof: Path, statement: Path, key: Path) -> None:
    result = subprocess.run((str(binary), str(proof), str(statement), str(key)),
                            capture_output=True, text=True, timeout=120, check=False)
    if result.returncode == 0:
        raise AssertionError("altered commitment root was accepted")


def run(work: Path) -> dict:
    work.mkdir(parents=True, exist_ok=True)
    source = work / "square.s31"
    source.write_bytes(SOURCE)
    assignment = work / "assignment.json"
    assignment.write_bytes(canonical(ASSIGNMENT))
    statement = work / "statement.json"
    statement.write_bytes(canonical({key: ASSIGNMENT[key]
                                     for key in ("public_inputs", "public_outputs")}))
    raw = artifacts(SOURCE)
    raw["assignment"] = assignment.read_bytes()
    raw["statement"] = statement.read_bytes()
    paths = []
    for name in ("source", "tree", "certificate", "relation", "abi",
                 "assignment", "statement"):
        path = work / name
        path.write_bytes(raw[name])
        paths.append(path)
    graph_path = work / "native-graph.json"
    source_audit = check_graph_source(paths, graph_path)
    if source_audit["status"] != "accepted":
        raise AssertionError("source/graph certificate did not accept")
    graph = json.loads(graph_path.read_bytes())
    source_digest = hashlib.sha256(SOURCE).hexdigest()
    public_words = [*ASSIGNMENT["public_inputs"]["x"],
                    *ASSIGNMENT["public_outputs"]["y"]]

    package = s31.build(source, work / "package", "direct-gate")
    manifest = s31.verify_package(package)
    if ((package / "source.s31").read_bytes() != SOURCE or
            (package / "source.s31.json").read_bytes() != raw["relation"] or
            manifest.get("source_text_sha256") != source_digest):
        raise ValueError("native package does not embed the Lean-checked source/relation")
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    key = package / "verification-key.json"
    proof = work / "proof.bin"
    s31.invoke(str(prover), "prove", str(assignment), str(proof))
    s31.invoke(str(verifier), str(proof), str(statement), str(key))
    physical = invoke(prover, "inspect-physical-rows", assignment)
    root_report = invoke(prover, "inspect-physical-root", assignment)
    (work / "physical.json").write_bytes(canonical(physical))
    (work / "physical-root.json").write_bytes(canonical(root_report))
    joined = check_columns(graph, physical, root_report,
                           manifest["program_sha256"], public_words)
    source_wire = graph["node_wires"][graph["source_map"][1]["id"]]["wires"][0]
    source_gates = [(index, gate) for index, gate in enumerate(graph["pointwise_mul"])
                    if gate["out"] == source_wire]
    if len(source_gates) != 1:
        raise ValueError("source multiplication lacks one unique native Gate row")
    source_row = sum(len(graph["padded"][op]) for op in ("add", "sub", "mul")) + source_gates[0][0]
    if ([joined["fixed_columns"][column][source_row] for column in range(7)] !=
            [0, 0, 0, 1, source_gates[0][1]["in0"],
             source_gates[0][1]["in1"], source_wire] or
            [joined["main_columns"][column][source_row] for column in range(8, 12)] !=
            ASSIGNMENT["public_outputs"]["y"]):
        raise ValueError("selected source multiplication row differs")

    fixed_input = work / "fixed-columns.json"
    fixed_input.write_bytes(canonical({"schema": "s31-direct-gate-fixed-columns-v1",
                                       "fixed_columns": joined["fixed_columns"]}))
    main_input = work / "main-columns.json"
    main_input.write_bytes(canonical({"schema": "s31-direct-gate-main-columns-v1",
                                      "main_columns": joined["main_columns"]}))
    fixed_commitment = invoke(prover, "inspect-fixed-root-from-columns", fixed_input)
    main_commitment = invoke(prover, "inspect-main-root-from-columns", main_input)
    fixed_root, main_root, main_offset = proof_roots(proof.read_bytes())
    key_data = json.loads(key.read_bytes())
    if (fixed_root.hex() != key_data["preprocessed_root"] or
            fixed_root.hex() != fixed_commitment.get("fixed_root") or
            main_root.hex() != root_report.get("main_root") or
            main_root.hex() != main_commitment.get("main_root") or
            main_commitment.get("main_columns_sha256") != joined["main_columns_sha256"]):
        raise ValueError("source-derived cell commitment differs from accepted proof")

    mutations = 0
    for column_set, column, row in (("fixed_columns", 3, source_row),
                                    ("main_columns", 0, source_row),
                                    ("main_columns", 8, source_row)):
        changed = copy.deepcopy(physical)
        changed[column_set][column][row] ^= 1
        try:
            check_columns(graph, changed, root_report,
                          manifest["program_sha256"], public_words)
        except ValueError:
            mutations += 1
        else:
            raise AssertionError(f"changed {column_set} cell was accepted")
    for label, offset in (("fixed", main_offset - 32), ("main", main_offset)):
        changed = bytearray(proof.read_bytes())
        changed[offset] ^= 1
        wrong_root = work / f"wrong-{label}-root.bin"
        wrong_root.write_bytes(changed)
        denied(verifier, wrong_root, statement, key)
        mutations += 1
    return {"schema": "s31-structural-committed-air-join-v1",
            "source_sha256": source_digest,
            "native_arithmetic_gates": source_audit["arithmetic_gates"],
            "source_mul_row": source_row,
            "source_mul_output_address": source_wire,
            "fixed_cells": joined["fixed_cells"],
            "main_cells": joined["main_cells"],
            "fixed_root": fixed_root.hex(), "main_root": main_root.hex(),
            "main_columns_sha256": joined["main_columns_sha256"],
            "native_verifier_accepted": True,
            "mutations_rejected": mutations}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, help="retain public diagnostic artifacts")
    args = parser.parse_args()
    if args.work is not None:
        print(json.dumps(run(args.work), sort_keys=True))
    else:
        with tempfile.TemporaryDirectory(prefix="s31-structural-committed-air-") as temp:
            print(json.dumps(run(Path(temp)), sort_keys=True))


if __name__ == "__main__":
    main()
