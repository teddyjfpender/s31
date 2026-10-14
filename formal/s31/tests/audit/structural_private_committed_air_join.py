#!/usr/bin/env python3
"""Finite private-input source -> exact direct-Gate cells -> accepted roots audit.

The sensitive graph and cell roster exist only in a mode-0700 temporary
directory. The production prover retains its public-only inspection guard.
This transparent proof profile does not promise zero knowledge.
"""

from __future__ import annotations

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
from scripts.general_structural_native_witness import checked_words  # noqa: E402
from scripts.structural_committed_air_join import expected_columns  # noqa: E402
from structural_derivation_lean import artifacts, canonical  # noqa: E402
from package.fixed_root_join import proof_roots  # noqa: E402
import s31  # noqa: E402

SOURCE = (b"circuit private_square(public x: [m31; 4], private y: [m31; 4]) "
          b"-> public [m31; 4] { let pair = (x, y); "
          b"let d = pair.0 - pair.1; let z = d .* d; z }\n")
ASSIGNMENT = {
    "public_inputs": {"x": [5, 8, 13, 21]},
    "private_inputs": {"y": [1, 3, 5, 8]},
    "public_outputs": {"z": [16, 25, 64, 169]},
}


def command(binary: Path, *args: Path | str) -> subprocess.CompletedProcess[str]:
    return subprocess.run((str(binary), *(str(arg) for arg in args)),
                          capture_output=True, text=True, timeout=120, check=False)


def denied(binary: Path, *args: Path | str) -> None:
    if command(binary, *args).returncode == 0:
        raise AssertionError(f"{binary.name} accepted a forbidden private diagnostic or mutant")


def run_corpus(corpus: Path, expected: bool, reason: str = "") -> None:
    result = subprocess.run(("zig", "build", "--build-file", str(S31 / "build.zig"),
                             "structural-native-witness-corpus", "-j1", "--", str(corpus)),
                            cwd=ROOT, capture_output=True, text=True,
                            check=False, timeout=240)
    if expected:
        if result.returncode or json.loads(result.stdout) != {"checked": 1}:
            raise AssertionError("honest native physical audit failed: " + result.stderr[-2500:])
    elif result.returncode == 0 or reason not in result.stderr:
        raise AssertionError("mutant did not fail at " + reason + ": " + result.stderr[-1500:])


def run(work: Path) -> dict:
    source = work / "private_square.s31"
    source.write_bytes(SOURCE)
    assignment = work / "assignment.json"
    assignment.write_bytes(canonical(ASSIGNMENT))
    statement = work / "statement.json"
    statement.write_bytes(canonical({key: ASSIGNMENT[key]
                                     for key in ("public_inputs", "public_outputs")}))
    raw = artifacts(SOURCE)
    raw["assignment"] = assignment.read_bytes()
    raw["statement"] = statement.read_bytes()
    names = ("source", "tree", "certificate", "relation", "abi", "assignment", "statement")
    paths = []
    for name in names:
        path = work / name
        path.write_bytes(raw[name])
        paths.append(path)
    graph_path = work / "native-graph.json"
    accepted = check_graph_source(paths, graph_path)
    if accepted["status"] != "accepted":
        raise AssertionError("Lean/source graph gate rejected private fixture")
    graph = json.loads(graph_path.read_bytes())
    fixed, main = expected_columns(graph)
    inputs, nodes = checked_words(raw)
    source_mul = graph["node_wires"][graph["source_map"][3]["id"]]["wires"][0]
    source_gates = [(i, gate) for i, gate in enumerate(graph["pointwise_mul"])
                    if gate["out"] == source_mul]
    if len(source_gates) != 1:
        raise AssertionError("private source multiplication lacks one native row")
    row = sum(len(graph["padded"][op]) for op in ("add", "sub", "mul")) + source_gates[0][0]
    if ([main[col][row] for col in range(8, 12)] != ASSIGNMENT["public_outputs"]["z"] or
            [main[col][row] for col in range(4)] != [4, 5, 8, 13]):
        raise AssertionError("selected private multiplication row differs")

    package = s31.build(source, work / "package", "direct-gate")
    manifest = s31.verify_package(package)
    if ((package / "source.s31").read_bytes() != SOURCE or
            (package / "source.s31.json").read_bytes() != raw["relation"] or
            manifest.get("source_text_sha256") != hashlib.sha256(SOURCE).hexdigest()):
        raise AssertionError("native private package source identity differs")
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    key = package / "verification-key.json"
    proof = work / "proof.bin"
    s31.invoke(str(prover), "prove", str(assignment), str(proof))
    s31.invoke(str(verifier), str(proof), str(statement), str(key))
    proof_fixed, proof_main, main_offset = proof_roots(proof.read_bytes())
    if proof_fixed.hex() != json.loads(key.read_bytes())["preprocessed_root"]:
        raise AssertionError("accepted proof fixed root differs from sealed key")

    # The installed CLI must continue to reject private witness inspection.
    for option in ("inspect-physical-rows", "inspect-physical-root"):
        denied(prover, option, assignment)

    case = {
        "label": "private-source-physical-join",
        "relation": raw["relation"].decode(),
        "assignment": raw["assignment"].decode(),
        "expected_inputs": inputs,
        "expected_nodes": nodes,
        "expected_output_source_id": 3,
        "expected_valid": True,
        "expected_circuit_valid": True,
        "expected_public_match": True,
        "physical_audit": {
            "fixed_columns": fixed,
            "main_columns": main,
            "accepted_fixed_root": proof_fixed.hex(),
            "accepted_main_root": proof_main.hex(),
            "accepted_proof_path": str(proof),
            "mutated_opening_path": str(work / "changed-main-opening.bin"),
        },
    }
    corpus = work / "physical-corpus.json"

    def check(payload: dict, expected: bool, reason: str = "") -> None:
        corpus.write_bytes(canonical({"schema": "s31-structural-m31-native-witness-corpus-v1",
                                      "cases": [payload]}))
        run_corpus(corpus, expected, reason)

    check(case, True)
    opened_mutant = work / "changed-main-opening.bin"
    if not opened_mutant.is_file():
        raise AssertionError("test-only proof opening mutant was not generated")
    opening_rejection = command(verifier, opened_mutant, statement, key)
    if opening_rejection.returncode == 0 or "RootMismatch" not in opening_rejection.stderr:
        raise AssertionError("changed authenticated main opening did not reach root rejection")
    del case["physical_audit"]["accepted_proof_path"]
    del case["physical_audit"]["mutated_opening_path"]
    mutations = 1
    for kind, column, index, reason in (
        ("fixed_columns", 3, row, "private physical fixed cell differs"),
        ("main_columns", 0, row, "private physical main cell differs"),
        ("main_columns", 8, row, "private physical main cell differs"),
    ):
        mutant = copy.deepcopy(case)
        mutant["physical_audit"][kind][column][index] ^= 1
        check(mutant, False, reason)
        mutations += 1
    for kind, reason in (("accepted_fixed_root", "source-derived fixed root differs"),
                         ("accepted_main_root", "source-derived private main root differs")):
        mutant = copy.deepcopy(case)
        root = mutant["physical_audit"][kind]
        mutant["physical_audit"][kind] = ("0" if root[0] != "0" else "1") + root[1:]
        check(mutant, False, reason)
        mutations += 1
    for label, offset in (("fixed", main_offset - 32), ("main", main_offset)):
        changed = bytearray(proof.read_bytes())
        changed[offset] ^= 1
        mutant = work / f"changed-{label}-proof.bin"
        mutant.write_bytes(changed)
        denied(verifier, mutant, statement, key)
        mutations += 1
    return {"schema": "s31-structural-private-committed-air-join-v1",
            "source_sha256": hashlib.sha256(SOURCE).hexdigest(),
            "private_input_count": 1,
            "source_mul_row": row,
            "fixed_cells": 4096, "main_cells": 6144,
            "native_verifier_accepted": True,
            "mutations_rejected": mutations,
            "production_private_export_rejected": True}


if __name__ == "__main__":
    with tempfile.TemporaryDirectory(prefix="s31-private-committed-air-") as directory:
        print(json.dumps(run(Path(directory)), sort_keys=True))
