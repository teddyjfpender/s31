#!/usr/bin/env python3
"""Recommit four source-checked fixed rosters and join accepted proof roots.

Each case uses a fresh direct-Gate package and native export. This finite
regression does not authenticate arbitrary PCS openings or prove Merkle/FRI
soundness.
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

import alias8_fixed_root_recommit as fixed
import full_native_roster as roster


def rejected_input(prover: Path, columns: list[list[int]], work: Path,
                   name: str, wanted: str) -> None:
    path = work / f"{name}.json"
    path.write_text(json.dumps({"schema": "s31-direct-gate-fixed-columns-v1",
                                "fixed_columns": columns}, separators=(",", ":")))
    result = subprocess.run((str(prover), "inspect-fixed-root-from-columns", str(path)),
                            capture_output=True, text=True, timeout=120, check=False)
    if result.returncode == 0 or wanted not in result.stderr:
        raise AssertionError(f"{name} was not rejected at {wanted}: {result.stderr}")


def check_mutations(prover: Path, columns: list[list[int]], root: str,
                    work: Path, prefix: str) -> list[str]:
    """Controls exercise the same native commitment path as the honest case."""
    mutations = {
        "selector": (0, 16),
        "source-address": (4, 0),
        "multiplicity": (7, 16),
    }
    rejected = []
    for name, (column, row) in mutations.items():
        changed = copy.deepcopy(columns)
        changed[column][row] = (changed[column][row] + 1) % roster.P
        if fixed.recommit(prover, changed, work, f"{prefix}-{name}") == root:
            raise AssertionError(f"{prefix}: {name} changed cell retained sealed root")
        rejected.append(name)
    swapped = copy.deepcopy(columns)
    swapped[4], swapped[5] = swapped[5], swapped[4]
    if fixed.recommit(prover, swapped, work, f"{prefix}-column-order") == root:
        raise AssertionError(f"{prefix}: fixed-column swap retained sealed root")
    rejected.append("column-order")

    noncanonical = copy.deepcopy(columns)
    noncanonical[0][16] = roster.P
    rejected_input(prover, noncanonical, work, f"{prefix}-noncanonical",
                   "NonCanonicalM31Word")
    rejected.append("noncanonical")
    short = copy.deepcopy(columns)
    short[0].pop()
    rejected_input(prover, short, work, f"{prefix}-short", "InvalidDirectTraceShape")
    rejected.append("short-column")
    return rejected


def run_case(work: Path, sample, prefix: str, pinned: dict) -> dict:
    print(f"fixed-root proof join: {sample.label}", file=sys.stderr, flush=True)
    case_work = work / prefix
    case_work.mkdir(parents=True, exist_ok=True)
    data, proof = roster.native_case(case_work, sample, prefix, pinned)
    # native_case checks the fresh source-bound package, topology export,
    # complete source schedule, physical row export, and accepted proof bytes.
    fixture = roster.FIXTURES / f"{prefix}-full-native-roster.json"
    if data != json.loads(fixture.read_bytes()):
        raise ValueError(f"{prefix}: fresh native diagnostic differs from pinned fixture")
    columns = data["physical"]["fixed_columns"]
    package = case_work / f"package-{prefix}"
    manifest = roster.s31.verify_package(package)
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    root = fixed.recommit(prover, columns, case_work, "honest")
    if (root != data["sealed_key_root"] or
            root != proof["proof_fixed_root"] or
            root != data["topology"]["preprocessed_root"]):
        raise ValueError(f"{prefix}: native recommit, key, topology, and accepted proof roots differ")
    trial_dir = case_work / f"trial-{sample.label.replace(':', '-')}"
    accepted = (trial_dir / "proof.bin").read_bytes()
    if hashlib.sha256(accepted).hexdigest() != proof["proof_sha256"]:
        raise ValueError(f"{prefix}: accepted proof bytes differ from reported digest")
    first, _, main_offset = roster.proof_roots(accepted)
    if first.hex() != root:
        raise ValueError(f"{prefix}: decoded accepted proof root differs from recommitment")
    changed = bytearray(accepted)
    changed[main_offset - 32] ^= 1
    mutant = case_work / "wrong-fixed-root.bin"
    mutant.write_bytes(changed)
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    denied = subprocess.run((str(verifier), str(mutant), str(trial_dir / "statement.json"),
                             str(package / "verification-key.json")),
                            capture_output=True, text=True, timeout=120, check=False)
    if denied.returncode == 0 or denied.stderr.strip() != "error: InvalidPreprocessedRoot":
        raise AssertionError(f"{prefix}: one-byte proof fixed-root mutation was not rejected: "
                             f"{denied.stderr}")
    rejected = check_mutations(prover, columns, root, case_work, prefix)
    return {"label": sample.label, "source_sha256": data["source_sha256"],
            "fixed_cells": 4096, "native_recommitted_root": root,
            "sealed_key_root": data["sealed_key_root"],
            "accepted_proof_fixed_root": proof["proof_fixed_root"],
            "accepted_proof_sha256": proof["proof_sha256"],
            "native_verifier_accepted": proof["native_verifier_accepted"],
            "proof_fixed_root_mutation_rejected": "InvalidPreprocessedRoot",
            "mutations_rejected": rejected}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--case", choices=[prefix for _, prefix in roster.SELECTED],
                        help="run one of the four pinned cases (default: all)")
    parser.add_argument("--work", type=Path, help="retain packages, exports and proofs")
    args = parser.parse_args()
    selected = [(sample, prefix) for sample, prefix in roster.selected_samples()
                if args.case is None or prefix == args.case]
    pinned = roster.pinned_cases()
    if args.work:
        work = args.work.resolve()
        work.mkdir(parents=True, exist_ok=True)
        results = [run_case(work, sample, prefix, pinned[sample.label])
                   for sample, prefix in selected]
    else:
        with tempfile.TemporaryDirectory(prefix="s31-four-case-fixed-root-") as directory:
            work = Path(directory)
            results = [run_case(work, sample, prefix, pinned[sample.label])
                       for sample, prefix in selected]
    print(json.dumps({"schema": "s31-four-case-fixed-root-proof-join-v1",
                      "cases": results,
                      "scope": "four pinned source/proof-byte regressions; no arbitrary PCS opening theorem"},
                     sort_keys=True))


if __name__ == "__main__":
    main()
