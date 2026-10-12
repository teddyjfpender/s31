#!/usr/bin/env python3
"""Audit one pinned, verified public direct-Gate proof against its full base trace.

This is a deterministic public-trace diagnostic for the independently admitted
four-lane, 1..16-gate release fragment. It does not prove PCS/FRI soundness or
authenticate arbitrary openings beyond the accepted proof and its roots.
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

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from abi.binding_v2 import parse_assignment_json  # noqa: E402
from package.context import invoke, write_json  # noqa: E402
from package.correspondence import read_canonical_json  # noqa: E402
from package.direct_gate_main_correspondence import check_export, source_values  # noqa: E402
from package.fixed_root_join import proof_roots  # noqa: E402
from package.release_admission import bounded_direct_gate_snapshot  # noqa: E402
from runtime.proof_inputs import proof_inputs_snapshot  # noqa: E402

P = (1 << 31) - 1
PHYSICAL_SCHEMAS = {
    "s31-direct-gate-public-functional-physical-v1",
    "s31-direct-gate-square4-physical-v1",
    "s31-direct-gate-early-return-physical-v1",
}


def _public_words(statement: Path, syntax: dict) -> tuple[list[int], list[int]]:
    parsed = parse_assignment_json(statement.read_bytes())
    if (set(parsed) != {"public_inputs", "public_outputs"} or
            type(parsed["public_inputs"]) is not dict or
            type(parsed["public_outputs"]) is not dict or
            set(parsed["public_inputs"]) != {syntax["input"]} or
            set(parsed["public_outputs"]) != {syntax["output_name"]}):
        raise ValueError("public statement differs from the admitted source ABI")
    values = (parsed["public_inputs"][syntax["input"]],
              parsed["public_outputs"][syntax["output_name"]])
    for words in values:
        if (type(words) is not list or len(words) != 4 or
                any(type(word) is not int or not 0 <= word < P for word in words)):
            raise ValueError("public statement has a noncanonical four-lane M31 value")
    return values


def _check_snapshot(package: Path, manifest: dict, certificate: dict,
                    proof: Path, statement: Path) -> dict:
    syntax = certificate["source_ssa"]
    input_words, output_words = _public_words(statement, syntax)
    _, expected_output = source_values(syntax, input_words)
    if list(expected_output) != output_words:
        raise ValueError("public claim differs from independently evaluated source")

    key_path = package / "verification-key.json"
    key = read_canonical_json(key_path)
    topology = read_canonical_json(package / "gate-topology.json")
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    # Only interpret commitment fields after this exact captured proof and
    # statement have been accepted by the pinned generated verifier.
    invoke(str(verifier), str(proof), str(statement), str(key_path))

    with tempfile.TemporaryDirectory(prefix="s31-public-trace-audit-") as directory:
        assignment = Path(directory) / "assignment.json"
        write_json(assignment, {"public_inputs": {syntax["input"]: input_words},
                                "private_inputs": {},
                                "public_outputs": {syntax["output_name"]: output_words}})
        fresh = json.loads(invoke(str(prover), "inspect-topology"))
        physical = json.loads(invoke(str(prover), "inspect-physical-rows", str(assignment)))
        root = json.loads(invoke(str(prover), "inspect-physical-root", str(assignment)))
        if (fresh != topology or
                topology.get("preprocessed_root") != key.get("preprocessed_root") or
                physical.get("schema") not in PHYSICAL_SCHEMAS or
                root.get("schema") != "s31-direct-gate-public-main-root-v1" or
                physical.get("program_sha256") != manifest.get("program_sha256") or
                root.get("program_sha256") != manifest.get("program_sha256") or
                [column.get("values") for column in topology.get("columns", [])] !=
                physical.get("fixed_columns")):
            raise ValueError("native public trace differs from the admitted package")
        reconstructed = check_export(syntax, input_words, physical, root)
        changed = copy.deepcopy(physical)
        changed["main_columns"][8][0] = (changed["main_columns"][8][0] + 1) % P
        try:
            check_export(syntax, input_words, changed, root)
        except ValueError:
            pass
        else:
            raise AssertionError("changed native main cell passed the source-derived trace check")

        denied_assignment = Path(directory) / "private-assignment.json"
        write_json(denied_assignment, {"public_inputs": {syntax["input"]: input_words},
                                       "private_inputs": {"secret": [1]},
                                       "public_outputs": {syntax["output_name"]: output_words}})
        for command in ("inspect-physical-rows", "inspect-physical-root"):
            attempt = subprocess.run((str(prover), command, str(denied_assignment)),
                                     capture_output=True, text=True, timeout=120, check=False)
            report = attempt.stdout + attempt.stderr
            if (attempt.returncode == 0 or
                    "PrivatePhysicalRowsUnavailable" not in attempt.stderr or
                    any(field in report for field in ('"main_columns"', '"fixed_columns"',
                                                      '"main_root"', '"main_columns_sha256"'))):
                raise ValueError("public trace exporter exposed private assignment data")

    proof_bytes = proof.read_bytes()
    fixed_root, main_root, _ = proof_roots(proof_bytes)
    if (fixed_root.hex() != key.get("preprocessed_root") or
            main_root.hex() != root.get("main_root")):
        raise ValueError("accepted proof commitments differ from reconstructed public trace")
    return {"schema": "s31-pinned-public-main-trace-audit-v1",
            "scope": "one accepted public direct-Gate proof; PCS/FRI assumptions remain",
            "source_sha256": certificate["source_sha256"],
            "canonical_ir_sha256": key["canonical_ir_sha256"],
            "fixed_root": fixed_root.hex(),
            "main_root": main_root.hex(),
            "main_cells": reconstructed["source_derived_main_cells"],
            "main_columns_sha256": reconstructed["source_derived_main_columns_sha256"],
            "public_words": reconstructed["source_derived_public_words"],
            "proof_sha256": hashlib.sha256(proof_bytes).hexdigest(),
            "native_verifier_accepted": True,
            "changed_main_cell_rejected": True,
            "private_assignment_diagnostic_rejected": True}


def check(package: Path, proof: Path, statement: Path, pins: dict[str, str]) -> dict:
    """Use private input and package snapshots throughout the pinned audit."""
    with proof_inputs_snapshot(proof, statement) as (captured_proof, captured_statement):
        with bounded_direct_gate_snapshot(package, pins) as (snapshot, manifest, certificate):
            return _check_snapshot(snapshot, manifest, certificate,
                                   captured_proof, captured_statement)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("--statement", type=Path, required=True)
    for kind in ("source", "key", "prover", "verifier", "text"):
        parser.add_argument(f"--{kind}-sha256", required=True)
    args = parser.parse_args()
    pins = {kind: getattr(args, f"{kind}_sha256")
            for kind in ("source", "key", "prover", "verifier", "text")}
    print(json.dumps(check(args.package, args.proof, args.statement, pins),
                     indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
