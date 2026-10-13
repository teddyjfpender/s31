#!/usr/bin/env python3
"""Pinned exact-source, typed-Program and native fixed-row record admission.

This joins independent Lean static admission with source-owned Gate row
matching, a full fixed-column replay/recommitment, and native proof acceptance
on one private snapshot. The native PCS/FRI and verifier remain assumptions.
No particular private witness is extracted from the accepted proof here.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))
sys.path.insert(0, str(ROOT / "src/frontends/s31/tools/audit"))

from package.context import invoke  # noqa: E402
from package.correspondence import parse_canonical_json  # noqa: E402
from package.lean_effects_admission import _pinned_checker  # noqa: E402
from package.trust import admitted_snapshot  # noqa: E402
from record_source_cells import audit_snapshot  # noqa: E402
from runtime.proof_inputs import proof_inputs_snapshot  # noqa: E402

M31 = 2**31 - 1


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _check_static(checker: Path, snapshot: Path) -> None:
    files = [snapshot / name for name in (
        "source.s31", "typed-structural-derivation.json",
        "source.s31.json", "public-abi.json")]
    if any(path.stat().st_size > (131072 if path.name ==
                                  "typed-structural-derivation.json" else 65536)
           for path in files):
        raise ValueError("record Lean input exceeds byte bound")
    try:
        result = subprocess.run([str(checker), *(str(path) for path in files)],
                                capture_output=True, text=True, timeout=30,
                                check=False)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise ValueError("pinned Lean record checker did not complete") from exc
    if result.returncode or not result.stdout.startswith(
            "accepted: record-v2 source/typed Program correspondence"):
        raise ValueError("pinned Lean record checker rejected: " +
                         (result.stderr + result.stdout).strip()[:512])


def _no_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate public statement key: {key}")
        result[key] = value
    return result


def _invalid_constant(value: str) -> object:
    raise ValueError(f"invalid public statement number: {value}")


def _statement_boundary(statement_bytes: bytes, abi: dict) -> tuple[int, int]:
    """Check public typed paths/words and duplicate-wire claims, not semantics."""
    if len(statement_bytes) > 65536:
        raise ValueError("record public statement exceeds byte bound")
    statement = json.loads(statement_bytes, object_pairs_hook=_no_duplicate_keys,
                           parse_constant=_invalid_constant)
    if (type(statement) is not dict or
            set(statement) != {"version", "abi_sha256", "leaves"} or
            type(statement["version"]) is not int or statement["version"] != 2 or
            statement["abi_sha256"] != abi["boundary_sha256"] or
            type(statement["leaves"]) is not list):
        raise ValueError("record public statement header differs from source ABI")
    boundary = abi["boundary"]
    declared = [leaf for root in boundary["inputs"]
                if root["visibility"] == "public" for leaf in root["leaves"]]
    declared.extend(boundary["result"]["leaves"])
    if len(statement["leaves"]) != len(declared):
        raise ValueError("record public statement leaf count differs from source ABI")
    values: dict[str, int] = {}
    for observed, expected in zip(statement["leaves"], declared, strict=True):
        if (type(observed) is not dict or set(observed) != {"path", "words"} or
                observed["path"] != expected["path"] or
                type(observed["words"]) is not list or
                len(observed["words"]) != 1 or
                type(observed["words"][0]) is not int or
                not 0 <= observed["words"][0] < M31):
            raise ValueError("record public statement leaf differs from source ABI")
        wire, word = expected["wire"], observed["words"][0]
        if wire in values and values[wire] != word:
            raise ValueError("aliased public record leaves disagree")
        values[wire] = word
    return len(declared), len(values)


def certify(package: Path, proof: Path, statement: Path,
            pins: dict[str, str], checker_path: Path,
            checker_sha256: str) -> dict:
    with proof_inputs_snapshot(proof, statement) as (captured_proof, captured_statement):
        with _pinned_checker(checker_path, checker_sha256) as checker:
            with admitted_snapshot(package, pins) as (snapshot, manifest):
                _check_static(checker, snapshot)
                rows = audit_snapshot(snapshot, manifest, pins)
                abi = parse_canonical_json((snapshot / "public-abi.json").read_bytes(),
                                           "public-abi.json")
                key = parse_canonical_json((snapshot / "verification-key.json").read_bytes(),
                                           "verification-key.json")
                relation = parse_canonical_json((snapshot / "source.s31.json").read_bytes(),
                                                "source.s31.json")
                tree = parse_canonical_json(
                    (snapshot / "typed-structural-derivation.json").read_bytes(),
                    "typed-structural-derivation.json")
                if (key.get("public_abi_sha256") != abi.get("boundary_sha256") or
                        key.get("program_sha256") != rows["relation_sha256"] or
                        len(rows["source_cells"]) != len(relation["nodes"])):
                    raise ValueError("record source, ABI, key or source Gate rows differ")
                leaf_count, distinct_words = _statement_boundary(
                    captured_statement.read_bytes(), abi)
                steps = tree["program"]["steps"]
                aliases = sum(step["expr"]["kind"] == "project" for step in steps)
                if len(steps) != aliases + len(relation["nodes"]):
                    raise ValueError("pattern alias emitted an unexpected source Gate node")
                verifier = snapshot / "bin" / f"s31-{manifest['name']}-native-verifier"
                key_path = snapshot / "verification-key.json"
                invoke(str(verifier), "check-key", str(key_path))
                accepted = invoke(str(verifier), str(captured_proof),
                                  str(captured_statement), str(key_path))
                if "native verification accepted" not in accepted:
                    raise ValueError("pinned native verifier did not accept proof")
                return {
                    "schema": "s31-record-v2-multifield-native-row-certificate-v1",
                    "source_sha256": pins["text"],
                    "relation_sha256": rows["relation_sha256"],
                    "structural_tree_sha256": _sha((snapshot / "typed-structural-derivation.json").read_bytes()),
                    "abi_sha256": abi["boundary_sha256"],
                    "key_sha256": pins["key"],
                    "prover_sha256": pins["prover"],
                    "verifier_sha256": pins["verifier"],
                    "checker_sha256": checker_sha256,
                    "proof_sha256": _sha(captured_proof.read_bytes()),
                    "statement_sha256": _sha(captured_statement.read_bytes()),
                    "fixed_root": rows["fixed_root"],
                    "fixed_rows": rows["fixed_rows"],
                    "source_cells": rows["source_cells"],
                    "arithmetic_nodes": len(relation["nodes"]),
                    "zero_row_aliases": aliases,
                    "public_leaves": leaf_count,
                    "distinct_public_wires": distinct_words,
                    "native_verifier_accepted": True,
                    "scope": "source/typed Program/fixed Gate rows and native acceptance; private witness and PCS/FRI binding conditional",
                }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("--statement", type=Path, required=True)
    parser.add_argument("--lean-checker", type=Path, required=True)
    parser.add_argument("--lean-checker-sha256", required=True)
    for kind in ("source", "key", "prover", "verifier", "text"):
        parser.add_argument(f"--{kind}-sha256", required=True)
    args = parser.parse_args()
    pins = {kind: getattr(args, f"{kind}_sha256") for kind in
            ("source", "key", "prover", "verifier", "text")}
    try:
        print(json.dumps(certify(args.package, args.proof, args.statement, pins,
                                 args.lean_checker, args.lean_checker_sha256),
                         indent=2, sort_keys=True))
    except (OSError, ValueError, RuntimeError, KeyError, TypeError,
            json.JSONDecodeError) as exc:
        print(f"record native row certificate rejected: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
