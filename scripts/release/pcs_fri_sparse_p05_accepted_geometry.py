#!/usr/bin/env python3
"""Inspect an accepted sparse Gate proof's P05 geometry; certify no bits.

The verifier's opt-in `inspect-p05` path runs the ordinary sealed-key and
native-proof verification first. The resulting counts describe required
separate original/own-quotient tracks, not tracks already proven by legacy FRI.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ordered_claim_slices(shape: dict[str, object]):
    claims = shape["claims"]
    expected_offset = 0
    for column in shape["columns"]:
        first = column["first_claim_index"]
        count = column["ood_claims"]
        if (type(first) is not int or type(count) is not int or
                first != expected_offset or count < 0):
            raise ValueError("column claim slices are not contiguous")
        owned = claims[first:first + count]
        if len(owned) != count:
            raise ValueError("column claim slice out of bounds")
        yield column, owned
        expected_offset += count
    if expected_offset != len(claims):
        raise ValueError("column claim slices do not cover all accepted claims")


def report(package: Path, proof: Path, statement: Path) -> dict[str, object]:
    manifest_path = package / "manifest.json"
    key_path = package / "verification-key.json"
    manifest = json.loads(manifest_path.read_text())
    key = json.loads(key_path.read_text())
    if (manifest.get("lowering") != "sparse-gate" or
            key.get("schema") != "s31-verification-key-sparse-roster-v1" or
            key.get("profile") != "sparse-v3"):
        raise ValueError("expected a sealed sparse Gate package")
    for artifact, expected in manifest["artifacts"].items():
        if digest(package / artifact) != expected:
            raise ValueError(f"package artifact digest mismatch: {artifact}")
    name = key["name"]
    verifier = package / "bin" / f"s31-{name}-native-verifier"
    subprocess.run([str(verifier), "check-key", str(key_path)],
                   check=True, capture_output=True, text=True)
    completed = subprocess.run(
        [str(verifier), "inspect-p05", str(proof), str(statement), str(key_path)],
        check=True, capture_output=True, text=True,
    )
    shape = json.loads(completed.stderr.strip())
    if (shape.get("schema") != "s31-sparse-p05-accepted-capture-shape-v1" or
            shape.get("native_to_paper_batch_width_M") is not None or
            shape.get("native_security_bits") is not None):
        raise ValueError("unexpected inspector result")
    if (sum(shape["root_columns"]) != len(shape["columns"]) or
            sum(shape["root_ood_claims"]) != sum(h["ood_claims"] for h in shape["heights"]) or
            any(h["source_columns"] != h["required_original_tracks_if_paired"] or
                h["ood_claims"] != h["required_own_quotient_tracks_if_paired"]
                for h in shape["heights"])):
        raise ValueError("inconsistent accepted-capture counts")
    claims = shape["claims"]
    if sum(shape["root_ood_claims"]) != len(claims):
        raise ValueError("missing accepted OOD coordinates")
    prime = (1 << 31) - 1
    base_point = (shape["oods_point_x_limbs"], shape["oods_point_y_limbs"])
    for field in (*base_point, shape["oods_seed_limbs"]):
        if len(field) != 4 or any(type(word) is not int or not 0 <= word < prime
                                  for word in field):
            raise ValueError("noncanonical OOD seed or base point")
    for column, owned in ordered_claim_slices(shape):
        for sample, claim in enumerate(owned):
            if (claim["root_index"] != column["root_index"] or
                    claim["column_index"] != column["column_index"] or
                    claim["sample_index"] != sample or
                    claim["extended_log_size"] != column["extended_log_size"]):
                raise ValueError("claim order differs from source column roster")
            for field in (claim["point_x_limbs"], claim["point_y_limbs"],
                          claim["value_limbs"]):
                if len(field) != 4 or any(type(word) is not int or
                                          not 0 <= word < prime for word in field):
                    raise ValueError("noncanonical captured OOD coordinate/value")
            if column["root_index"] in (0, 3) and (
                    claim["point_x_limbs"], claim["point_y_limbs"]) != base_point:
                raise ValueError("fixed/composition point differs from base OOD point")
        if len(owned) == 2 and (
                owned[0]["point_x_limbs"], owned[0]["point_y_limbs"]) == (
                owned[1]["point_x_limbs"], owned[1]["point_y_limbs"]):
            raise ValueError("two OOD masks collapsed to the same point")
    if (sum(h["composition_columns"] for h in shape["heights"]) != 8 or
            shape["composition_log_split"] != 1):
        raise ValueError("expected eight split-one composition columns")

    q = (1 << 31) - 1
    t = 1 << 64
    target_denominator = 1 << 96
    n = 1 << key["trace_log_size"]
    blowup = 1 << key["fri"]["log_blowup_factor"]
    candidate_d0 = n * blowup**2
    # Isolated ungrinded batching factor with minimum BCS R=1 and zero
    # certified batch-grinding credit. This is not the full published bound;
    # D0=N*B² and the native-to-paper mapping of M remain premises.
    max_excess = (q**4 * t) // (candidate_d0 * target_denominator * (t + 1))
    return {
        "schema": "s31-p05-sparse-gate-accepted-geometry-v1",
        "status": "accepted_native_proof_experimental_geometry_only",
        "proof_profile": "legacy_postcard_sparse_v3",
        "package_checks": {
            "manifest_artifacts": "verified",
            "native_check_key": "accepted",
            "native_proof": "accepted_before_geometry_inspection",
            "source_sha256": digest(package / "source.s31.json"),
            "manifest_sha256": digest(manifest_path),
            "key_sha256": digest(key_path),
            "roster_artifact_sha256": digest(package / "sparse-component-roster.json"),
            "proof_sha256": digest(proof),
            "statement_sha256": digest(statement),
        },
        "candidate_paper_parameters": {
            "N_from_sealed_max_trace_log": n,
            "B_from_sealed_fri_blowup": blowup,
            "D0_conditionally_N_times_B_squared": candidate_d0,
            "T_hash_queries": t,
            "epsilon_over_T_target_bits": 96,
            "minimum_BCS_rounds_R": 1,
            "certified_batch_grinding_credit": 0,
            "largest_integer_M_passing_isolated_batch_factor": max_excess + 1,
        },
        "accepted_capture": shape,
        "accepted_ood_claim_map_sha256": hashlib.sha256(
            json.dumps(claims, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest(),
        "native_to_paper_batch_width_M": None,
        "native_proven_security_bits": None,
        "proven_release_admissible": False,
        "missing": [
            "a selected four-epoch original-plus-own-quotient whole-oracle protocol",
            "theorem mapping of native domain batches to padded M and D0",
            "full list/AIR/FRI/BCS/collision/PoW error composition",
            "a selected line-tree commitment and descriptor binding profile",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("proof", type=Path)
    parser.add_argument("statement", type=Path)
    parser.add_argument("--require-proven", action="store_true")
    args = parser.parse_args()
    result = report(args.package, args.proof, args.statement)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 2 if args.require_proven else 0


if __name__ == "__main__":
    raise SystemExit(main())
