#!/usr/bin/env python3
"""Publish a checked, path-free record from a fixed-division tune run."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


PROFILE_FIELDS = (
    "build_or_load_seconds",
    "changed_public_statement_rejected_all",
    "independent_value_oracle_statuses",
    "median_native_verify_seconds",
    "median_proof_bytes",
    "median_prove_excluding_pow_seconds",
    "median_wall_prove_seconds",
    "native_verifier_accepted_all",
    "native_verify_seconds_per_assignment",
    "padded",
    "preprocessed_cells",
    "profile",
    "proof_bytes_per_assignment",
    "prove_excluding_pow_seconds_per_assignment",
    "public_abi",
    "raw",
    "visible_fri",
    "wall_prove_seconds_per_assignment",
)


def curate(kind: str, date: str, summary: dict, tune: dict) -> dict:
    if summary["kind"] != kind or summary["schema"] != "s31-fixed-division-benchmark-v1":
        raise ValueError("unexpected benchmark summary")
    if tune["canonical_ir_sha256"] != summary["canonical_ir_sha256"]:
        raise ValueError("summary and tune relation hashes disagree")
    if tune["assignment_sha256"] != summary["assignment_sha256"]:
        raise ValueError("summary and tune witnesses disagree")
    if not tune["same_visible_fri_settings"] or not tune["distinct_assignments"]:
        raise ValueError("profile comparison lacks matched settings or distinct witnesses")
    count = summary["count"]
    if count != 20 or len(tune["assignment_sha256"]) != count:
        raise ValueError("expected exactly 20 recorded witnesses")
    profiles = {}
    for mode in ("direct-gate", "sparse-wide-gate"):
        original = tune["profiles"][mode]
        if not original["native_verifier_accepted_all"] or not original["changed_public_statement_rejected_all"]:
            raise ValueError(f"{mode} failed a native proof control")
        if original["independent_value_oracle_statuses"] != ["passed"] * count:
            raise ValueError(f"{mode} failed an independent value check")
        for field in ("proof_bytes_per_assignment", "prove_excluding_pow_seconds_per_assignment",
                      "native_verify_seconds_per_assignment", "wall_prove_seconds_per_assignment"):
            if len(original[field]) != count:
                raise ValueError(f"{mode} is missing {field} samples")
        profiles[mode] = {key: original[key] for key in PROFILE_FIELDS}
    direct = profiles["direct-gate"]
    wide = profiles["sparse-wide-gate"]
    ratio_fields = {
        "median_proof_bytes": "median_proof_bytes",
        "median_prove_excluding_pow_seconds": "median_prove_excluding_pow_seconds",
        "median_wall_prove_seconds": "median_wall_prove_seconds",
        "preprocessed_cells": "preprocessed_cells",
    }
    return {
        "schema": "s31-direct-wide-division-benchmark-v1",
        "date": date,
        "name": f"{kind}_div_quotient" if kind in ("u128", "i128") else f"{kind}_div_rem",
        "corpus_generator": "src/frontends/s31/benchmarks/benchmark_fixed_division.py",
        "method": "Same source and canonical relation, twenty distinct valid boundary-plus-seeded witnesses, one warmup per profile. Every proof is natively verified, every changed public claim rejected, and every value accepted by the independent oracle.",
        "measurement_limits": "Local host only. Full wall time includes process startup and variable proof-of-work search. Matching visible FRI settings alone do not establish equal soundness across AIRs.",
        "assignment_count": count,
        "assignment_sha256": tune["assignment_sha256"],
        "canonical_ir_sha256": tune["canonical_ir_sha256"],
        "distinct_assignments": tune["distinct_assignments"],
        "host": tune["host"],
        "profiles": profiles,
        "program_sha256": tune["program_sha256"],
        "same_visible_fri_settings": tune["same_visible_fri_settings"],
        "seed": summary["seed"],
        "warmup_assignment_sha256": tune["warmup_assignment_sha256"],
        "wide_over_direct_ratio": {
            name: round(wide[field] / direct[field], 3)
            for name, field in ratio_fields.items()
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("kind")
    parser.add_argument("--date", required=True)
    parser.add_argument("--run", type=Path, required=True,
                        help="directory containing summary.json and tune/tune-report.json")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    summary = json.loads((args.run / "summary.json").read_text())
    tune = json.loads((args.run / "tune/tune-report.json").read_text())
    record = curate(args.kind, args.date, summary, tune)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(record, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
