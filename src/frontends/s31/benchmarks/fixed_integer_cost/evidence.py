"""Check and account for interleaved native fixed-integer benchmark evidence.

The report is an observed whole-process cost decomposition, not an unseen-
program predictor. Native acceptance is checked against saved trial controls;
this offline gate does not rerun a verifier.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import statistics
import sys
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from runtime.cost_model import observed_cost_model


LOWERINGS = {"direct-gate": "direct-m31-v4", "sparse-wide-gate": "sparse-wide-v5"}
TOLERANCE = 0.000005  # Native timers print six decimal places.


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def load(path: Path) -> dict:
    value = json.loads(path.read_text())
    require(isinstance(value, dict), f"{path}: expected object")
    return value


def host_identity() -> dict:
    node = platform.node()
    require(bool(node), "host name unavailable")
    return {"host_id_sha256": hashlib.sha256(node.encode()).hexdigest(),
            "platform": platform.platform(), "machine": platform.machine(),
            "python": platform.python_version(),
            "zig": s31.invoke("zig", "version").strip()}


def finite_nonnegative(value: object) -> bool:
    return type(value) in (int, float) and math.isfinite(value) and value >= 0


def median(values: list[float]) -> float:
    return statistics.median(values)


def stage_parts(trial: dict, label: str) -> dict:
    stages = trial.get("prover_stages")
    require(isinstance(stages, dict), f"{label}: missing native stage timers")
    names = ("witness_seconds", "setup_seconds", "prove_seconds",
             "interaction_pow_seconds", "fri_pow_seconds",
             "prove_excluding_pow_seconds", "total_through_verification_seconds",
             "runtime_other_seconds")
    require(all(finite_nonnegative(stages.get(name)) for name in names),
            f"{label}: invalid or incomplete native stage timers")
    require(all(finite_nonnegative(trial.get(name)) for name in
                ("prove_seconds", "verify_seconds")),
            f"{label}: invalid process wall time")
    internal_prove = (stages["prove_excluding_pow_seconds"] +
                      stages["interaction_pow_seconds"] + stages["fri_pow_seconds"])
    internal_total = (stages["witness_seconds"] + stages["setup_seconds"] +
                      stages["prove_seconds"] + stages["runtime_other_seconds"])
    require(abs(stages["prove_seconds"] - internal_prove) <= TOLERANCE,
            f"{label}: PoW/non-PoW accounting differs from native prove timer")
    require(abs(stages["total_through_verification_seconds"] - internal_total) <=
            TOLERANCE, f"{label}: native runtime-stage accounting differs")
    residual = trial["prove_seconds"] - stages["total_through_verification_seconds"]
    require(residual >= -0.003,
            f"{label}: runtime total exceeds measured prover process wall")
    # Keep the signed residual: clamping would conceal a timer disagreement.
    return {"witness": stages["witness_seconds"], "setup": stages["setup_seconds"],
            "prove_non_pow": stages["prove_excluding_pow_seconds"],
            "interaction_pow": stages["interaction_pow_seconds"],
            "fri_pow": stages["fri_pow_seconds"],
            "runtime_other": stages["runtime_other_seconds"],
            "process_residual": residual,
            "native_verify_process": trial["verify_seconds"],
            "whole_process": trial["prove_seconds"] + trial["verify_seconds"]}


def analyze(output: Path) -> dict:
    output = output.resolve()
    summary = load(output / "summary.json")
    tune = load(output / "tune" / "tune-report.json")
    kind, count = summary.get("kind"), summary.get("count")
    require(summary.get("schema") in ("s31-fixed-addition-paired-v2",
                                       "s31-fixed-multiplication-paired-v2"),
            "unsupported fixed-integer paired report")
    operation = "add" if summary["schema"] == "s31-fixed-addition-paired-v2" else "mul"
    require(kind in {f"{sign}{width}" for sign in ("u", "i")
                     for width in (8, 16, 32, 64, 128)} and
            type(count) is int and 5 <= count <= 256,
            "invalid fixed-integer kind or witness count")
    require(tune.get("schema") == "s31-tune-v1", "invalid raw tune report")
    require(summary.get("compiler_sha256") == s31.compiler_fingerprint(),
            "stale compiler fingerprint")
    host = host_identity()
    require(summary.get("host") == host and
            tune.get("host") == {k: v for k, v in host.items() if k != "host_id_sha256"},
            "host or toolchain differs from paired evidence")
    source = output / f"{kind}_checked_{operation}.s31"
    expected_source = (f"use std@1;\ncircuit {kind}_checked_{operation}(private a: {kind}, "
                       f"private b: {kind}) -> public {kind} "
                       f"{{ std::int::{operation}_checked(a, b) }}\n")
    require(source.read_text() == expected_source and
            summary.get("source_sha256") == s31.file_hash(source) and
            Path(tune.get("source", "")).resolve() == source,
            "source or source identity differs from paired evidence")
    for name in ("program_sha256", "canonical_ir_sha256", "assignment_sha256",
                 "same_visible_fri_settings"):
        require(summary.get(name) == tune.get(name),
                f"{name} differs between paired and raw evidence")
    require(tune["same_visible_fri_settings"] is True and
            tune.get("distinct_assignments") is True and
            tune.get("distinct_assignment_count") == count and
            tune.get("warmup_assignment_sha256") == tune["assignment_sha256"][0],
            "assignment or visible FRI controls failed")
    assignments = [output / "assignments" / f"{index:03d}.json"
                   for index in range(count)]
    require(set((output / "assignments").glob("*.json")) == set(assignments) and
            [s31.assignment_digest(path) for path in assignments] ==
            tune["assignment_sha256"] and
            len(set(tune["assignment_sha256"])) == count,
            "assignment files or digests differ from raw evidence")
    expected_schedule = [
        {"assignment_index": index, "lowering": lowering}
        for index in range(count)
        for lowering in (("direct-gate", "sparse-wide-gate") if index % 2 == 0
                         else ("sparse-wide-gate", "direct-gate"))]
    require(tune.get("measurement_order") == "alternating-by-assignment-v1" and
            tune.get("trial_schedule") == expected_schedule,
            "paired trial schedule is missing or not balanced")
    require(tune.get("independent_value_oracle_provenance") == s31.oracle_provenance(),
            "independent oracle provenance differs from current source")
    profiles = tune.get("profiles")
    require(isinstance(profiles, dict) and set(profiles) == set(LOWERINGS) and
            isinstance(summary.get("profiles"), dict) and
            set(summary["profiles"]) == set(LOWERINGS),
            "paired profiles differ from requested lowerings")
    result = {}
    all_parts = {}
    for lowering, profile_name in LOWERINGS.items():
        profile = profiles[lowering]
        reported = summary["profiles"][lowering]
        require(profile.get("profile") == profile_name and
                reported.get("profile") == profile_name and
                profile.get("visible_fri") == reported.get("visible_fri") and
                profile.get("native_verifier_accepted_all") is True and
                profile.get("changed_public_statement_rejected_all") is True and
                profile.get("independent_value_oracle_statuses") == ["passed"] * count,
                f"{lowering}: profile or proof controls failed")
        package = output / "tune" / "packages" / lowering
        manifest = load(package / "manifest.json")
        for name, value in (("compiler_sha256", summary["compiler_sha256"]),
                            ("source_text_sha256", summary["source_sha256"]),
                            ("program_sha256", summary["program_sha256"]),
                            ("canonical_ir_sha256", summary["canonical_ir_sha256"]),
                            ("lowering", lowering)):
            require(manifest.get(name) == value,
                    f"{lowering}: manifest {name} differs from paired evidence")
        run_root = output / "tune" / "runs" / lowering
        require(set(path.name for path in run_root.iterdir() if path.is_dir()) ==
                {f"{index:03d}" for index in range(count)},
                f"{lowering}: native trial directory set differs")
        trials = []
        parts = []
        for index, assignment in enumerate(assignments):
            trial_dir = run_root / f"{index:03d}"
            trial = load(trial_dir / "trial-report.json")
            label = f"{lowering} trial {index}"
            proof = trial_dir / "proof.bin"
            require(trial.get("schema") == "s31-trial-v1" and
                    Path(trial.get("assignment", "")).resolve() == assignment and
                    Path(trial.get("package", "")).resolve() == package and
                    trial.get("lowering") == lowering and
                    trial.get("profile") == profile_name and
                    trial.get("visible_fri") == profile["visible_fri"] and
                    trial.get("program_sha256") == summary["program_sha256"] and
                    trial.get("canonical_ir_sha256") == summary["canonical_ir_sha256"] and
                    trial.get("raw") == profile["raw"] and
                    trial.get("padded") == profile["padded"] and
                    trial.get("preprocessed_cells") == profile["preprocessed_cells"],
                    f"{label}: native trial identity differs")
            require(trial.get("proof_bytes") == proof.stat().st_size and
                    trial.get("proof_sha256") == s31.file_hash(proof) and
                    trial.get("native_verifier_accepted") is True and
                    bool(trial.get("changed_public_statement_rejected")) and
                    trial.get("independent_value_oracle", {}).get("status") == "passed" and
                    trial.get("independent_value_oracle_provenance") ==
                    tune["independent_value_oracle_provenance"],
                    f"{label}: proof, verifier, or oracle evidence differs")
            claim = load(assignment)
            statement = load(trial_dir / "statement.json")
            changed = load(trial_dir / "changed-statement.json")
            require(statement == {"public_inputs": claim["public_inputs"],
                                  "public_outputs": claim["public_outputs"]} and
                    changed != statement and
                    trial["independent_value_oracle"].get("computed_public_outputs") ==
                    claim["public_outputs"],
                    f"{label}: public statement or oracle value differs")
            part = stage_parts(trial, label)
            require(trial.get("observed_cost_model") == observed_cost_model([trial]),
                    f"{label}: per-trial cost summary differs")
            trials.append(trial)
            parts.append(part)
        require(profile.get("observed_cost_model") == observed_cost_model(trials) and
                profile.get("proof_bytes_per_assignment") ==
                [trial["proof_bytes"] for trial in trials] and
                profile.get("wall_prove_seconds_per_assignment") ==
                [trial["prove_seconds"] for trial in trials] and
                profile.get("native_verify_seconds_per_assignment") ==
                [trial["verify_seconds"] for trial in trials] and
                profile.get("prove_excluding_pow_seconds_per_assignment") ==
                [trial["prover_stages"]["prove_excluding_pow_seconds"]
                 for trial in trials],
                f"{lowering}: raw tune metrics differ from trials")
        require(profile.get("median_proof_bytes") == median(
                    [trial["proof_bytes"] for trial in trials]) and
                profile.get("median_wall_prove_seconds") == median(
                    [trial["prove_seconds"] for trial in trials]) and
                profile.get("median_native_verify_seconds") == median(
                    [trial["verify_seconds"] for trial in trials]) and
                profile.get("median_prove_excluding_pow_seconds") == median(
                    [trial["prover_stages"]["prove_excluding_pow_seconds"]
                     for trial in trials]),
                f"{lowering}: raw tune median differs from trials")
        for name in ("profile", "visible_fri", "raw", "padded", "preprocessed_cells",
                     "proof_bytes_per_assignment", "median_proof_bytes",
                     "wall_prove_seconds_per_assignment", "median_wall_prove_seconds",
                     "median_prove_excluding_pow_seconds", "median_native_verify_seconds",
                     "native_verifier_accepted_all", "changed_public_statement_rejected_all",
                     "independent_value_oracle_statuses"):
            require(reported.get(name) == profile.get(name),
                    f"{lowering}: summary {name} differs from raw tune")
        if operation == "mul":
            require(reported.get("native_overflow_rejected") is True and
                    summary.get("checked_overflow_oracle_rejected") is True,
                    f"{lowering}: missing checked-overflow control")
        all_parts[lowering] = parts
        result[lowering] = {
            "raw": profile["raw"], "padded": profile["padded"],
            "preprocessed_cells": profile["preprocessed_cells"],
            "median_proof_bytes": median([trial["proof_bytes"] for trial in trials]),
            "median_whole_process_seconds": median([part["whole_process"]
                                                     for part in parts]),
            "median_stage_seconds": {name: median([part[name] for part in parts])
                                     for name in parts[0] if name != "whole_process"},
            "max_absolute_accounting_residual_seconds": max(abs(
                part["whole_process"] - sum(part[name] for name in part
                                            if name != "whole_process"))
                for part in parts),
        }
    require(profiles["direct-gate"]["visible_fri"] ==
            profiles["sparse-wide-gate"]["visible_fri"],
            "visible FRI settings differ")
    direct = all_parts["direct-gate"]
    sparse = all_parts["sparse-wide-gate"]
    return {
        "schema": "s31-fixed-integer-whole-process-evidence-v1",
        "status": "current-host-compiler-and-artifacts-consistent",
        "operation": operation, "kind": kind, "count": count,
        "compiler_sha256": summary["compiler_sha256"],
        "host_id_sha256": host["host_id_sha256"],
        "measurement_order": "alternating-by-assignment-v1",
        "profiles": result,
        "median_paired_whole_process_difference_seconds": median([
            direct[i]["whole_process"] - sparse[i]["whole_process"]
            for i in range(count)]),
        "median_paired_direct_over_sparse_whole_process_ratio": median([
            direct[i]["whole_process"] / sparse[i]["whole_process"]
            for i in range(count)]),
        "limitations": ("One host, one source, distinct witnesses and cold native setup. "
                        "Per-assignment stage sums reconcile process wall; medians need not sum. "
                        "Proof-of-work and host load vary. Saved native controls are checked "
                        "against artifacts but native verification is not replayed here. "
                        "This is observed cost evidence, not unseen-program prediction or "
                        "soundness equivalence between AIR profiles."),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("measurement_dir", type=Path)
    args = parser.parse_args()
    print(json.dumps(analyze(args.measurement_dir), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
