#!/usr/bin/env python3
"""Single-run orthogonal geometry stress transfer of the frozen V8 model."""

from __future__ import annotations

import argparse
import json
import os
import statistics
import sys
from pathlib import Path

import protocol as p
sys.path.insert(0, str(p.S31 / "tests/acceptance/mixed_boundary"))
from registry_manifest_digest import digest as registry_manifest_digest

v2, v3 = p.v2, p.v3
ROOT, S31 = p.ROOT, p.S31
RESULT = p.LANGUAGE / "mixed-cost-v9-geometry-transfer-result.json"
SCORE = p.LANGUAGE / "mixed-cost-v9-geometry-transfer-score.json"
TRIALS = ((0, 0), (0, 1), *((index, 0) for index in range(1, p.CLAIMS + 1)))


def check_manifest(manifest: dict, expected: dict) -> None:
    count = expected["call_count"]
    pcs = manifest.get("pcs", {})
    fri = pcs.get("fri_config", {}) if isinstance(pcs, dict) else {}
    slots = manifest.get("slots")
    trees = manifest.get("tree_columns")
    geometry = expected["expected_geometry"]
    calls = manifest.get("calls")
    if (manifest.get("schema") != "s31-mixed-component-inspection-general-v3" or
            manifest.get("source_sha256") != expected["source_sha256"] or
            manifest.get("call_count") != count or
            manifest.get("slot_count") != geometry["slots"] or
            manifest.get("interaction_pow_bits") != 20 or
            fri.get("pow_bits") != 26 or
            type(slots) is not list or len(slots) != geometry["slots"] or
            trees != geometry["tree_columns"] or
            manifest.get("total_constraints") != geometry["constraints"] or
            manifest.get("max_column_log_size") != geometry["max_column_log_size"] or
            manifest.get("composition_log_size") != geometry["composition_log_size"] or
            [slot.get("trace_log_size") for slot in slots] !=
                geometry["slot_trace_logs"] or
            type(calls) is not list or len(calls) != 1 or
            calls[0].get("rounds") != expected["chip_rounds"] or
            sum(slot["n_constraints"] for slot in slots) != manifest.get("total_constraints") or
            manifest.get("main_columns") != trees[1] or
            manifest.get("interaction_columns") != trees[2] or
            manifest.get("registry_manifest_sha256") != registry_manifest_digest(manifest)):
        raise ValueError("native source identity, component geometry or PoW differs")


def bins(directory: Path, name: str) -> dict[str, Path]:
    base = f"s31-mixed_cost_v9_geometry_transfer_{name}-mixed-general-"
    binary = directory / "package/bin"
    return {role: binary / (base + suffix) for role, suffix in (
        ("prover", "prover"), ("verifier", "native-verifier"),
        ("manifest", "manifest"))}


def score_record(record: dict, expected: dict, gates: dict) -> dict:
    trials = record["trials"]
    scored = [row for row in trials if row["claim_index"] > 0]
    if len(scored) != p.CLAIMS:
        raise ValueError("wrong scored count")
    prediction = expected["prediction"]
    wall = [row["first_verified_process_wall_ns"] for row in scored]
    proof = [row["proof_bytes"] for row in scored]
    wall_median = statistics.median(wall)
    proof_median = statistics.median(proof)
    center_wall = prediction["warm_wall_quantile_ns"]["0.5"]
    center_proof = prediction["proof_bytes_center"]
    wall_band = [prediction["warm_wall_quantile_ns"][key] for key in ("0.05", "0.95")]
    proof_band = prediction["proof_bytes_interval"]
    metrics = {
        "scored_trials": len(scored),
        "observed_warm_wall_median_ns": wall_median,
        "predicted_warm_wall_median_ns": center_wall,
        "wall_median_relative_error": abs(wall_median - center_wall) / wall_median,
        "wall_interval_coverage": sum(wall_band[0] <= x <= wall_band[1] for x in wall) / len(wall),
        "observed_proof_median_bytes": proof_median,
        "predicted_proof_center_bytes": center_proof,
        "proof_median_relative_error": abs(proof_median - center_proof) / proof_median,
        "proof_interval_coverage": sum(proof_band[0] <= x <= proof_band[1] for x in proof) / len(proof),
        "first_post_build_verified_wall_ns": trials[0]["first_verified_process_wall_ns"],
        "same_claim_immediate_repeat_wall_ns": trials[1]["first_verified_process_wall_ns"],
        "build_wall_ns": record["build_wall_ns"],
        "fri_pow_median_ns": statistics.median(row["native_phases_ns"]["fri_pow_ns"] for row in scored),
        "interaction_pow_median_ns": statistics.median(
            row["native_phases_ns"]["interaction_pow_ns"] for row in scored),
    }
    checks = {
        "wall_median_error": metrics["wall_median_relative_error"] <=
            gates["wall_median_relative_error_per_source_max"],
        "wall_interval_coverage": metrics["wall_interval_coverage"] >=
            gates["wall_90_interval_coverage_per_source_min"],
        "proof_median_error": metrics["proof_median_relative_error"] <=
            gates["proof_median_relative_error_per_source_max"],
        "proof_interval_coverage": metrics["proof_interval_coverage"] >=
            gates["proof_90_interval_coverage_per_source_min"],
    }
    return {**metrics, "gates": checks, "all_gates_pass": all(checks.values())}


def run(out: Path) -> dict:
    protocol, protocol_sha = p.frozen()
    if RESULT.exists() or SCORE.exists() or out.exists():
        raise ValueError("one prospective run only: output already exists")
    out.mkdir(parents=True)
    env = os.environ.copy()
    env.pop("STWO_ZIG_POW_WORKERS", None)
    env["S31_MIXED_NATIVE_PHASES"] = "1"
    records = []
    for name, expected in protocol["source_roster"].items():
        directory = out / name
        directory.mkdir()
        raw_source = p.source(name)
        source_path = directory / "source.s31.json"
        source_path.write_bytes(raw_source)
        built, build_wall = v2.process([
            "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=2",
            "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
            f"-Ds31-name=mixed_cost_v9_geometry_transfer_{name}", "-j1", "--prefix",
            str(directory / "package")])
        (directory / "build.stdout").write_bytes(built.stdout)
        (directory / "build.stderr").write_bytes(built.stderr)
        if built.returncode:
            raise RuntimeError(f"{name} native package build failed; preserve run as failure")
        binaries = bins(directory, name)
        binary_hashes = {role: p.sha(path.read_bytes()) for role, path in binaries.items()}
        inspected, _ = v2.process([str(binaries["manifest"])])
        (directory / "manifest.stdout").write_bytes(inspected.stdout)
        (directory / "manifest.stderr").write_bytes(inspected.stderr)
        if inspected.returncode:
            raise RuntimeError("native manifest executable failed")
        manifest = v2.parse(inspected.stdout)
        check_manifest(manifest, expected)
        trials = []
        for ordinal, (index, repeat) in enumerate(TRIALS):
            _, assignment, statement = p.case(name, index)
            prefix = f"a{index:02d}r{repeat}"
            assignment_path = directory / f"{prefix}.assignment.json"
            statement_path = directory / f"{prefix}.statement.json"
            changed_path = directory / f"{prefix}.changed.json"
            proof_path = directory / f"{prefix}.proof"
            emitted_path = directory / f"{prefix}.emitted.json"
            assignment_path.write_bytes(assignment)
            statement_path.write_bytes(statement)
            changed_path.write_bytes(v2.changed_result(raw_source, statement))
            if {role: p.sha(path.read_bytes()) for role, path in binaries.items()} != binary_hashes:
                raise ValueError("package binary changed during timing")
            proved, prove_wall = v3.timed([
                str(binaries["prover"]), str(assignment_path), str(proof_path),
                str(emitted_path), str(statement_path)], env)
            (directory / f"{prefix}.prove.stderr").write_bytes(proved.stderr)
            if (proved.returncode or not proof_path.exists() or
                    not emitted_path.exists() or emitted_path.read_bytes() != statement):
                raise RuntimeError(f"{name}/{prefix} prover or statement failed")
            verified, verify_wall = v3.timed([
                str(binaries["verifier"]), str(proof_path), str(statement_path)], env)
            changed, _ = v2.process([
                str(binaries["verifier"]), str(proof_path), str(changed_path)], env)
            (directory / f"{prefix}.verified.stderr").write_bytes(verified.stderr)
            (directory / f"{prefix}.changed.stderr").write_bytes(changed.stderr)
            if (verified.returncode or b"verified" not in verified.stderr or
                    not v2.proof_layer_rejection(changed)):
                raise RuntimeError(f"{name}/{prefix} native verifier controls failed")
            stage = v2.tagged(proved.stderr, b"S31_MIXED_STAGE_V1")
            phase = v2.tagged(proved.stderr, b"S31_MIXED_NATIVE_PHASE_V1")
            if (stage["source_sha256"] != expected["source_sha256"] or
                    stage["proof_bytes"] != proof_path.stat().st_size):
                raise ValueError("source/proof differs from native stage report")
            trials.append({"ordinal": ordinal, "claim_index": index, "repeat": repeat,
                           "assignment_sha256": p.sha(assignment),
                           "statement_sha256": p.sha(statement),
                           "proof_sha256": p.sha(proof_path.read_bytes()),
                           "proof_bytes": proof_path.stat().st_size,
                           "prover_process_monotonic_ns": prove_wall,
                           "external_verifier_process_monotonic_ns": verify_wall,
                           "first_verified_process_wall_ns":
                               prove_wall["duration"] + verify_wall["duration"],
                           "package_stages_ns": stage["stages_ns"],
                           "native_phases_ns": phase,
                           "changed_result_rejected_at_interaction_nonce": True})
        records.append({"name": name, "call_count": expected["call_count"],
                        "source_sha256": expected["source_sha256"],
                        "binary_sha256": binary_hashes,
                        "manifest_sha256": p.sha(inspected.stdout),
                        "native_manifest": manifest,
                        "build_wall_ns": build_wall, "trials": trials})
    p.frozen()
    corpus = {"schema": "s31-mixed-cost-v9-geometry-transfer-result",
              "protocol_sha256": protocol_sha,
              "v8_model_sha256": protocol["v8_model_sha256"],
              "host": protocol["host"], "records": records,
              "verified_proofs": len(records) * len(TRIALS),
              "changed_claim_proof_rejections": len(records) * len(TRIALS)}
    raw = p.canonical(corpus)
    (out / "result.json").write_bytes(raw)
    RESULT.write_bytes(raw)
    scores = {record["name"]: score_record(
        record, protocol["source_roster"][record["name"]], protocol["gates"])
        for record in records}
    score = {"schema": "s31-mixed-cost-v9-geometry-transfer-score",
             "protocol_sha256": protocol_sha, "result_sha256": p.sha(raw),
             "sources": scores, "all_gates_pass": all(row["all_gates_pass"] for row in scores.values())}
    SCORE.write_bytes(p.canonical(score))
    return score


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("run",))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.out), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
