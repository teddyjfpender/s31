#!/usr/bin/env python3
"""One prospective native falsification of V18 mixed-operator transfer."""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import protocol as p
sys.path.insert(0, str(p.S31 / "tests/acceptance/mixed_boundary"))
from registry_manifest_digest import digest as registry_manifest_digest

v2, v3 = p.v2, p.v3
ROOT, S31 = p.ROOT, p.S31
RESULT = p.LANGUAGE / "mixed-cost-v18-topology-transfer-result.json"
SCORE = p.LANGUAGE / "mixed-cost-v18-topology-transfer-score.json"
ATTEMPT = p.LANGUAGE / "mixed-cost-v18-topology-transfer-attempt.jsonl"


def check_calls(calls: list[dict], expected: list[dict]) -> None:
    if type(calls) is not list or len(calls) != len(expected):
        raise ValueError("native call count differs from frozen source")
    previous_output = None
    used_addresses: set[int] = set()
    for call, source_call in zip(calls, expected, strict=True):
        if (type(call) is not dict or
                {key: call.get(key) for key in source_call} != source_call):
            raise ValueError("native call identity, feeder, rounds or constant differs")
        inputs, outputs = call.get("input"), call.get("output")
        for addresses in (inputs, outputs):
            if (type(addresses) is not list or len(addresses) != 4 or
                    any(type(address) is not int or address < 0 for address in addresses) or
                    len(set(addresses)) != 4):
                raise ValueError("native call lane addresses are malformed")
        if previous_output is not None and inputs != previous_output:
            raise ValueError("sequential native call address chain differs")
        if any(address in used_addresses for address in outputs):
            raise ValueError("native call output address is not fresh")
        used_addresses.update(inputs)
        used_addresses.update(outputs)
        previous_output = outputs


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
            [slot.get("n_constraints") for slot in slots] !=
                geometry["slot_constraints"] or
            [{key: slot.get(key) for key in frozen_slot}
             for slot, frozen_slot in zip(slots, geometry["slot_layout"], strict=True)] !=
                geometry["slot_layout"] or
            type(calls) is not list or len(calls) != count or
            sum(slot["n_constraints"] for slot in slots) != manifest.get("total_constraints") or
            manifest.get("main_columns") != trees[1] or
            manifest.get("interaction_columns") != trees[2] or
            manifest.get("registry_manifest_sha256") != registry_manifest_digest(manifest)):
        raise ValueError("native source identity, component geometry or PoW differs")
    check_calls(calls, expected["expected_calls"])


def bins(directory: Path, name: str) -> dict[str, Path]:
    base = f"s31-mixed_cost_v18_topology_transfer_{name}-mixed-general-"
    binary = directory / "package/bin"
    return {role: binary / (base + suffix) for role, suffix in (
        ("prover", "prover"), ("verifier", "native-verifier"),
        ("manifest", "manifest"))}


def timed_rss(command: list[str], env: dict[str, str]) -> tuple[subprocess.CompletedProcess[bytes], dict]:
    """Fresh process wall and OS peak RSS; explicit unavailable marker."""
    method = "unavailable"
    with tempfile.TemporaryDirectory(prefix="s31-v18-rss-") as temporary:
        resource = Path(temporary) / "resource.txt"
        measured = command
        if Path("/usr/bin/time").is_file() and platform.system() == "Darwin":
            measured = ["/usr/bin/time", "-l", "-o", str(resource), *command]
            method = "darwin-time-max-rss-bytes"
        elif Path("/usr/bin/time").is_file() and platform.system() == "Linux":
            measured = ["/usr/bin/time", "-f", "%M", "-o", str(resource), *command]
            method = "gnu-time-max-rss-kib"
        start = time.perf_counter_ns()
        result = subprocess.run(measured, cwd=ROOT, capture_output=True, env=env,
                                timeout=120, check=False)
        end = time.perf_counter_ns()
        peak = None
        if resource.is_file():
            raw = resource.read_text()
            if method == "darwin-time-max-rss-bytes":
                match = re.search(r"^\s*(\d+)\s+maximum resident set size\s*$", raw, re.M)
                if match:
                    peak = int(match.group(1))
            elif method == "gnu-time-max-rss-kib" and raw.strip().isdigit():
                peak = int(raw.strip()) * 1024
        if peak is None:
            raise RuntimeError("OS peak RSS unavailable; V18 protocol requires it")
        return result, {"start": start, "end": end, "duration": end - start,
                        "peak_rss_bytes": peak,
                        "peak_rss_method": method if peak is not None else "unavailable"}


def score_record(record: dict, expected: dict, gates: dict) -> dict:
    trials = record["trials"]
    scored = [row for row in trials if row["claim_index"] > 0]
    if len(scored) != p.CLAIMS:
        raise ValueError("wrong scored count")
    residuals = [row["first_verified_process_wall_ns"] -
                 row["native_phases_ns"]["fri_pow_ns"] -
                 row["native_phases_ns"]["interaction_pow_ns"] for row in scored]
    if any(value <= 0 for value in residuals):
        raise ValueError("reported PoW must be less than measured verified process wall")
    prediction = expected["prediction"]
    wall = [row["first_verified_process_wall_ns"] for row in scored]
    proof = [row["proof_bytes"] for row in scored]
    wall_median = statistics.median(wall)
    proof_median = statistics.median(proof)
    center_wall = prediction["warm_wall_one_draw_quantile_ns"]["0.5"]
    center_proof = prediction["proof_bytes_center"]
    wall_band = [prediction["warm_wall_one_draw_quantile_ns"][key] for key in ("0.05", "0.95")]
    sample_band = [prediction["warm_wall_sample20_median_quantile_ns"][key]
                   for key in ("0.05", "0.95")]
    proof_band = prediction["proof_bytes_interval"]
    prover_rss = statistics.median(row["prover_process_monotonic_ns"]["peak_rss_bytes"]
                                   for row in scored)
    verifier_rss = statistics.median(row["external_verifier_process_monotonic_ns"]["peak_rss_bytes"]
                                     for row in scored)
    prover_rss_prediction = prediction["prover_peak_rss_median_bytes"]
    verifier_rss_prediction = prediction["verifier_peak_rss_median_bytes"]
    wall_hits = sum(wall_band[0] <= x <= wall_band[1] for x in wall)
    metrics = {
        "scored_trials": len(scored),
        "observed_warm_wall_median_ns": wall_median,
        "predicted_warm_wall_median_ns": center_wall,
        "wall_median_relative_error": abs(wall_median - center_wall) / wall_median,
        "wall_one_draw_interval_hits": wall_hits,
        "wall_one_draw_interval_coverage": wall_hits / len(wall),
        "wall_sample20_median_in_band": sample_band[0] <= wall_median <= sample_band[1],
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
        "prover_peak_rss_median_bytes": prover_rss,
        "external_verifier_peak_rss_median_bytes": verifier_rss,
        "prover_rss_median_relative_error": abs(prover_rss - prover_rss_prediction) / prover_rss,
        "verifier_rss_median_relative_error": abs(verifier_rss - verifier_rss_prediction) / verifier_rss,
        "verified_wall_minus_reported_pow_median_ns": statistics.median(residuals),
        "observed_native_package_phase_medians_ns": {
            key: statistics.median(row["package_stages_ns"][key] for row in scored)
            for key in p.cost_model.PHASES
        },
    }
    metrics["nonpow_wall_median_relative_error"] = abs(
        metrics["verified_wall_minus_reported_pow_median_ns"] -
        prediction["nonpow_whole_process_center_ns"]) / metrics[
            "verified_wall_minus_reported_pow_median_ns"]
    metrics["native_package_phase_relative_errors"] = {
        key: abs(observed - prediction["native_package_phase_center_ns"][key]) / observed
        for key, observed in metrics["observed_native_package_phase_medians_ns"].items()
    }
    checks = {
        "wall_median_error": metrics["wall_median_relative_error"] <=
            gates["wall_median_relative_error_per_source_max"],
        "wall_one_draw_interval_coverage": metrics["wall_one_draw_interval_coverage"] >=
            gates["wall_one_draw_90_coverage_per_source_min"],
        "proof_median_error": metrics["proof_median_relative_error"] <=
            gates["proof_median_relative_error_per_source_max"],
        "proof_interval_coverage": metrics["proof_interval_coverage"] >=
            gates["proof_90_interval_coverage_per_source_min"],
        "prover_rss_median_error": metrics["prover_rss_median_relative_error"] <=
            gates["prover_rss_median_relative_error_per_source_max"],
        "verifier_rss_median_error": metrics["verifier_rss_median_relative_error"] <=
            gates["verifier_rss_median_relative_error_per_source_max"],
        "nonpow_wall_median_error": metrics["nonpow_wall_median_relative_error"] <=
            gates["nonpow_wall_median_relative_error_per_source_max"],
    }
    checks.update({f"native_phase_{key}_median_error": error <=
                   gates["native_phase_median_relative_error_per_source_max"]
                   for key, error in metrics["native_package_phase_relative_errors"].items()})
    return {**metrics, "gates": checks, "all_gates_pass": all(checks.values())}


def start_attempt(out: Path, protocol_sha: str) -> None:
    """Atomic fixed marker; even an empty interrupted file blocks a retry."""
    fd = os.open(ATTEMPT, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o644)
    with os.fdopen(fd, "wb") as marker:
        marker.write(p.canonical({"schema": "s31-mixed-cost-v18-attempt-v1",
                                  "event": "started", "protocol_sha256": protocol_sha,
                                  "output_dir": str(out.resolve()), "time_ns": time.time_ns()}))
        marker.flush()
        os.fsync(marker.fileno())
    directory_fd = os.open(ATTEMPT.parent, os.O_RDONLY)
    try:
        os.fsync(directory_fd)
    finally:
        os.close(directory_fd)


def finish_attempt(event: dict) -> None:
    with ATTEMPT.open("ab") as marker:
        marker.write(p.canonical({**event, "time_ns": time.time_ns()}))
        marker.flush()
        os.fsync(marker.fileno())


def run(out: Path) -> dict:
    protocol, protocol_sha = p.frozen()
    if RESULT.exists() or SCORE.exists() or out.exists():
        raise ValueError("one prospective run only: output already exists")
    start_attempt(out, protocol_sha)
    try:
        score = run_after_attempt(out, protocol, protocol_sha)
    except BaseException as exc:
        finish_attempt({"event": "failed", "error_type": type(exc).__name__,
                        "error_message": str(exc)})
        raise
    finish_attempt({"event": "completed", "score_sha256": p.sha(SCORE.read_bytes()),
                    "all_gates_pass": score["all_gates_pass"]})
    return score


def run_after_attempt(out: Path, protocol: dict, protocol_sha: str) -> dict:
    out.mkdir(parents=True)
    env = os.environ.copy()
    env.pop("STWO_ZIG_POW_WORKERS", None)
    env["S31_MIXED_NATIVE_PHASES"] = "1"
    records: dict[str, dict] = {}
    binaries_by_name = {}
    raw_sources = {}
    # Package/build/geometry cost is separate. No proof is timed before all
    # three exact native manifests have passed the frozen admission check.
    for name, expected in protocol["source_roster"].items():
        directory = out / name
        directory.mkdir()
        raw_source = p.source(name)
        raw_sources[name] = raw_source
        source_path = directory / "source.s31.json"
        source_path.write_bytes(raw_source)
        built, build_wall = v2.process([
            "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=2",
            "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
            f"-Ds31-name=mixed_cost_v18_topology_transfer_{name}", "-j1", "--prefix",
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
        binaries_by_name[name] = binaries
        records[name] = {"name": name, "call_count": expected["call_count"],
                         "source_sha256": expected["source_sha256"],
                         "binary_sha256": binary_hashes,
                         "manifest_sha256": p.sha(inspected.stdout),
                         "native_manifest": manifest,
                         "build_wall_ns": build_wall, "trials": []}

    def run_claim(name: str, index: int, repeat: int, scored_ordinal: int | None) -> None:
        expected = protocol["source_roster"][name]
        record = records[name]
        directory = out / name
        binaries = binaries_by_name[name]
        raw_source = raw_sources[name]
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
        if {role: p.sha(path.read_bytes()) for role, path in binaries.items()} != record["binary_sha256"]:
            raise ValueError("package binary changed during timing")
        proved, prove_wall = timed_rss([
            str(binaries["prover"]), str(assignment_path), str(proof_path),
            str(emitted_path), str(statement_path)], env)
        (directory / f"{prefix}.prove.stderr").write_bytes(proved.stderr)
        if (proved.returncode or not proof_path.exists() or
                not emitted_path.exists() or emitted_path.read_bytes() != statement):
            raise RuntimeError(f"{name}/{prefix} prover or statement failed")
        verified, verify_wall = timed_rss([
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
        if (phase["fri_pow_ns"] <= 0 or phase["interaction_pow_ns"] <= 0 or
                phase["fri_pow_ns"] + phase["interaction_pow_ns"] >=
                prove_wall["duration"] + verify_wall["duration"]):
            raise ValueError("reported PoW must be positive and below measured verified wall")
        record["trials"].append({
            "ordinal": len(record["trials"]), "scored_ordinal": scored_ordinal,
            "claim_index": index, "repeat": repeat,
            "assignment_sha256": p.sha(assignment),
            "statement_sha256": p.sha(statement),
            "proof_sha256": p.sha(proof_path.read_bytes()),
            "proof_bytes": proof_path.stat().st_size,
            "prover_process_monotonic_ns": prove_wall,
            "external_verifier_process_monotonic_ns": verify_wall,
            "first_verified_process_wall_ns": prove_wall["duration"] + verify_wall["duration"],
            "package_stages_ns": stage["stages_ns"],
            "native_phases_ns": phase,
            "changed_result_rejected_at_interaction_nonce": True})

    # Descriptive post-build and immediate-repeat cost, excluded from score.
    for name in protocol["source_roster"]:
        run_claim(name, 0, 0, None)
        run_claim(name, 0, 1, None)
    for ordinal, task in enumerate(protocol["scored_schedule"]):
        run_claim(task["name"], task["claim_index"], 0, ordinal)
    p.frozen()
    corpus = {"schema": "s31-mixed-cost-v18-topology-transfer-result",
              "protocol_sha256": protocol_sha,
              "v18_model_sha256": protocol["v18_model_sha256"],
              "host": protocol["host"], "records": list(records.values()),
              "verified_proofs": len(records) * (p.CLAIMS + 2),
              "changed_claim_proof_rejections": len(records) * (p.CLAIMS + 2)}
    raw = p.canonical(corpus)
    (out / "result.json").write_bytes(raw)
    RESULT.write_bytes(raw)
    scores = {record["name"]: score_record(
        record, protocol["source_roster"][record["name"]], protocol["gates"])
        for record in records.values()}
    pooled_hits = sum(row["wall_one_draw_interval_hits"] for row in scores.values())
    sample_medians_in_band = sum(row["wall_sample20_median_in_band"] for row in scores.values())
    aggregate = {
        "pooled_wall_one_draw_interval_hits": pooled_hits,
        "pooled_wall_one_draw_interval_coverage": pooled_hits / (p.CLAIMS * len(records)),
        "wall_sample20_medians_in_band": sample_medians_in_band,
        "gates": {
            "pooled_wall_one_draw_coverage": pooled_hits / (p.CLAIMS * len(records)) >=
                protocol["gates"]["wall_one_draw_90_coverage_pooled_min"],
            "wall_sample20_median_band_count": sample_medians_in_band >=
                protocol["gates"]["wall_sample20_median_90_band_source_count_min"],
        },
    }
    score = {"schema": "s31-mixed-cost-v18-topology-transfer-score",
             "protocol_sha256": protocol_sha, "result_sha256": p.sha(raw),
             "sources": scores, "aggregate": aggregate,
             "all_gates_pass": all(row["all_gates_pass"] for row in scores.values()) and
                               all(aggregate["gates"].values())}
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
