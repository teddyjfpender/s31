#!/usr/bin/env python3
"""Independent V17 scoring, frozen artifact checks, and exact native replay."""

from __future__ import annotations

import argparse
import json
import statistics
import subprocess
import sys
from pathlib import Path

import protocol as p
sys.path.insert(0, str(p.S31 / "tests/acceptance/mixed_boundary"))
from registry_manifest_digest import digest as registry_manifest_digest

RESULT = p.LANGUAGE / "mixed-cost-v17-mixed-calls-result.json"
SCORE = p.LANGUAGE / "mixed-cost-v17-mixed-calls-score.json"
AUDIT = p.LANGUAGE / "mixed-cost-v17-mixed-calls-audit.json"
ATTEMPT = p.LANGUAGE / "mixed-cost-v17-mixed-calls-attempt.jsonl"


def independently_check_calls(calls: list[dict], frozen_calls: list[dict]) -> None:
    if len(calls) != len(frozen_calls):
        raise ValueError("saved native call count differs")
    prior_outputs = None
    seen_addresses: set[int] = set()
    for observed, expected in zip(calls, frozen_calls, strict=True):
        if any(observed.get(field) != value for field, value in expected.items()):
            raise ValueError("saved native call semantics differ from frozen source")
        inputs, outputs = observed.get("input"), observed.get("output")
        if any(type(group) is not list or len(group) != 4 or
               any(type(address) is not int or address < 0 for address in group) or
               len(set(group)) != 4 for group in (inputs, outputs)):
            raise ValueError("saved native call addresses malformed")
        if prior_outputs is not None and inputs != prior_outputs:
            raise ValueError("saved native call chain differs")
        if seen_addresses.intersection(outputs):
            raise ValueError("saved native call output address was reused")
        seen_addresses.update(inputs)
        seen_addresses.update(outputs)
        prior_outputs = outputs


def independently_check_slots(slots: list[dict], frozen_slots: list[dict]) -> None:
    if len(slots) != len(frozen_slots):
        raise ValueError("saved native slot count differs")
    for observed, expected in zip(slots, frozen_slots, strict=True):
        if any(observed.get(field) != value for field, value in expected.items()):
            raise ValueError("saved native slot layout differs from frozen prediction")


def calculated_score(rows: list[dict], prediction: dict, gates: dict) -> dict:
    scored = rows[2:]
    if len(scored) != p.CLAIMS or sorted(row["claim_index"] for row in scored) != list(
            range(1, p.CLAIMS + 1)):
        raise ValueError("scored claim roster differs")
    residuals = [row["first_verified_process_wall_ns"] -
                 row["native_phases_ns"]["fri_pow_ns"] -
                 row["native_phases_ns"]["interaction_pow_ns"] for row in scored]
    if any(value <= 0 for value in residuals):
        raise ValueError("nonpositive independently recomputed non-PoW residual")
    walls = [row["first_verified_process_wall_ns"] for row in scored]
    sizes = [row["proof_bytes"] for row in scored]
    observed_wall = statistics.median(walls)
    observed_size = statistics.median(sizes)
    expected_wall = prediction["warm_wall_one_draw_quantile_ns"]["0.5"]
    expected_size = prediction["proof_bytes_center"]
    wall_low = prediction["warm_wall_one_draw_quantile_ns"]["0.05"]
    wall_high = prediction["warm_wall_one_draw_quantile_ns"]["0.95"]
    median_low = prediction["warm_wall_sample20_median_quantile_ns"]["0.05"]
    median_high = prediction["warm_wall_sample20_median_quantile_ns"]["0.95"]
    size_low, size_high = prediction["proof_bytes_interval"]
    wall_error = abs(observed_wall - expected_wall) / observed_wall
    size_error = abs(observed_size - expected_size) / observed_size
    wall_hits = sum(wall_low <= value <= wall_high for value in walls)
    wall_coverage = wall_hits / len(walls)
    size_coverage = sum(size_low <= value <= size_high for value in sizes) / len(sizes)
    prover_rss = statistics.median(row["prover_process_monotonic_ns"]["peak_rss_bytes"] for row in scored)
    verifier_rss = statistics.median(row["external_verifier_process_monotonic_ns"]["peak_rss_bytes"] for row in scored)
    prover_rss_error = abs(prover_rss - prediction["prover_peak_rss_median_bytes"]) / prover_rss
    verifier_rss_error = abs(verifier_rss - prediction["verifier_peak_rss_median_bytes"]) / verifier_rss
    nonpow = statistics.median(residuals)
    nonpow_error = abs(nonpow - prediction["nonpow_whole_process_center_ns"]) / nonpow
    phase_medians = {key: statistics.median(row["package_stages_ns"][key] for row in scored)
                     for key in p.cost_model.PHASES}
    phase_errors = {key: abs(value - prediction["native_package_phase_center_ns"][key]) / value
                    for key, value in phase_medians.items()}
    checks = {
        "wall_median_error": wall_error <= gates["wall_median_relative_error_per_source_max"],
        "wall_one_draw_interval_coverage": wall_coverage >= gates["wall_one_draw_90_coverage_per_source_min"],
        "proof_median_error": size_error <= gates["proof_median_relative_error_per_source_max"],
        "proof_interval_coverage": size_coverage >= gates["proof_90_interval_coverage_per_source_min"],
        "prover_rss_median_error": prover_rss_error <= gates["prover_rss_median_relative_error_per_source_max"],
        "verifier_rss_median_error": verifier_rss_error <= gates["verifier_rss_median_relative_error_per_source_max"],
        "nonpow_wall_median_error": nonpow_error <= gates["nonpow_wall_median_relative_error_per_source_max"],
    }
    checks.update({f"native_phase_{key}_median_error": error <=
                   gates["native_phase_median_relative_error_per_source_max"]
                   for key, error in phase_errors.items()})
    return {"wall_median_ns": observed_wall, "proof_median_bytes": observed_size,
            "wall_median_relative_error": wall_error,
            "wall_one_draw_interval_hits": wall_hits,
            "wall_one_draw_interval_coverage": wall_coverage,
            "wall_sample20_median_in_band": median_low <= observed_wall <= median_high,
            "proof_median_relative_error": size_error,
            "proof_interval_coverage": size_coverage,
            "prover_rss_median_relative_error": prover_rss_error,
            "verifier_rss_median_relative_error": verifier_rss_error,
            "nonpow_wall_median_relative_error": nonpow_error,
            "observed_native_package_phase_medians_ns": phase_medians,
            "native_package_phase_relative_errors": phase_errors,
            "gates": checks, "all_gates_pass": all(checks.values())}


def run(out: Path, native: bool) -> dict:
    p.frozen()
    protocol_raw = p.PROTOCOL.read_bytes()
    model_raw = p.MODEL.read_bytes()
    result_raw = RESULT.read_bytes()
    score_raw = SCORE.read_bytes()
    protocol = p.v2.parse(protocol_raw)
    result = p.v2.parse(result_raw)
    score = p.v2.parse(score_raw)
    if (protocol_raw != p.canonical(protocol) or
            model_raw != p.canonical(p.v2.parse(model_raw)) or
            result_raw != p.canonical(result) or
            score_raw != p.canonical(score) or
            protocol.get("schema") != "s31-mixed-cost-v17-mixed-calls-protocol" or
            result.get("schema") != "s31-mixed-cost-v17-mixed-calls-result" or
            score.get("schema") != "s31-mixed-cost-v17-mixed-calls-score" or
            p.sha(model_raw) != protocol["v17_model_sha256"] or
            result.get("v17_model_sha256") != protocol["v17_model_sha256"] or
            result.get("host") != protocol["host"] or
            p.sha(protocol_raw) != result["protocol_sha256"] or
            p.sha(protocol_raw) != score["protocol_sha256"] or
            p.sha(result_raw) != score["result_sha256"] or
            (out / "result.json").read_bytes() != result_raw or
            set(score["sources"]) != set(protocol["source_roster"])):
        raise ValueError("frozen identity or canonical result/score differs")
    marker_raw = ATTEMPT.read_bytes()
    marker_lines = marker_raw.splitlines(keepends=True)
    if len(marker_lines) != 2:
        raise ValueError("fixed one-run marker must contain exactly start and terminal records")
    started, ended = [p.v2.parse(line) for line in marker_lines]
    if (any(line != p.canonical(value) for line, value in zip(
            marker_lines, (started, ended), strict=True)) or
            started.get("schema") != "s31-mixed-cost-v17-attempt-v1" or
            started.get("event") != "started" or
            started.get("protocol_sha256") != p.sha(protocol_raw) or
            started.get("output_dir") != str(out.resolve()) or
            not isinstance(started.get("time_ns"), int) or started["time_ns"] <= 0 or
            ended.get("event") != "completed" or
            ended.get("score_sha256") != p.sha(score_raw) or
            ended.get("all_gates_pass") != score["all_gates_pass"] or
            not isinstance(ended.get("time_ns"), int) or
            ended["time_ns"] < started["time_ns"]):
        raise ValueError("fixed one-run marker does not match scored artifacts")
    checked = 0
    scored = {}
    global_timing_order = []
    if [row["name"] for row in result["records"]] != list(protocol["source_roster"]):
        raise ValueError("result source roster/order differs from protocol")
    for record in result["records"]:
        name = record["name"]
        expected = protocol["source_roster"][name]
        directory = out / name
        source = (directory / "source.s31.json").read_bytes()
        if (source != (p.SOURCE_DIR / f"{name}.json").read_bytes() or
                source != p.source(name) or
                p.sha(source) != expected["source_sha256"] or
                record["source_sha256"] != expected["source_sha256"] or
                len(record["trials"]) != p.CLAIMS + 2):
            raise ValueError(f"source or trial roster differs: {name}")
        binaries = {role: directory / "package/bin" /
                    f"s31-mixed_cost_v17_mixed_calls_{name}-mixed-general-{suffix}"
                    for role, suffix in (("prover", "prover"),
                                         ("verifier", "native-verifier"),
                                         ("manifest", "manifest"))}
        if {role: p.sha(path.read_bytes()) for role, path in binaries.items()} != record[
                "binary_sha256"]:
            raise ValueError(f"saved binary hashes differ: {name}")
        manifest_raw = (directory / "manifest.stdout").read_bytes()
        manifest = p.v2.parse(manifest_raw)
        geometry = expected["expected_geometry"]
        if (manifest != record["native_manifest"] or
                p.sha(manifest_raw) != record["manifest_sha256"] or
                manifest["source_sha256"] != expected["source_sha256"] or
                manifest["call_count"] != expected["call_count"] or
                manifest["slot_count"] != geometry["slots"] or
                manifest["total_constraints"] != geometry["constraints"] or
                manifest["tree_columns"] != geometry["tree_columns"] or
                [slot["trace_log_size"] for slot in manifest["slots"]] !=
                geometry["slot_trace_logs"] or
                [slot["n_constraints"] for slot in manifest["slots"]] !=
                geometry["slot_constraints"] or
                manifest["max_column_log_size"] != geometry["max_column_log_size"] or
                manifest["composition_log_size"] != geometry["composition_log_size"] or
                manifest["interaction_pow_bits"] != 20 or
                manifest["pcs"]["fri_config"]["pow_bits"] != 26 or
                manifest["registry_manifest_sha256"] !=
                registry_manifest_digest(manifest)):
            raise ValueError(f"saved native manifest differs: {name}")
        independently_check_slots(manifest["slots"], geometry["slot_layout"])
        independently_check_calls(manifest["calls"], expected["expected_calls"])
        scored_indices = [task for task in protocol["scored_schedule"] if task["name"] == name]
        if [row["claim_index"] for row in record["trials"][2:]] != [
                task["claim_index"] for task in scored_indices]:
            raise ValueError(f"interleaved claim order differs: {name}")
        for ordinal, row in enumerate(record["trials"]):
            index = 0 if ordinal < 2 else scored_indices[ordinal - 2]["claim_index"]
            repeat = ordinal if ordinal < 2 else 0
            scored_ordinal = None if ordinal < 2 else protocol["scored_schedule"].index(
                scored_indices[ordinal - 2])
            prefix = f"a{index:02d}r{repeat}"
            assignment = (directory / f"{prefix}.assignment.json").read_bytes()
            statement = (directory / f"{prefix}.statement.json").read_bytes()
            changed = (directory / f"{prefix}.changed.json").read_bytes()
            proof_path = directory / f"{prefix}.proof"
            proof = proof_path.read_bytes()
            recomputed_source, recomputed_assignment, recomputed_statement = p.case(
                name, index)
            if (row["ordinal"] != ordinal or row["scored_ordinal"] != scored_ordinal or
                    row["claim_index"] != index or
                    row["repeat"] != repeat or
                    (source, assignment, statement) !=
                    (recomputed_source, recomputed_assignment, recomputed_statement) or
                    changed != p.v2.changed_result(source, statement) or
                    p.sha(assignment) != expected["assignment_sha256"][index] or
                    p.sha(statement) != expected["statement_sha256"][index] or
                    p.sha(assignment) != row["assignment_sha256"] or
                    p.sha(statement) != row["statement_sha256"] or
                    p.sha(proof) != row["proof_sha256"] or
                    len(proof) != row["proof_bytes"] or
                    (directory / f"{prefix}.emitted.json").read_bytes() != statement):
                raise ValueError(f"claim, changed-result, or proof differs: {name}/{prefix}")
            stage = p.v2.tagged((directory / f"{prefix}.prove.stderr").read_bytes(),
                                b"S31_MIXED_STAGE_V1")
            phase = p.v2.tagged((directory / f"{prefix}.prove.stderr").read_bytes(),
                                b"S31_MIXED_NATIVE_PHASE_V1")
            if (stage["source_sha256"] != expected["source_sha256"] or
                    stage["proof_bytes"] != len(proof) or
                    stage["stages_ns"] != row["package_stages_ns"] or
                    phase != row["native_phases_ns"] or
                    phase["source_sha256"] != expected["source_sha256"] or
                    phase["fri_pow_ns"] <= 0 or
                    phase["interaction_pow_ns"] <= 0 or
                    b"verified" not in (directory / f"{prefix}.verified.stderr").read_bytes() or
                    (directory / f"{prefix}.changed.stderr").read_bytes().strip() !=
                    b"error: InvalidMixedInteractionNonce"):
                raise ValueError(f"native report/control differs: {name}/{prefix}")
            prove = row["prover_process_monotonic_ns"]
            verify = row["external_verifier_process_monotonic_ns"]
            if (any(set(endpoint) != {"start", "end", "duration", "peak_rss_bytes", "peak_rss_method"} or
                    endpoint["end"] - endpoint["start"] != endpoint["duration"] or
                    endpoint["duration"] <= 0 or
                    not isinstance(endpoint["peak_rss_bytes"], int) or
                    endpoint["peak_rss_bytes"] <= 0 or
                    endpoint["peak_rss_method"] not in
                    {"darwin-time-max-rss-bytes", "gnu-time-max-rss-kib"}
                    for endpoint in (prove, verify)) or
                    prove["duration"] + verify["duration"] != row[
                        "first_verified_process_wall_ns"] or
                    phase["fri_pow_ns"] + phase["interaction_pow_ns"] >= row[
                        "first_verified_process_wall_ns"]):
                raise ValueError(f"monotonic timing endpoints differ: {name}/{prefix}")
            if scored_ordinal is not None:
                global_timing_order.append((prove["start"], scored_ordinal))
            if native:
                honest = subprocess.run([str(binaries["verifier"]), str(proof_path),
                                         str(directory / f"{prefix}.statement.json")],
                                        capture_output=True, check=False)
                negative = subprocess.run([str(binaries["verifier"]), str(proof_path),
                                           str(directory / f"{prefix}.changed.json")],
                                          capture_output=True, check=False)
                if (honest.returncode or b"verified" not in honest.stderr or
                        not p.v2.proof_layer_rejection(negative)):
                    raise ValueError(f"independent native replay differs: {name}/{prefix}")
            checked += 1
        scored[name] = calculated_score(record["trials"], expected["prediction"],
                                        protocol["gates"])
        official = score["sources"][name]
        for key in ("observed_warm_wall_median_ns", "observed_proof_median_bytes",
                    "wall_median_relative_error", "wall_one_draw_interval_hits",
                    "wall_one_draw_interval_coverage", "wall_sample20_median_in_band",
                    "proof_median_relative_error", "proof_interval_coverage",
                    "prover_rss_median_relative_error", "verifier_rss_median_relative_error",
                    "nonpow_wall_median_relative_error",
                    "observed_native_package_phase_medians_ns",
                    "native_package_phase_relative_errors"):
            independent_key = "wall_median_ns" if key == "observed_warm_wall_median_ns" \
                else "proof_median_bytes" if key == "observed_proof_median_bytes" else key
            if official[key] != scored[name][independent_key]:
                raise ValueError(f"independent score differs: {name}/{key}")
        if (official["gates"] != scored[name]["gates"] or
                official["all_gates_pass"] != scored[name]["all_gates_pass"]):
            raise ValueError(f"independent gates differ: {name}")
        rows = record["trials"][2:]
        if (official["scored_trials"] != len(rows) or
                official["build_wall_ns"] != record["build_wall_ns"] or
                official["prover_peak_rss_median_bytes"] != statistics.median(
                    row["prover_process_monotonic_ns"]["peak_rss_bytes"] for row in rows) or
                official["external_verifier_peak_rss_median_bytes"] != statistics.median(
                    row["external_verifier_process_monotonic_ns"]["peak_rss_bytes"] for row in rows) or
                official["verified_wall_minus_reported_pow_median_ns"] != statistics.median(
                    row["first_verified_process_wall_ns"] -
                    row["native_phases_ns"]["fri_pow_ns"] -
                    row["native_phases_ns"]["interaction_pow_ns"] for row in rows)):
            raise ValueError(f"independent memory, build or phase score differs: {name}")
    if [ordinal for _, ordinal in sorted(global_timing_order)] != list(range(
            p.CLAIMS * len(p.SOURCES))):
        raise ValueError("physical process timing order differs from frozen interleaved schedule")
    pooled_hits = sum(row["wall_one_draw_interval_hits"] for row in scored.values())
    median_hits = sum(row["wall_sample20_median_in_band"] for row in scored.values())
    expected_aggregate = {
        "pooled_wall_one_draw_interval_hits": pooled_hits,
        "pooled_wall_one_draw_interval_coverage": pooled_hits / (p.CLAIMS * len(p.SOURCES)),
        "wall_sample20_medians_in_band": median_hits,
        "gates": {
            "pooled_wall_one_draw_coverage": pooled_hits / (p.CLAIMS * len(p.SOURCES)) >=
                protocol["gates"]["wall_one_draw_90_coverage_pooled_min"],
            "wall_sample20_median_band_count": median_hits >=
                protocol["gates"]["wall_sample20_median_90_band_source_count_min"],
        },
    }
    if (score["aggregate"] != expected_aggregate or
            checked != len(p.SOURCES) * (p.CLAIMS + 2) or
            checked != result["verified_proofs"] or
            checked != result["changed_claim_proof_rejections"] or
            score["all_gates_pass"] != (all(row["all_gates_pass"] for row in scored.values()) and
                                        all(expected_aggregate["gates"].values()))):
        raise ValueError("proof totals or aggregate gate differ")
    return {"schema": "s31-mixed-cost-v17-mixed-calls-audit",
            "attempt_marker_sha256": p.sha(marker_raw),
            "protocol_sha256": p.sha(protocol_raw),
            "model_sha256": p.sha(model_raw),
            "result_sha256": p.sha(result_raw),
            "score_sha256": p.sha(score_raw),
            "exact_changed_result_files": checked,
            "exact_claim_and_proof_files": checked,
            "native_reports_and_timing_endpoints": checked,
            "native_replay": native,
            "native_replayed_proofs": checked if native else 0,
            "source_scores": scored,
            "all_gates_pass": score["all_gates_pass"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    report = run(args.out, args.native)
    if args.write:
        if AUDIT.exists():
            raise ValueError("independent audit artifact already exists")
        AUDIT.write_bytes(p.canonical(report))
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
