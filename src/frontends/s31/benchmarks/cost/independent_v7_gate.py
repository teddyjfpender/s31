#!/usr/bin/env python3
"""Second-source V7 held-out gate math, independent of predictor functions.

This reads the frozen serialized model and raw held-out trials. It does not
fit training coefficients and never imports whole_prover_predictor_v7.
"""

from __future__ import annotations

import math
import statistics

TARGETS = ("paired_prove_and_verify_wall_seconds", "proof_bytes",
           "prover_peak_rss_bytes")
PROCESS = ("prover_process_unattributed_seconds",
           "native_verify_process_wall_seconds")


def require_finite(value: object, label: str, *, positive: bool = True) -> float:
    if (type(value) not in (int, float) or not math.isfinite(value) or
        (value <= 0 if positive else value < 0)):
        raise ValueError(f"{label} must be finite and {'positive' if positive else 'nonnegative'}")
    return float(value)


def percentile(values: list[float], fraction: float) -> float:
    if not values or not 0 <= fraction <= 1:
        raise ValueError("nonempty values and a percentile in [0, 1] are required")
    ordered = sorted(values)
    location = fraction * (len(ordered) - 1)
    before = int(location)
    return ordered[before] * (1 - (location - before)) + ordered[
        min(before + 1, len(ordered) - 1)] * (location - before)


def features(case: dict) -> dict[str, float]:
    raw, padded = case["raw"], case["padded"]
    if not raw or raw.keys() != padded.keys():
        raise ValueError("raw and padded component sets differ")
    if any(type(value) is not int or value < 0
           for table in (raw, padded) for value in table.values()):
        raise ValueError("component rows must be nonnegative integers")
    result = {
        "raw_rows": require_finite(sum(raw.values()), "raw rows"),
        "padded_rows": require_finite(sum(padded.values()), "padded rows"),
        "preprocessed_cells": require_finite(case["preprocessed_cells"], "preprocessed cells"),
        "hash_work": require_finite(1 + raw.get("blake_g", 0), "hash work"),
        "constant": 1.0,
    }
    if case["family"] == "chip":
        binding = case["chip_manifest_binding"]
        result["chip_trace_cells"] = require_finite(binding["chip_trace_cells"],
                                                     "chip trace cells")
        result["chip_fri_domain_rows"] = require_finite(binding["chip_fri_domain_rows"],
                                                         "chip FRI rows")
    return result


def fitted_value(model: dict, scale: float) -> float:
    require_finite(scale, "feature")
    if "constant" in model:
        return require_finite(model["constant"], "constant fit")
    return require_finite(math.exp(model["intercept"] + model["slope"] * math.log(scale)),
                          "log fit")


def prediction(policy: dict, x: dict) -> dict:
    wall = sum(fitted_value(stage["fit"], x[stage["feature"]])
               for stage in policy["wall_stages"].values())
    wall_ratio = policy["wall_interval"]
    proof = policy["proof_bytes"]
    proof_center = fitted_value(proof["fit"], x[proof["feature"]])
    error = require_finite(proof["training_loo_max_abs_log_error"], "proof envelope")
    proof_lower_ratio = proof.get("stochastic_trial_ratio_min",
                                  proof["training_trial_ratio_p05"])
    proof_upper_ratio = proof.get("stochastic_trial_ratio_max",
                                  proof["training_trial_ratio_p95"])
    rss = policy["prover_peak_rss_bytes"]
    scale = x[rss["feature"]]
    if rss["fit_kind"] == "positive_affine_rss":
        rss_center = (rss["fit"]["intercept_bytes"] +
                      rss["fit"]["bytes_per_padded_row"] * scale)
    elif rss["fit_kind"] == "log_linear_rss":
        rss_center = fitted_value(rss["fit"], scale)
    else:
        raise ValueError("unsupported RSS model")
    require_finite(rss_center, "RSS center")
    radius = max(rss["radius_bytes"], rss["relative_radius"] * rss_center)
    return {
        TARGETS[0]: {"center": wall,
                     "lower": wall * wall_ratio["ratio_p05"],
                     "upper": wall * wall_ratio["ratio_p95"]},
        TARGETS[1]: {"center": proof_center,
                     "lower": proof_center * math.exp(-error) * proof_lower_ratio,
                     "upper": proof_center * math.exp(error) * proof_upper_ratio},
        TARGETS[2]: {"center": rss_center,
                     "lower": max(0.0, rss_center - radius),
                     "upper": rss_center + radius},
    }


def observations(case: dict, target: str) -> list[float]:
    if target == TARGETS[0]:
        return [require_finite(trial["prove_seconds"], "prover wall") +
                require_finite(trial["verify_seconds"], "verifier wall")
                for trial in case["trials"]]
    return [require_finite(trial[target], target) for trial in case["trials"]]


def process_observations(case: dict, stage: str) -> list[float]:
    if stage == PROCESS[1]:
        return [require_finite(trial["verify_seconds"], stage)
                for trial in case["trials"]]
    values = []
    for trial in case["trials"]:
        residual = trial["prove_seconds"] - trial["prover_stages"]["total_through_verification_seconds"]
        if residual < -.003:
            raise ValueError("native runtime exceeds prover process wall")
        values.append(max(1e-9, residual))
    return values


def program_results(name: str, case: dict, policy: dict, gates: dict) -> dict:
    x = features(case)
    predicted = prediction(policy, x)
    targets = {}
    for target in TARGETS:
        values = observations(case, target)
        point = statistics.mean(values) if target == TARGETS[0] else statistics.median(values)
        interval = predicted[target]
        targets[target] = {
            "predicted": interval,
            "measured_point": point,
            "measured_p90": percentile(values, .9),
            "relative_point_error": abs(interval["center"] - point) / point,
            "covered_trials": sum(interval["lower"] <= value <= interval["upper"]
                                  for value in values),
            "trial_count": len(values),
            "interval_upper_to_measured_point": interval["upper"] / point,
        }
    process = {}
    for stage in PROCESS:
        values = process_observations(case, stage)
        observed = statistics.mean(values)
        fitted = policy["wall_stages"][stage]
        expected = fitted_value(fitted["fit"], x[fitted["feature"]])
        process[stage] = {
            "measured_mean": observed, "predicted_mean": expected,
            "absolute_mean_error_seconds": abs(expected - observed),
            "relative_mean_error": abs(expected - observed) / observed,
        }
    process_pass = all(
        row["relative_mean_error"] <= gates["per_program_process_stage_mean_relative_error_max"] or
        row["absolute_mean_error_seconds"] <= gates["per_program_process_stage_mean_absolute_error_seconds_max"]
        for row in process.values())
    return {"program": name, "family": case["family"], "source_sha256": case["source_sha256"],
            "targets": targets, "process": process, "process_stage_gate_pass": process_pass}


def family_gate(members: list[dict], gates: dict) -> tuple[dict, bool]:
    if len(members) < gates["minimum_validation_programs_per_family"]:
        return {}, False
    if any(len(item["targets"][TARGETS[0]]["predicted"]) != 3 for item in members):
        raise ValueError("missing target prediction")
    accuracy = {}
    for target in TARGETS:
        rows = [item["targets"][target] for item in members]
        errors = [row["relative_point_error"] for row in rows]
        accuracy[target] = {
            "programs": len(members),
            "median_program_relative_error": statistics.median(errors),
            "p90_program_relative_error": percentile(errors, .9),
            "max_program_relative_error": max(errors),
            "trial_interval_coverage": sum(row["covered_trials"] for row in rows) /
                                       sum(row["trial_count"] for row in rows),
            "median_interval_upper_to_measured_point": statistics.median(
                row["interval_upper_to_measured_point"] for row in rows),
        }
    minimum_trials = gates["minimum_validation_trials_per_program"]
    passed = all(row["targets"][TARGETS[0]]["trial_count"] >= minimum_trials
                 for row in members)
    wall = accuracy[TARGETS[0]]
    passed &= (wall["p90_program_relative_error"] <=
               gates["per_family_whole_wall_program_mean_p90_relative_error_max"] and
               wall["trial_interval_coverage"] >=
               gates["per_family_whole_wall_trial_interval_coverage_min"] and
               wall["median_interval_upper_to_measured_point"] <=
               gates["per_family_whole_wall_median_interval_upper_to_measured_mean_max"])
    for target, key in ((TARGETS[1], "per_family_proof_bytes_program_median_p90_relative_error_max"),
                        (TARGETS[2], "per_family_prover_rss_program_median_p90_relative_error_max")):
        passed &= (accuracy[target]["p90_program_relative_error"] <= gates[key] and
                   accuracy[target]["trial_interval_coverage"] >=
                   gates["per_family_proof_bytes_and_rss_trial_interval_coverage_min"])
    for member in members:
        rss = member["targets"][TARGETS[2]]
        passed &= (rss["covered_trials"] / rss["trial_count"] >=
                   gates["per_program_rss_trial_interval_coverage_min"] and
                   rss["interval_upper_to_measured_point"] <=
                   gates["per_program_rss_interval_upper_to_measured_median_max"])
    return accuracy, bool(passed)


def check_saved_evaluation(model: dict, corpus: dict, protocol: dict,
                           saved: dict) -> dict:
    """Recompute every target prediction and all pass/fail gates from raw trials."""
    if (model["schema"] != "s31-whole-prover-cost-model-v7" or
        corpus["schema"] != "s31-whole-prover-cost-corpus-v7" or
        corpus["split"] != "validation" or
        saved["schema"] != "s31-whole-prover-cost-evaluation-v7" or
        corpus["protocol_sha256"] != model["protocol_sha256"] or
        saved["protocol_sha256"] != model["protocol_sha256"]):
        raise ValueError("model/corpus/evaluation schema or protocol mismatch")
    if corpus["cases"].keys() != protocol["inventory"]["validation"].keys():
        raise ValueError("held-out program roster differs from protocol")
    gates = protocol["accuracy_gate"]
    computed = {}
    for name, case in corpus["cases"].items():
        family = case["family"]
        frozen = protocol["inventory"]["validation"][name]
        policy = model["families"][family]
        if (case["source_sha256"] != frozen["source_sha256"] or
            case["assignment_sha256"] != frozen["assignment_sha256"] or
            case["lowering"] != frozen["lowering"] or
            any(case[key] != policy[key] for key in ("lowering", "profile", "visible_fri"))):
            raise ValueError(f"{name}: case differs from frozen model or workload")
        computed[name] = program_results(name, case, policy, gates)
    saved_rows = {row["program"]: row for row in saved["programs"]}
    if saved_rows.keys() != computed.keys():
        raise ValueError("saved evaluation program set differs")
    for name, expected in computed.items():
        actual = saved_rows[name]
        if (actual["family"] != expected["family"] or
            actual["source_sha256"] != expected["source_sha256"] or
            actual["process_stage_gate_pass"] is not expected["process_stage_gate_pass"]):
            raise ValueError(f"{name}: saved family/source/process gate differs")
        for target, result in expected["targets"].items():
            reported = actual["targets"][target]
            for key, value in result.items():
                if key == "predicted":
                    for part, number in value.items():
                        close(reported[key][part], number, f"{name}.{target}.{part}")
                elif key in ("covered_trials", "trial_count"):
                    if reported[key] != value:
                        raise ValueError(f"{name}.{target}.{key} differs")
                else:
                    close(reported[key], value, f"{name}.{target}.{key}")
        for stage, row in expected["process"].items():
            for key, value in row.items():
                close(actual["stages"][stage][key], value, f"{name}.{stage}.{key}")
    accuracy = {}
    passed = all(item["process_stage_gate_pass"] for item in computed.values())
    for family in protocol["profiles"]:
        members = [item for item in computed.values() if item["family"] == family]
        result, gate = family_gate(members, gates)
        accuracy[family] = result
        passed &= gate
    if saved["local_accuracy_gate_pass"] is not bool(passed):
        raise ValueError("saved held-out gate pass differs")
    if saved["automatic_lowering_selection_enabled"] is not False:
        raise ValueError("automatic lowering must stay disabled")
    for family, result in accuracy.items():
        for target, row in result.items():
            for key, value in row.items():
                if key == "programs":
                    if saved["accuracy"][family][target][key] != value:
                        raise ValueError(f"{family}.{target}.programs differs")
                else:
                    close(saved["accuracy"][family][target][key], value,
                          f"{family}.{target}.{key}")
    return {"local_accuracy_gate_pass": bool(passed),
            "programs_checked": len(computed),
            "trials_checked": sum(len(case["trials"]) for case in corpus["cases"].values()),
            "second_source_gate_math": True}


def close(actual: object, expected: float, label: str) -> None:
    if (type(actual) not in (int, float) or not math.isfinite(actual) or
        not math.isclose(actual, expected, rel_tol=1e-10, abs_tol=1e-8)):
        raise ValueError(f"independent held-out value differs: {label}")
