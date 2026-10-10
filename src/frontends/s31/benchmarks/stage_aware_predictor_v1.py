#!/usr/bin/env python3
"""Fit the pinned S31 stage model and evaluate a new, sealed held-out split."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
from pathlib import Path

PROTOCOL = Path(__file__).resolve().parents[4] / "design/s31/measurements/stage-aware-cost-v1.json"
DIRECT_STAGES = (
    "runtime_witness_seconds", "runtime_setup_seconds",
    "runtime_prove_excluding_pow_seconds", "runtime_interaction_pow_seconds",
    "runtime_fri_pow_seconds", "runtime_runtime_other_seconds",
    "prover_process_unattributed_seconds", "native_verify_process_wall_seconds",
)
OPAQUE_STAGES = (
    "runtime_witness_seconds", "runtime_setup_seconds",
    "runtime_prove_seconds_when_pow_opaque", "runtime_runtime_other_seconds",
    "prover_process_unattributed_seconds", "native_verify_process_wall_seconds",
)
TARGETS = ("paired_prove_and_verify_wall_seconds", "proof_bytes", "prover_peak_rss_bytes")


def positive(value: object, label: str) -> float:
    if isinstance(value, bool) or not isinstance(value, (int, float)) or not math.isfinite(value) or value <= 0:
        raise ValueError(f"{label} must be positive and finite")
    return float(value)


def quantile(values: list[float], fraction: float) -> float:
    if not values or not 0 <= fraction <= 1:
        raise ValueError("quantile needs values and a fraction in [0,1]")
    ordered = sorted(values)
    rank = fraction * (len(ordered) - 1)
    lower = int(rank)
    return ordered[lower] + (ordered[min(lower + 1, len(ordered) - 1)] - ordered[lower]) * (rank - lower)


def features(case: dict) -> dict[str, float]:
    raw = case["raw"]
    padded = case["padded"]
    if raw.keys() != padded.keys():
        raise ValueError("raw and padded component sets differ")
    result = {
        "raw_rows": positive(sum(raw.values()), "raw rows"),
        "padded_rows": positive(sum(padded.values()), "padded rows"),
        "preprocessed_cells": positive(case["preprocessed_cells"], "preprocessed cells"),
        "hash_work": positive(1 + raw.get("blake_g", 0), "hash work"),
        "constant": 1.0,
    }
    if any(isinstance(value, bool) or not isinstance(value, int) or value < 0
           for table in (raw, padded) for value in table.values()):
        raise ValueError("component rows must be nonnegative integers")
    return result


def stage_value(trial: dict, stage: str) -> float:
    stages = trial.get("prover_stages")
    if not isinstance(stages, dict):
        raise ValueError("native stage timers are missing")
    if stage == "prover_process_unattributed_seconds":
        value = trial["prove_seconds"] - stages["total_through_verification_seconds"]
        if value < -0.003:
            raise ValueError("native runtime exceeds prover process wall")
        return positive(max(1e-9, value), stage)
    if stage == "native_verify_process_wall_seconds":
        return positive(trial["verify_seconds"], stage)
    if stage == "runtime_prove_seconds_when_pow_opaque":
        return positive(stages["prove_seconds"], stage)
    if stage.startswith("runtime_"):
        return positive(stages[stage[len("runtime_"):]], stage)
    return positive(trial[stage], stage)


def stages_for_family(family: str) -> tuple[str, ...]:
    return OPAQUE_STAGES if family == "hash" else DIRECT_STAGES


def checked_cases(corpus: dict, split: str, protocol: dict) -> list[dict]:
    if corpus.get("schema") != "s31-stage-aware-cost-corpus-v1" or corpus.get("split") != split:
        raise ValueError(f"expected {split} stage-aware corpus")
    protocol_digest = hashlib.sha256(PROTOCOL.read_bytes()).hexdigest()
    if corpus.get("protocol_sha256") != protocol_digest:
        raise ValueError("corpus was produced against a different protocol")
    cases = corpus.get("cases")
    if not isinstance(cases, dict):
        raise ValueError("missing cases")
    expected = protocol["splits"][split]
    expected_names = ({f"arithmetic_{rounds}" for rounds in expected["arithmetic_rounds"]} |
                      {f"hash_{depth}" for depth in expected["hash_depths"]} |
                      {f"signed_{'quotient' if split == 'validation' else 'div_rem'}_{width}"
                       for width in expected["signed_widths"]})
    if set(cases) != expected_names:
        raise ValueError("wrong program set for prospective split")
    if corpus.get("samples_per_program") != protocol["samples_per_program"]:
        raise ValueError("wrong declared trial count")
    records = []
    sources: set[str] = set()
    assignments: set[str] = set()
    for name, case in sorted(cases.items()):
        family = case["family"]
        if family not in protocol["profiles"] or case["lowering"] != protocol["profiles"][family]:
            raise ValueError(f"{name}: unexpected family/profile")
        source = case["source_sha256"]
        if not isinstance(source, str) or len(source) != 64 or source in sources:
            raise ValueError(f"{name}: duplicate or invalid source digest")
        sources.add(source)
        trial_list = case["trials"]
        digests = case["assignment_sha256"]
        if len(trial_list) != protocol["samples_per_program"] or len(digests) != len(trial_list):
            raise ValueError(f"{name}: wrong trial count")
        for digest, trial in zip(digests, trial_list):
            if not isinstance(digest, str) or len(digest) != 64 or digest in assignments:
                raise ValueError(f"{name}: duplicate or invalid assignment digest")
            assignments.add(digest)
            if trial["native_verifier_accepted"] is not True or not trial["changed_public_statement_rejected"]:
                raise ValueError(f"{name}: native proof or changed-claim control failed")
            if trial["independent_value_oracle"]["status"] != "passed":
                raise ValueError(f"{name}: independent value oracle failed")
            for stage in (*stages_for_family(family), "proof_bytes", "prover_peak_rss_bytes"):
                stage_value(trial, stage)
        records.append({"name": name, "family": family, "source": source,
                        "features": features(case), "case": case})
    for family in protocol["profiles"]:
        family_cases = [item["case"] for item in records if item["family"] == family]
        expected_family_count = (len(expected["arithmetic_rounds"]) if family == "arithmetic" else
                                 len(expected["hash_depths"]) if family == "hash" else
                                 len(expected["signed_widths"]))
        if len(family_cases) != expected_family_count:
            raise ValueError(f"{family}: wrong number of programs")
        for key in ("compiler_sha256", "lowering", "profile", "visible_fri"):
            if len({json.dumps(case[key], sort_keys=True) for case in family_cases}) != 1:
                raise ValueError(f"{family}: mixed {key}")
    if len({item["case"]["compiler_sha256"] for item in records}) != 1:
        raise ValueError("compiler digest differs across families")
    return records


def log_fit(points: list[tuple[float, float]]) -> dict:
    xs = [math.log(positive(x, "scale")) for x, _ in points]
    ys = [math.log(positive(y, "stage median")) for _, y in points]
    if len(points) < 2:
        raise ValueError("log fit needs two programs")
    mean_x, mean_y = statistics.mean(xs), statistics.mean(ys)
    denominator = sum((x - mean_x) ** 2 for x in xs)
    if denominator < 1e-12:
        raise ValueError("training scales are not distinct")
    slope = sum((x - mean_x) * (y - mean_y) for x, y in zip(xs, ys)) / denominator
    return {"intercept": mean_y - slope * mean_x, "slope": slope}


def estimate(fit: dict, feature: float) -> float:
    if "constant" in fit:
        return fit["constant"]
    return math.exp(fit["intercept"] + fit["slope"] * math.log(feature))


def stage_fit(records: list[dict], stage: str, feature_name: str) -> dict:
    points = []
    ratios = []
    for item in records:
        observed = [stage_value(trial, stage) for trial in item["case"]["trials"]]
        median = statistics.median(observed)
        points.append((item["features"][feature_name], median))
        ratios.extend(value / median for value in observed)
    fit = ({"constant": statistics.median(y for _, y in points)} if feature_name == "constant"
           else log_fit(points))
    loo_errors = []
    for index, (scale, measured) in enumerate(points):
        remaining = points[:index] + points[index + 1:]
        held_fit = ({"constant": statistics.median(y for _, y in remaining)}
                    if feature_name == "constant" else log_fit(remaining))
        loo_errors.append(abs(math.log(estimate(held_fit, scale) / measured)))
    return {
        "feature": feature_name, "fit": fit,
        "training_loo_max_abs_log_error": max(1e-12, max(loo_errors)),
        "training_trial_ratio_p05": quantile(ratios, 0.05),
        "training_trial_ratio_p95": quantile(ratios, 0.95),
        "training_programs": len(records), "training_trials": len(ratios),
    }


def fit_model(corpus: dict, protocol: dict) -> dict:
    records = checked_cases(corpus, "train", protocol)
    model = {
        "schema": "s31-stage-aware-cost-model-v1",
        "protocol_sha256": corpus["protocol_sha256"],
        "training_host": corpus["host"],
        "compiler_sha256": records[0]["case"]["compiler_sha256"],
        "training_source_sha256": sorted(item["source"] for item in records),
        "training_assignment_sha256": sorted(digest for item in records
                                              for digest in item["case"]["assignment_sha256"]),
        "families": {}, "automatic_lowering_selection_enabled": False,
    }
    for family in protocol["profiles"]:
        members = [item for item in records if item["family"] == family]
        stages = (*stages_for_family(family), "proof_bytes", "prover_peak_rss_bytes")
        model["families"][family] = {
            "lowering": members[0]["case"]["lowering"],
            "profile": members[0]["case"]["profile"],
            "visible_fri": members[0]["case"]["visible_fri"],
            "stages": {stage: stage_fit(members, stage, protocol["stage_features"][stage])
                       for stage in stages},
        }
    return model


def stage_prediction(stage_model: dict, features_: dict) -> dict:
    center = estimate(stage_model["fit"], features_[stage_model["feature"]])
    envelope = stage_model["training_loo_max_abs_log_error"]
    return {
        "center": center,
        "lower": center * math.exp(-envelope) * stage_model["training_trial_ratio_p05"],
        "upper": center * math.exp(envelope) * stage_model["training_trial_ratio_p95"],
    }


def predict_case(model_family: dict, family: str, features_: dict) -> dict:
    stages = {name: stage_prediction(stage_model, features_)
              for name, stage_model in model_family["stages"].items()}
    whole = {part: sum(stages[name][part] for name in stages_for_family(family))
             for part in ("center", "lower", "upper")}
    return {"stages": stages,
            "targets": {"paired_prove_and_verify_wall_seconds": whole,
                        "proof_bytes": stages["proof_bytes"],
                        "prover_peak_rss_bytes": stages["prover_peak_rss_bytes"]}}


def actual_target(trial: dict, target: str) -> float:
    if target == "paired_prove_and_verify_wall_seconds":
        return trial["prove_seconds"] + trial["verify_seconds"]
    return positive(trial[target], target)


def evaluate(model: dict, corpus: dict, protocol: dict) -> dict:
    if model.get("schema") != "s31-stage-aware-cost-model-v1":
        raise ValueError("unsupported stage model")
    records = checked_cases(corpus, "validation", protocol)
    if model["protocol_sha256"] != corpus["protocol_sha256"]:
        raise ValueError("model/validation protocol mismatch")
    if model["training_host"] != corpus["host"]:
        raise ValueError("host changed between training and validation")
    if model["compiler_sha256"] != records[0]["case"]["compiler_sha256"]:
        raise ValueError("compiler changed between training and validation")
    train_sources = set(model["training_source_sha256"])
    train_assignments = set(model["training_assignment_sha256"])
    if train_sources.intersection(item["source"] for item in records):
        raise ValueError("training source leaked into validation")
    if train_assignments.intersection(digest for item in records
                                      for digest in item["case"]["assignment_sha256"]):
        raise ValueError("training assignment leaked into validation")
    program_results = []
    for item in records:
        family = item["family"]
        expected_policy = model["families"][family]
        for key in ("lowering", "profile", "visible_fri"):
            if expected_policy[key] != item["case"][key]:
                raise ValueError(f"{family}: profile/FRI policy changed")
        predicted = predict_case(expected_policy, family, item["features"])
        targets = {}
        for target in TARGETS:
            observed = [actual_target(trial, target) for trial in item["case"]["trials"]]
            median = statistics.median(observed)
            interval = predicted["targets"][target]
            targets[target] = {
                "predicted": interval,
                "measured_median": median,
                "measured_p90": quantile(observed, 0.9),
                "absolute_median_error": abs(interval["center"] - median),
                "relative_median_error": abs(interval["center"] - median) / median,
                "covered_trials": sum(interval["lower"] <= value <= interval["upper"]
                                      for value in observed),
                "trial_count": len(observed),
                "median_interval_upper_to_measured_median": interval["upper"] / median,
            }
        stage_errors = {}
        for stage in stages_for_family(family):
            observed = [stage_value(trial, stage) for trial in item["case"]["trials"]]
            median = statistics.median(observed)
            stage_errors[stage] = {
                "measured_median": median,
                "predicted_median": predicted["stages"][stage]["center"],
                "relative_median_error": abs(predicted["stages"][stage]["center"] - median) / median,
            }
        program_results.append({"program": item["name"], "family": family,
                                "source_sha256": item["source"],
                                "features": item["features"],
                                "targets": targets, "stages": stage_errors})
    accuracy = {}
    gates = protocol["accuracy_gate"]
    passed = True
    for family in protocol["profiles"]:
        members = [item for item in program_results if item["family"] == family]
        family_accuracy = {}
        for target in TARGETS:
            observations = [item["targets"][target] for item in members]
            errors = [entry["relative_median_error"] for entry in observations]
            family_accuracy[target] = {
                "programs": len(members),
                "median_program_relative_error": statistics.median(errors),
                "p90_program_relative_error": quantile(errors, 0.9),
                "max_program_relative_error": max(errors),
                "trial_interval_coverage": sum(entry["covered_trials"] for entry in observations) /
                                           sum(entry["trial_count"] for entry in observations),
                "median_interval_upper_to_measured_median": statistics.median(
                    entry["median_interval_upper_to_measured_median"] for entry in observations),
            }
        accuracy[family] = family_accuracy
        if len(members) < gates["minimum_validation_programs_per_family"]:
            passed = False
        wall = family_accuracy["paired_prove_and_verify_wall_seconds"]
        if (wall["p90_program_relative_error"] > gates["per_family_whole_wall_program_median_p90_relative_error_max"] or
            wall["trial_interval_coverage"] < gates["per_family_whole_wall_trial_interval_coverage_min"] or
            wall["median_interval_upper_to_measured_median"] > gates["per_family_whole_wall_median_interval_upper_to_measured_median_max"]):
            passed = False
        for target in ("proof_bytes", "prover_peak_rss_bytes"):
            stat = family_accuracy[target]
            if (stat["p90_program_relative_error"] > gates["per_family_proof_bytes_program_median_p90_relative_error_max"]
                if target == "proof_bytes" else
                stat["p90_program_relative_error"] > gates["per_family_prover_rss_program_median_p90_relative_error_max"]):
                passed = False
            if stat["trial_interval_coverage"] < gates["per_family_proof_bytes_and_rss_trial_interval_coverage_min"]:
                passed = False
    return {
        "schema": "s31-stage-aware-cost-evaluation-v1",
        "protocol_sha256": corpus["protocol_sha256"],
        "compiler_sha256": model["compiler_sha256"],
        "programs": program_results, "accuracy": accuracy,
        "local_accuracy_gate_pass": passed,
        "automatic_lowering_selection_enabled": False,
        "selection_reason": protocol["selection_policy"],
        "interpretation": "This is a one-host, profile-specific prospective check. Intervals are empirical diagnostics, not confidence intervals or tail guarantees.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    fit_parser = commands.add_parser("fit")
    fit_parser.add_argument("corpus", type=Path)
    fit_parser.add_argument("--out", type=Path, required=True)
    eval_parser = commands.add_parser("evaluate")
    eval_parser.add_argument("model", type=Path)
    eval_parser.add_argument("corpus", type=Path)
    eval_parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    protocol = json.loads(PROTOCOL.read_text())
    corpus_bytes = args.corpus.read_bytes()
    corpus = json.loads(corpus_bytes)
    if args.command == "fit":
        result = fit_model(corpus, protocol)
        result["training_corpus_sha256"] = hashlib.sha256(corpus_bytes).hexdigest()
    else:
        model_bytes = args.model.read_bytes()
        result = evaluate(json.loads(model_bytes), corpus, protocol)
        result["frozen_model_sha256"] = hashlib.sha256(model_bytes).hexdigest()
        result["validation_corpus_sha256"] = hashlib.sha256(corpus_bytes).hexdigest()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
