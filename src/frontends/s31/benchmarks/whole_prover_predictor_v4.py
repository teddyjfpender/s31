#!/usr/bin/env python3
"""Predict expected whole-process wall and empirical per-trial intervals."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import statistics
from pathlib import Path

from stage_aware_predictor_v1 import (
    TARGETS, actual_target, estimate, log_fit, quantile, stage_value,
)
from whole_prover_predictor_v3 import (
    checked_cases, fit_affine_rss, fit_stage, predict_stage, stages_for_family,
)

PROTOCOL = Path(__file__).resolve().parents[4] / "design/s31/measurements/whole-prover-cost-v4.json"
CORPUS_SCHEMA = "s31-whole-prover-cost-corpus-v4"
MODEL_SCHEMA = "s31-whole-prover-cost-model-v4"


def records_for(corpus: dict, split: str, protocol: dict) -> list[dict]:
    if not re.fullmatch(r"[0-9a-f]{64}", corpus.get("measurement_tool_sha256", "")):
        raise ValueError("missing pinned measurement tool digest")
    records = checked_cases(corpus, split, protocol, protocol_path=PROTOCOL,
                            corpus_schema=CORPUS_SCHEMA)
    if any(record["case"]["visible_fri"].get("pow_bits") !=
           protocol["pow_bits_required"] for record in records):
        raise ValueError("v4 requires the predeclared PoW bit policy")
    return records


def mean_stage_fit(records: list[dict], stage: str, feature: str) -> dict:
    points = [(record["features"][feature], statistics.mean(
        stage_value(trial, stage) for trial in record["case"]["trials"]))
        for record in records]
    fit = ({"constant": statistics.mean(y for _, y in points)}
           if feature == "constant" else log_fit(points))
    return {"feature": feature, "fit": fit,
            "target": "arithmetic mean of fresh-process stage trials",
            "training_programs": len(points),
            "training_trials": sum(len(record["case"]["trials"]) for record in records)}


def wall_stage_models(records: list[dict], family: str, protocol: dict) -> dict:
    features = (protocol["chip_stage_features"] if family == "chip"
                else protocol["stage_features"])
    return {stage: mean_stage_fit(records, stage, features[stage])
            for stage in stages_for_family(family)}


def wall_center(stages: dict, features: dict) -> float:
    return sum(estimate(stage["fit"], features[stage["feature"]])
               for stage in stages.values())


def wall_interval_calibration(records: list[dict], family: str,
                              protocol: dict) -> dict:
    ratios = []
    errors = []
    per_program = []
    for held in records:
        other = [record for record in records if record is not held]
        stages = wall_stage_models(other, family, protocol)
        center = wall_center(stages, held["features"])
        wall_trials = [actual_target(trial, "paired_prove_and_verify_wall_seconds")
                       for trial in held["case"]["trials"]]
        measured_mean = statistics.mean(wall_trials)
        error = abs(center - measured_mean) / measured_mean
        errors.append(error)
        ratios.extend(value / center for value in wall_trials)
        per_program.append({"name": held["name"], "out_of_fold_center": center,
                            "measured_mean": measured_mean, "relative_mean_error": error})
    return {"method": "leave-one-training-program-out pooled whole-wall trial ratios",
            "ratio_p05": quantile(ratios, .05),
            "ratio_p95": quantile(ratios, .95),
            "out_of_fold_program_mean_p90_relative_error": quantile(errors, .9),
            "out_of_fold_programs": per_program,
            "training_trial_ratios": len(ratios)}


def fit_model(corpus: dict, protocol: dict) -> dict:
    records = records_for(corpus, "train", protocol)
    model = {"schema": MODEL_SCHEMA, "protocol_sha256": corpus["protocol_sha256"],
             "measurement_tool_sha256": corpus["measurement_tool_sha256"],
             "training_host": corpus["host"],
             "compiler_sha256": records[0]["case"]["compiler_sha256"],
             "training_source_sha256": sorted(record["source"] for record in records),
             "training_assignment_sha256": sorted(
                 digest for record in records
                 for digest in record["case"]["assignment_sha256"]),
             "families": {}, "automatic_lowering_selection_enabled": False}
    for family in protocol["profiles"]:
        members = [record for record in records if record["family"] == family]
        features = (protocol["chip_stage_features"] if family == "chip"
                    else protocol["stage_features"])
        model["families"][family] = {
            "lowering": members[0]["case"]["lowering"],
            "profile": members[0]["case"]["profile"],
            "visible_fri": members[0]["case"]["visible_fri"],
            "wall_stages": wall_stage_models(members, family, protocol),
            "wall_interval": wall_interval_calibration(members, family, protocol),
            "proof_bytes": fit_stage(members, "proof_bytes", features["proof_bytes"]),
            "prover_peak_rss_bytes": (
                fit_affine_rss(members, features["prover_peak_rss_bytes"])
                if family in {"arithmetic", "chip"} else
                fit_stage(members, "prover_peak_rss_bytes",
                          features["prover_peak_rss_bytes"])),
        }
    return model


def evaluate(model: dict, corpus: dict, protocol: dict) -> dict:
    if model.get("schema") != MODEL_SCHEMA:
        raise ValueError("wrong frozen v4 model")
    records = records_for(corpus, "validation", protocol)
    if (model["protocol_sha256"] != corpus["protocol_sha256"] or
        model["measurement_tool_sha256"] != corpus["measurement_tool_sha256"] or
        model["training_host"] != corpus["host"] or
        model["compiler_sha256"] != records[0]["case"]["compiler_sha256"]):
        raise ValueError("protocol/tool/host/compiler changed across splits")
    if set(model["training_source_sha256"]) & {record["source"] for record in records}:
        raise ValueError("training source leaked into validation")
    if set(model["training_assignment_sha256"]) & {
            digest for record in records for digest in record["case"]["assignment_sha256"]}:
        raise ValueError("training assignment leaked into validation")
    results = []
    for record in records:
        family = record["family"]
        policy = model["families"][family]
        if any(policy[key] != record["case"][key]
               for key in ("lowering", "profile", "visible_fri")):
            raise ValueError(f"{family}: profile/FRI changed across splits")
        center = wall_center(policy["wall_stages"], record["features"])
        interval = policy["wall_interval"]
        predictions = {
            "paired_prove_and_verify_wall_seconds": {
                "center": center, "lower": center * interval["ratio_p05"],
                "upper": center * interval["ratio_p95"]},
            "proof_bytes": predict_stage(policy["proof_bytes"], record["features"]),
            "prover_peak_rss_bytes": predict_stage(
                policy["prover_peak_rss_bytes"], record["features"]),
        }
        targets = {}
        for target in TARGETS:
            values = [actual_target(trial, target) for trial in record["case"]["trials"]]
            point = (statistics.mean(values) if target ==
                     "paired_prove_and_verify_wall_seconds" else statistics.median(values))
            prediction = predictions[target]
            targets[target] = {
                "predicted": prediction, "measured_point": point,
                "point_statistic": "mean" if target ==
                                   "paired_prove_and_verify_wall_seconds" else "median",
                "measured_p90": quantile(values, .9),
                "relative_point_error": abs(prediction["center"] - point) / point,
                "covered_trials": sum(prediction["lower"] <= value <= prediction["upper"]
                                      for value in values),
                "trial_count": len(values),
                "interval_upper_to_measured_point": prediction["upper"] / point,
            }
        stages = {}
        for stage in stages_for_family(family):
            values = [stage_value(trial, stage) for trial in record["case"]["trials"]]
            predicted = estimate(policy["wall_stages"][stage]["fit"],
                                 record["features"][policy["wall_stages"][stage]["feature"]])
            observed = statistics.mean(values)
            stages[stage] = {"measured_mean": observed,
                             "measured_median": statistics.median(values),
                             "measured_p90": quantile(values, .9),
                             "coefficient_of_variation": statistics.pstdev(values) / observed,
                             "predicted_mean": predicted,
                             "relative_mean_error": abs(predicted - observed) / observed}
        results.append({"program": record["name"], "family": family,
                        "source_sha256": record["source"],
                        "features": record["features"], "targets": targets,
                        "stages": stages})
    gates = protocol["accuracy_gate"]
    accuracy = {}
    passed = True
    for family in protocol["profiles"]:
        members = [result for result in results if result["family"] == family]
        family_accuracy = {}
        for target in TARGETS:
            entries = [member["targets"][target] for member in members]
            errors = [entry["relative_point_error"] for entry in entries]
            family_accuracy[target] = {
                "programs": len(members),
                "median_program_relative_error": statistics.median(errors),
                "p90_program_relative_error": quantile(errors, .9),
                "max_program_relative_error": max(errors),
                "trial_interval_coverage": sum(entry["covered_trials"] for entry in entries) /
                                           sum(entry["trial_count"] for entry in entries),
                "median_interval_upper_to_measured_point": statistics.median(
                    entry["interval_upper_to_measured_point"] for entry in entries),
            }
        accuracy[family] = family_accuracy
        if (len(members) < gates["minimum_validation_programs_per_family"] or
            any(entry["targets"]["proof_bytes"]["trial_count"] <
                gates["minimum_validation_trials_per_program"] for entry in members)):
            passed = False
        wall = family_accuracy["paired_prove_and_verify_wall_seconds"]
        if (wall["p90_program_relative_error"] >
            gates["per_family_whole_wall_program_mean_p90_relative_error_max"] or
            wall["trial_interval_coverage"] <
            gates["per_family_whole_wall_trial_interval_coverage_min"] or
            wall["median_interval_upper_to_measured_point"] >
            gates["per_family_whole_wall_median_interval_upper_to_measured_mean_max"]):
            passed = False
        for target, limit in (
            ("proof_bytes", gates["per_family_proof_bytes_program_median_p90_relative_error_max"]),
            ("prover_peak_rss_bytes", gates["per_family_prover_rss_program_median_p90_relative_error_max"]),
        ):
            stat = family_accuracy[target]
            if (stat["p90_program_relative_error"] > limit or
                stat["trial_interval_coverage"] <
                gates["per_family_proof_bytes_and_rss_trial_interval_coverage_min"]):
                passed = False
    return {"schema": "s31-whole-prover-cost-evaluation-v4",
            "protocol_sha256": corpus["protocol_sha256"],
            "compiler_sha256": model["compiler_sha256"],
            "programs": results, "accuracy": accuracy,
            "local_accuracy_gate_pass": passed,
            "automatic_lowering_selection_enabled": False,
            "selection_reason": protocol["selection_policy"],
            "interpretation": "One-host same-compiler prospective check; expected-wall point is a sample mean, and empirical trial intervals have no guaranteed tail coverage."}


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
        if corpus.get("frozen_model_sha256") != hashlib.sha256(model_bytes).hexdigest():
            raise ValueError("held-out timings were not collected against this frozen model")
        result = evaluate(json.loads(model_bytes), corpus, protocol)
        result["frozen_model_sha256"] = hashlib.sha256(model_bytes).hexdigest()
        result["validation_corpus_sha256"] = hashlib.sha256(corpus_bytes).hexdigest()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
