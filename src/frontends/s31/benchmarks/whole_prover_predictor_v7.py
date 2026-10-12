#!/usr/bin/env python3
"""Fit V7 on training only; evaluate pinned held-out process and native stages."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
import statistics
import sys
from pathlib import Path

from stage_aware_predictor_v1 import (
    TARGETS, actual_target, estimate, log_fit, quantile, stage_value,
)
from arithmetic_rss_predictor_v2 import affine_fit, affine_predict
from whole_prover_predictor_v3 import (
    checked_cases, fit_stage, predict_stage, stages_for_family,
)

sys.path.insert(0, str(Path(__file__).resolve().parent / "cost"))
from v7_protocol import (MODEL, PROTOCOL, check_corpus_cost_geometry,
                         require_model, require_protocol)

CORPUS_SCHEMA = "s31-whole-prover-cost-corpus-v7"
MODEL_SCHEMA = "s31-whole-prover-cost-model-v7"


def records_for(corpus: dict, split: str, protocol: dict) -> list[dict]:
    if not re.fullmatch(r"[0-9a-f]{64}", corpus.get("measurement_tool_sha256", "")):
        raise ValueError("missing pinned measurement tool digest")
    records = checked_cases(corpus, split, protocol, protocol_path=PROTOCOL,
                            corpus_schema=CORPUS_SCHEMA)
    if any(record["case"]["visible_fri"].get("pow_bits") !=
           protocol["pow_bits_required"] for record in records):
        raise ValueError("V7 requires the predeclared PoW bit policy")
    for record in records:
        item = protocol["inventory"][split][record["name"]]
        if (record["source"] != item["source_sha256"] or
            record["case"]["assignment_sha256"] != item["assignment_sha256"] or
            record["family"] != item["family"] or
            record["case"]["lowering"] != item["lowering"] or
            record["case"]["profile"] != protocol["profile_by_family"][record["family"]] or
            record["case"]["visible_fri"] != protocol["visible_fri"]):
            raise ValueError(f"{record['name']}: corpus differs from frozen workload inventory")
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


def rss_point_fit(records: list[dict], feature: str, family: str) -> dict:
    points = [(record["features"][feature], statistics.median(
        trial["prover_peak_rss_bytes"] for trial in record["case"]["trials"]))
        for record in records]
    if family in {"arithmetic", "chip"}:
        return {"fit_kind": "positive_affine_rss", "fit": affine_fit(points)}
    return {"fit_kind": "log_linear_rss", "fit": log_fit(points)}


def rss_point(fit: dict, feature_value: float) -> float:
    return (affine_predict(fit["fit"], feature_value)
            if fit["fit_kind"] == "positive_affine_rss"
            else estimate(fit["fit"], feature_value))


def fit_rss_interval(records: list[dict], feature: str, family: str) -> dict:
    """Calibrate absolute and, for chips, relative RSS envelopes on train only."""
    full_fit = rss_point_fit(records, feature, family)
    per_program = []
    for held in records:
        other = [record for record in records if record is not held]
        predicted = rss_point(rss_point_fit(other, feature, family),
                              held["features"][feature])
        if not math.isfinite(predicted) or predicted <= 0:
            raise ValueError("out-of-fold RSS center must be positive")
        residuals = [trial["prover_peak_rss_bytes"] - predicted
                     for trial in held["case"]["trials"]]
        low, high = quantile(residuals, .05), quantile(residuals, .95)
        absolute_radius = max(abs(low), abs(high))
        per_program.append({"name": held["name"],
                            "out_of_fold_center_bytes": predicted,
                            "measured_median_bytes": statistics.median(
                                trial["prover_peak_rss_bytes"]
                                for trial in held["case"]["trials"]),
                            "residual_p05_bytes": low,
                            "residual_p95_bytes": high,
                            "absolute_byte_radius": absolute_radius,
                            "relative_radius": absolute_radius / predicted})
    radius = max(item["absolute_byte_radius"] for item in per_program)
    relative_radius = (max(item["relative_radius"] for item in per_program)
                       if family == "chip" else 0.0)
    return {"feature": feature, **full_fit,
            "interval_kind": (
                "symmetric_max_absolute_relative_training_loo_envelopes"
                if family == "chip" else
                "symmetric_absolute_byte_loo_program_envelope"),
            "radius_bytes": radius,
            "relative_radius": relative_radius,
            "calibration": per_program,
            "training_programs": len(records),
            "training_trials": sum(len(record["case"]["trials"]) for record in records)}


def predict_rss_interval(model: dict, features: dict) -> dict:
    center = rss_point(model, features[model["feature"]])
    if not math.isfinite(center) or center <= 0:
        raise ValueError("predicted RSS center must be positive")
    radius = max(model["radius_bytes"], model["relative_radius"] * center)
    return {"center": center, "lower": max(0.0, center - radius),
            "upper": center + radius}


def rss_program_gate(entries: list[dict], gates: dict) -> bool:
    return all(
        entry["covered_trials"] / entry["trial_count"] >=
        gates["per_program_rss_trial_interval_coverage_min"] and
        entry["interval_upper_to_measured_point"] <=
        gates["per_program_rss_interval_upper_to_measured_median_max"]
        for entry in entries
    )


def process_stage_gate(stages: dict, gates: dict) -> bool:
    """Each program must explain its OS-process overhead, not only total wall."""
    return all(
        stages[stage]["relative_mean_error"] <=
        gates["per_program_process_stage_mean_relative_error_max"] or
        stages[stage]["absolute_mean_error_seconds"] <=
        gates["per_program_process_stage_mean_absolute_error_seconds_max"]
        for stage in ("prover_process_unattributed_seconds",
                      "native_verify_process_wall_seconds")
    )


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
            "prover_peak_rss_bytes": fit_rss_interval(
                members, features["prover_peak_rss_bytes"], family),
        }
    return model


def evaluate(model: dict, corpus: dict, protocol: dict) -> dict:
    if model.get("schema") != MODEL_SCHEMA:
        raise ValueError("wrong frozen V7 model")
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
    gates = protocol["accuracy_gate"]
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
            "prover_peak_rss_bytes": predict_rss_interval(
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
                             "absolute_mean_error_seconds": abs(predicted - observed),
                             "relative_mean_error": abs(predicted - observed) / observed}
        process_gate = process_stage_gate(stages, gates)
        results.append({"program": record["name"], "family": family,
                        "source_sha256": record["source"],
                        "features": record["features"], "targets": targets,
                        "stages": stages, "process_stage_gate_pass": process_gate})
    accuracy = {}
    passed = all(result["process_stage_gate_pass"] for result in results)
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
        if not rss_program_gate(
            [member["targets"]["prover_peak_rss_bytes"] for member in members], gates
        ):
            passed = False
    return {"schema": "s31-whole-prover-cost-evaluation-v7",
            "protocol_sha256": corpus["protocol_sha256"],
            "compiler_sha256": model["compiler_sha256"],
            "programs": results, "accuracy": accuracy,
            "local_accuracy_gate_pass": passed,
            "automatic_lowering_selection_enabled": False,
            "selection_reason": protocol["selection_policy"],
            "interpretation": "One-host same-compiler prospective check; expected-wall point is a sample mean, and empirical trial intervals have no guaranteed tail coverage."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-protocol-sha256", required=True)
    parser.add_argument("--protocol-anchor-commit", required=True)
    parser.add_argument("--expected-model-sha256")
    parser.add_argument("--model-anchor-commit")
    commands = parser.add_subparsers(dest="command", required=True)
    fit_parser = commands.add_parser("fit")
    fit_parser.add_argument("corpus", type=Path)
    fit_parser.add_argument("--out", type=Path, required=True)
    eval_parser = commands.add_parser("evaluate")
    eval_parser.add_argument("model", type=Path)
    eval_parser.add_argument("corpus", type=Path)
    eval_parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    protocol = require_protocol(args.expected_protocol_sha256,
                                args.protocol_anchor_commit)
    corpus_bytes = args.corpus.read_bytes()
    corpus = json.loads(corpus_bytes)
    check_corpus_cost_geometry(args.corpus, corpus, protocol)
    if args.command == "fit":
        if args.expected_model_sha256 is not None or args.model_anchor_commit is not None:
            raise ValueError("training fit cannot consume held-out model anchor")
        if args.out.resolve() != MODEL.resolve():
            raise ValueError("V7 training fit must write the canonical model artifact")
        result = fit_model(corpus, protocol)
        result["training_corpus_sha256"] = hashlib.sha256(corpus_bytes).hexdigest()
    else:
        if args.expected_model_sha256 is None or args.model_anchor_commit is None:
            raise ValueError("held-out evaluation requires committed model anchor")
        require_model(args.model, args.expected_model_sha256,
                      args.model_anchor_commit, args.expected_protocol_sha256,
                      args.protocol_anchor_commit)
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
