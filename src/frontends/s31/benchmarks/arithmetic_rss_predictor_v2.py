#!/usr/bin/env python3
"""Fit and prospectively evaluate the pinned arithmetic RSS affine hypothesis."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
from pathlib import Path

from stage_aware_predictor_v1 import changed_claim_field, log_fit, quantile

PROTOCOL = Path(__file__).resolve().parents[4] / "design/s31/measurements/arithmetic-rss-v2.json"


def expected_names(split: str, protocol: dict) -> set[str]:
    if split == "train":
        return {f"arith_rss_train_{rounds}" for rounds in protocol["train"]["rounds"]}
    return {f"arith_rss_{body}_{rounds}"
            for body in protocol["validation"]["bodies"]
            for rounds in protocol["validation"]["rounds"]}


def checked_cases(corpus: dict, split: str, protocol: dict) -> list[dict]:
    if corpus.get("schema") != "s31-arithmetic-rss-corpus-v2" or corpus.get("split") != split:
        raise ValueError(f"expected {split} arithmetic RSS corpus")
    if corpus.get("protocol_sha256") != hashlib.sha256(PROTOCOL.read_bytes()).hexdigest():
        raise ValueError("corpus/protocol mismatch")
    cases = corpus.get("cases")
    if not isinstance(cases, dict) or set(cases) != expected_names(split, protocol):
        raise ValueError("wrong prospective program set")
    if corpus.get("samples_per_program") != protocol["samples_per_program"]:
        raise ValueError("wrong prospective trial count")
    records = []
    source_set: set[str] = set()
    assignment_set: set[str] = set()
    for name, case in sorted(cases.items()):
        source = case["source_sha256"]
        if not isinstance(source, str) or len(source) != 64 or source in source_set:
            raise ValueError(f"{name}: source digest invalid or duplicated")
        source_set.add(source)
        if case["compiler_sha256"] != corpus["compiler_sha256"] or case["lowering"] != "direct-gate":
            raise ValueError(f"{name}: compiler/lowering mismatch")
        build = case["package_build"]
        if not isinstance(build["package_reused"], bool) or build["package_build_wall_seconds"] <= 0:
            raise ValueError(f"{name}: invalid package-build measurement")
        padded = case["padded"]
        if not isinstance(padded, dict) or not padded:
            raise ValueError(f"{name}: missing padded rows")
        rows = sum(padded.values())
        if isinstance(rows, bool) or not isinstance(rows, int) or rows <= 0 or any(
                isinstance(value, bool) or not isinstance(value, int) or value < 0
                for value in padded.values()):
            raise ValueError(f"{name}: invalid padded rows")
        trials = case["trials"]
        digests = case["assignment_sha256"]
        if len(trials) != protocol["samples_per_program"] or len(digests) != len(trials):
            raise ValueError(f"{name}: wrong trial count")
        rss = []
        for trial, digest in zip(trials, digests):
            if not isinstance(digest, str) or len(digest) != 64 or digest in assignment_set:
                raise ValueError(f"{name}: assignment digest invalid or duplicated")
            assignment_set.add(digest)
            if trial["native_verifier_accepted"] is not True or trial["independent_value_oracle"]["status"] != "passed":
                raise ValueError(f"{name}: proof/oracle control failed")
            changed_claim_field(trial["changed_public_statement_rejected"])
            value = trial["prover_peak_rss_bytes"]
            if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
                raise ValueError(f"{name}: peak RSS unavailable")
            rss.append(value)
        records.append({"name": name, "source_sha256": source,
                        "rows": rows, "rss": rss, "case": case})
    for key in ("compiler_sha256", "profile", "visible_fri"):
        if len({json.dumps(record["case"][key], sort_keys=True) for record in records}) != 1:
            raise ValueError(f"mixed {key} in {split}")
    return records


def affine_fit(points: list[tuple[float, float]]) -> dict:
    if len(points) < 2:
        raise ValueError("affine fit needs two programs")
    xs = [x for x, _ in points]
    ys = [y for _, y in points]
    mean_x, mean_y = statistics.mean(xs), statistics.mean(ys)
    denominator = sum((x - mean_x) ** 2 for x in xs)
    if denominator <= 0:
        raise ValueError("affine fit needs distinct padded tiers")
    slope = sum((x - mean_x) * (y - mean_y) for x, y in points) / denominator
    intercept = mean_y - slope * mean_x
    if intercept < 0 or slope < 0:
        raise ValueError("predeclared positive affine RSS hypothesis did not fit training data")
    return {"intercept_bytes": intercept, "bytes_per_padded_row": slope}


def affine_predict(fit: dict, rows: float) -> float:
    return fit["intercept_bytes"] + fit["bytes_per_padded_row"] * rows


def log_predict(fit: dict, rows: float) -> float:
    return math.exp(fit["intercept"] + fit["slope"] * math.log(rows))


def fit_model(corpus: dict, protocol: dict) -> dict:
    records = checked_cases(corpus, "train", protocol)
    points = [(record["rows"], statistics.median(record["rss"])) for record in records]
    candidate = affine_fit(points)
    reference = log_fit(points)
    loo = []
    residuals = []
    for index, record in enumerate(records):
        other = points[:index] + points[index + 1:]
        scale, measured = points[index]
        loo.append(abs(affine_predict(affine_fit(other), scale) - measured))
        residuals.extend(value - measured for value in record["rss"])
    return {
        "schema": "s31-arithmetic-rss-model-v2",
        "protocol_sha256": corpus["protocol_sha256"],
        "host": corpus["host"], "compiler_sha256": corpus["compiler_sha256"],
        "profile": records[0]["case"]["profile"],
        "visible_fri": records[0]["case"]["visible_fri"],
        "training_source_sha256": sorted(record["source_sha256"] for record in records),
        "training_assignment_sha256": sorted(digest for record in records
                                               for digest in record["case"]["assignment_sha256"]),
        "candidate_positive_affine": candidate,
        "reference_log_line": reference,
        "max_training_loo_absolute_error_bytes": max(loo),
        "training_trial_residual_p05_bytes": quantile(residuals, 0.05),
        "training_trial_residual_p95_bytes": quantile(residuals, 0.95),
        "training_loo_relative_errors": [error / point[1] for error, point in zip(loo, points)],
        "automatic_lowering_selection_enabled": False,
    }


def evaluate(model: dict, corpus: dict, protocol: dict) -> dict:
    if model.get("schema") != "s31-arithmetic-rss-model-v2":
        raise ValueError("wrong frozen arithmetic RSS model")
    records = checked_cases(corpus, "validation", protocol)
    if (model["protocol_sha256"] != corpus["protocol_sha256"] or
        model["host"] != corpus["host"] or
        model["compiler_sha256"] != corpus["compiler_sha256"]):
        raise ValueError("protocol/host/compiler changed between train and validation")
    if model["profile"] != records[0]["case"]["profile"] or model["visible_fri"] != records[0]["case"]["visible_fri"]:
        raise ValueError("proof profile or FRI policy changed")
    train_sources = set(model["training_source_sha256"])
    train_assignments = set(model["training_assignment_sha256"])
    if train_sources.intersection(record["source_sha256"] for record in records):
        raise ValueError("training source leaked into held-out split")
    if train_assignments.intersection(digest for record in records
                                      for digest in record["case"]["assignment_sha256"]):
        raise ValueError("training assignment leaked into held-out split")
    program_results = []
    for record in records:
        measured = statistics.median(record["rss"])
        center = affine_predict(model["candidate_positive_affine"], record["rows"])
        envelope = model["max_training_loo_absolute_error_bytes"]
        lower = max(0.0, center - envelope + model["training_trial_residual_p05_bytes"])
        upper = center + envelope + model["training_trial_residual_p95_bytes"]
        baseline = log_predict(model["reference_log_line"], record["rows"])
        program_results.append({
            "program": record["name"], "body": record["name"].split("_")[-2],
            "source_sha256": record["source_sha256"], "padded_rows": record["rows"],
            "measured_median_rss_bytes": measured,
            "candidate": {"predicted_median_bytes": center,
                          "absolute_error_bytes": abs(center - measured),
                          "relative_error": abs(center - measured) / measured,
                          "interval_lower_bytes": lower, "interval_upper_bytes": upper,
                          "covered_trials": sum(lower <= value <= upper for value in record["rss"]),
                          "trial_count": len(record["rss"]),
                          "interval_upper_to_measured_median": upper / measured},
            "reference_log_line": {"predicted_median_bytes": baseline,
                                   "relative_error": abs(baseline - measured) / measured},
        })
    def aggregate(items: list[dict]) -> dict:
        errors = [item["candidate"]["relative_error"] for item in items]
        return {
            "programs": len(items), "median_relative_error": statistics.median(errors),
            "p90_relative_error": quantile(errors, 0.9), "max_relative_error": max(errors),
            "trial_interval_coverage": sum(item["candidate"]["covered_trials"] for item in items) /
                                       sum(item["candidate"]["trial_count"] for item in items),
            "median_interval_upper_to_measured_median": statistics.median(
                item["candidate"]["interval_upper_to_measured_median"] for item in items),
            "reference_log_line_p90_relative_error": quantile(
                [item["reference_log_line"]["relative_error"] for item in items], 0.9),
        }
    accuracy = {"overall": aggregate(program_results)}
    for body in protocol["validation"]["bodies"]:
        accuracy[body] = aggregate([item for item in program_results if item["body"] == body])
    gate = protocol["accuracy_gate"]
    local_pass = (
        len(program_results) == gate["validation_programs"] and
        all(item["candidate"]["trial_count"] == gate["trials_per_program"] for item in program_results) and
        accuracy["overall"]["p90_relative_error"] <= gate["overall_program_median_p90_relative_error_max"] and
        accuracy["overall"]["max_relative_error"] <= gate["overall_program_median_max_relative_error_max"] and
        all(accuracy[body]["p90_relative_error"] <= gate["each_body_program_median_p90_relative_error_max"] and
            accuracy[body]["trial_interval_coverage"] >= gate["each_body_trial_interval_coverage_min"] and
            accuracy[body]["median_interval_upper_to_measured_median"] <= gate["each_body_median_interval_upper_to_measured_median_max"]
            for body in protocol["validation"]["bodies"])
    )
    return {
        "schema": "s31-arithmetic-rss-evaluation-v2",
        "protocol_sha256": corpus["protocol_sha256"],
        "compiler_sha256": model["compiler_sha256"],
        "programs": program_results, "accuracy": accuracy,
        "targeted_rss_accuracy_gate_pass": local_pass,
        "automatic_lowering_selection_enabled": False,
        "limitations": protocol["selection_policy"],
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
