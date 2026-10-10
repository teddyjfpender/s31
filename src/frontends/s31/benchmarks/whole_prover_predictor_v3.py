#!/usr/bin/env python3
"""Fit and evaluate the frozen four-profile whole-prover cost experiment."""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import statistics
from pathlib import Path

from arithmetic_rss_predictor_v2 import affine_fit, affine_predict
from stage_aware_predictor_v1 import (
    DIRECT_STAGES, OPAQUE_STAGES, TARGETS, actual_target, changed_claim_field,
    features, positive, quantile, stage_fit, stage_value,
)

PROTOCOL = Path(__file__).resolve().parents[4] / "design/s31/measurements/whole-prover-cost-v3.json"
STOCHASTIC_STAGES = {
    "runtime_interaction_pow_seconds", "runtime_fri_pow_seconds",
    "runtime_prove_seconds_when_pow_opaque",
}


def expected_names(split: str, protocol: dict) -> set[str]:
    spec = protocol["splits"][split]
    return ({f"arithmetic_{rounds}" for rounds in spec["arithmetic_rounds"]} |
            {f"chip_{rounds}" for rounds in spec["chip_rounds"]} |
            {f"hash_{depth}" for depth in spec["hash_depths"]} |
            {f"signed_{'quotient' if split == 'validation' else 'div_rem'}_{width}"
             for width in spec["signed_widths"]})


def stages_for_family(family: str) -> tuple[str, ...]:
    return OPAQUE_STAGES if family == "hash" else DIRECT_STAGES


def case_features(case: dict) -> dict[str, float]:
    result = features(case)
    if case["family"] != "chip":
        return result
    binding = case["chip_manifest_binding"]
    geometry = binding.get("component_geometry")
    if (not isinstance(geometry, list) or
        [item.get("name") for item in geometry] != ["qm31_ops", "repeated_step_chip"]):
        raise ValueError("invalid generated chip geometry")
    rows = []
    cells = 0
    for item in geometry:
        log_size = item.get("trace_log_size")
        base = item.get("base_trace_columns")
        interaction = item.get("interaction_trace_columns")
        if (type(log_size) is not int or not 0 <= log_size <= 24 or
            type(base) is not int or base <= 0 or
            type(interaction) is not int or interaction <= 0):
            raise ValueError("invalid generated chip trace dimensions")
        row_count = 1 << log_size
        rows.append(row_count)
        cells += row_count * (base + interaction)
    if (binding.get("chip_trace_cells") != cells or
        binding.get("chip_fri_domain_rows") != max(rows) or
        binding["chip_call"].get("rounds") != rows[1]):
        raise ValueError("chip geometry does not match generated manifest summary")
    result["chip_trace_cells"] = float(cells)
    result["chip_fri_domain_rows"] = float(max(rows))
    return result


def checked_cases(corpus: dict, split: str, protocol: dict, *,
                  protocol_path: Path = PROTOCOL,
                  corpus_schema: str = "s31-whole-prover-cost-corpus-v3.1") -> list[dict]:
    if corpus.get("schema") != corpus_schema or corpus.get("split") != split:
        raise ValueError(f"expected {split} whole-prover v3 corpus")
    if corpus.get("protocol_sha256") != hashlib.sha256(protocol_path.read_bytes()).hexdigest():
        raise ValueError("corpus/protocol mismatch")
    if corpus.get("samples_per_program") != protocol["samples_per_program"]:
        raise ValueError("wrong prospective trial count")
    cases = corpus.get("cases")
    if not isinstance(cases, dict) or set(cases) != expected_names(split, protocol):
        raise ValueError("wrong prospective program set")
    records = []
    sources: set[str] = set()
    assignments: set[str] = set()
    for name, case in sorted(cases.items()):
        family = case["family"]
        if family not in protocol["profiles"] or case["lowering"] != protocol["profiles"][family]:
            raise ValueError(f"{name}: wrong family/lowering")
        if case["compiler_sha256"] != corpus.get("compiler_sha256", case["compiler_sha256"]):
            raise ValueError(f"{name}: mixed compiler fingerprint")
        source = case["source_sha256"]
        if not isinstance(source, str) or len(source) != 64 or source in sources:
            raise ValueError(f"{name}: duplicate or invalid source digest")
        sources.add(source)
        binding = case.get("chip_manifest_binding")
        if family == "chip":
            if (not isinstance(binding, dict) or
                binding.get("schema") != "s31-component-manifest-direct-chip-v2" or
                binding.get("chip_call", {}).get("call_id") != 0 or
                any(not isinstance(binding.get(key), str) or len(binding[key]) != 64
                    for key in ("manifest_precommitment_sha256", "component_manifest_sha256"))):
                raise ValueError(f"{name}: missing generated one-call chip manifest binding")
        elif binding is not None:
            raise ValueError(f"{name}: non-chip case has chip binding")
        package_build = case["package_build"]
        positive(package_build["package_build_wall_seconds"], "package build wall")
        if package_build["package_reused"] is not False:
            raise ValueError(f"{name}: package was not freshly built")
        trials = case["trials"]
        digests = case["assignment_sha256"]
        if len(trials) != protocol["samples_per_program"] or len(digests) != len(trials):
            raise ValueError(f"{name}: wrong trial count")
        for digest, trial in zip(digests, trials):
            if not isinstance(digest, str) or len(digest) != 64 or digest in assignments:
                raise ValueError(f"{name}: duplicate or invalid assignment digest")
            assignments.add(digest)
            if trial["native_verifier_accepted"] is not True:
                raise ValueError(f"{name}: native proof failed")
            changed_claim_field(trial["changed_public_statement_rejected"])
            if trial["independent_value_oracle"]["status"] != "passed":
                raise ValueError(f"{name}: independent oracle failed")
            for stage in (*stages_for_family(family), "proof_bytes", "prover_peak_rss_bytes"):
                stage_value(trial, stage)
        records.append({"name": name, "family": family, "source": source,
                        "features": case_features(case), "case": case})
    if len({record["case"]["compiler_sha256"] for record in records}) != 1:
        raise ValueError("mixed compiler fingerprint across families")
    for family in protocol["profiles"]:
        members = [record["case"] for record in records if record["family"] == family]
        if len(members) < protocol["accuracy_gate"]["minimum_train_programs_per_family"]:
            raise ValueError(f"{family}: too few programs")
        for key in ("lowering", "profile", "visible_fri"):
            if len({json.dumps(case[key], sort_keys=True) for case in members}) != 1:
                raise ValueError(f"{family}: mixed {key}")
    return records


def fit_stage(records: list[dict], stage: str, feature_name: str) -> dict:
    result = stage_fit(records, stage, feature_name)
    if stage in STOCHASTIC_STAGES:
        ratios = []
        for record in records:
            values = [stage_value(trial, stage) for trial in record["case"]["trials"]]
            median = statistics.median(values)
            ratios.extend(value / median for value in values)
        result["stochastic_trial_ratio_min"] = min(ratios)
        result["stochastic_trial_ratio_max"] = max(ratios)
        result["stochastic_variance_policy"] = "full training trial ratio range"
    return result


def fit_affine_rss(records: list[dict], feature_name: str) -> dict:
    points = [(record["features"][feature_name], statistics.median(
        trial["prover_peak_rss_bytes"] for trial in record["case"]["trials"]))
        for record in records]
    fit = affine_fit(points)
    loo = []
    residuals = []
    for index, record in enumerate(records):
        rows, median = points[index]
        loo.append(abs(affine_predict(affine_fit(points[:index] + points[index + 1:]), rows) - median))
        residuals.extend(trial["prover_peak_rss_bytes"] - median
                         for trial in record["case"]["trials"])
    return {"feature": feature_name, "fit_kind": "positive_affine_rss",
            "fit": fit, "training_loo_max_absolute_error_bytes": max(loo),
            "training_trial_residual_p05_bytes": quantile(residuals, 0.05),
            "training_trial_residual_p95_bytes": quantile(residuals, 0.95),
            "training_programs": len(records), "training_trials": len(residuals)}


def fit_model(corpus: dict, protocol: dict) -> dict:
    records = checked_cases(corpus, "train", protocol)
    model = {
        "schema": "s31-whole-prover-cost-model-v3.1",
        "protocol_sha256": corpus["protocol_sha256"],
        "training_host": corpus["host"],
        "compiler_sha256": records[0]["case"]["compiler_sha256"],
        "training_source_sha256": sorted(record["source"] for record in records),
        "training_assignment_sha256": sorted(digest for record in records
                                              for digest in record["case"]["assignment_sha256"]),
        "families": {}, "automatic_lowering_selection_enabled": False,
    }
    for family in protocol["profiles"]:
        members = [record for record in records if record["family"] == family]
        stages = (*stages_for_family(family), "proof_bytes", "prover_peak_rss_bytes")
        stage_features = (protocol["chip_stage_features"] if family == "chip"
                          else protocol["stage_features"])
        model["families"][family] = {
            "lowering": members[0]["case"]["lowering"],
            "profile": members[0]["case"]["profile"],
            "visible_fri": members[0]["case"]["visible_fri"],
            "stages": {stage: (fit_affine_rss(members, stage_features[stage])
                               if family in {"arithmetic", "chip"} and
                               stage == "prover_peak_rss_bytes" else
                               fit_stage(members, stage, stage_features[stage]))
                       for stage in stages},
        }
    return model


def predict_stage(stage_model: dict, case_features: dict) -> dict:
    x = case_features[stage_model["feature"]]
    if stage_model.get("fit_kind") == "positive_affine_rss":
        center = affine_predict(stage_model["fit"], x)
        error = stage_model["training_loo_max_absolute_error_bytes"]
        return {"center": center,
                "lower": max(0.0, center - error + stage_model["training_trial_residual_p05_bytes"]),
                "upper": center + error + stage_model["training_trial_residual_p95_bytes"]}
    fit = stage_model["fit"]
    center = fit["constant"] if "constant" in fit else math.exp(
        fit["intercept"] + fit["slope"] * math.log(x))
    envelope = stage_model["training_loo_max_abs_log_error"]
    low_ratio = stage_model.get("stochastic_trial_ratio_min", stage_model["training_trial_ratio_p05"])
    high_ratio = stage_model.get("stochastic_trial_ratio_max", stage_model["training_trial_ratio_p95"])
    return {"center": center, "lower": center * math.exp(-envelope) * low_ratio,
            "upper": center * math.exp(envelope) * high_ratio}


def predict_case(model_family: dict, family: str, case_features: dict) -> dict:
    stages = {stage: predict_stage(stage_model, case_features)
              for stage, stage_model in model_family["stages"].items()}
    whole = {part: sum(stages[stage][part] for stage in stages_for_family(family))
             for part in ("center", "lower", "upper")}
    return {"stages": stages, "targets": {
        "paired_prove_and_verify_wall_seconds": whole,
        "proof_bytes": stages["proof_bytes"],
        "prover_peak_rss_bytes": stages["prover_peak_rss_bytes"],
    }}


def evaluate(model: dict, corpus: dict, protocol: dict) -> dict:
    if model.get("schema") != "s31-whole-prover-cost-model-v3.1":
        raise ValueError("wrong frozen v3 model")
    records = checked_cases(corpus, "validation", protocol)
    if (model["protocol_sha256"] != corpus["protocol_sha256"] or
        model["training_host"] != corpus["host"] or
        model["compiler_sha256"] != records[0]["case"]["compiler_sha256"]):
        raise ValueError("protocol/host/compiler changed across splits")
    if set(model["training_source_sha256"]) & {record["source"] for record in records}:
        raise ValueError("training source leaked into validation")
    if set(model["training_assignment_sha256"]) & {
            digest for record in records for digest in record["case"]["assignment_sha256"]}:
        raise ValueError("training assignment leaked into validation")
    program_results = []
    for record in records:
        family = record["family"]
        policy = model["families"][family]
        if any(policy[key] != record["case"][key] for key in ("lowering", "profile", "visible_fri")):
            raise ValueError(f"{family}: profile/FRI changed across splits")
        predicted = predict_case(policy, family, record["features"])
        targets = {}
        for target in TARGETS:
            values = [actual_target(trial, target) for trial in record["case"]["trials"]]
            median = statistics.median(values)
            interval = predicted["targets"][target]
            targets[target] = {
                "predicted": interval, "measured_median": median,
                "measured_p90": quantile(values, 0.9),
                "relative_median_error": abs(interval["center"] - median) / median,
                "covered_trials": sum(interval["lower"] <= value <= interval["upper"] for value in values),
                "trial_count": len(values),
                "median_interval_upper_to_measured_median": interval["upper"] / median,
            }
        stage_errors = {}
        for stage in stages_for_family(family):
            values = [stage_value(trial, stage) for trial in record["case"]["trials"]]
            median = statistics.median(values)
            stage_errors[stage] = {
                "measured_median": median, "measured_p90": quantile(values, 0.9),
                "measured_max": max(values),
                "coefficient_of_variation": statistics.pstdev(values) / statistics.mean(values),
                "predicted_median": predicted["stages"][stage]["center"],
                "relative_median_error": abs(predicted["stages"][stage]["center"] - median) / median,
                "pow_visibility": "opaque_in_prove" if stage == "runtime_prove_seconds_when_pow_opaque"
                                  else "separate" if stage.endswith("_pow_seconds") else "not_pow",
            }
        program_results.append({"program": record["name"], "family": family,
                                "source_sha256": record["source"],
                                "features": record["features"],
                                "targets": targets, "stages": stage_errors})
    gates = protocol["accuracy_gate"]
    accuracy = {}
    passed = True
    for family in protocol["profiles"]:
        members = [program for program in program_results if program["family"] == family]
        family_accuracy = {}
        for target in TARGETS:
            entries = [program["targets"][target] for program in members]
            errors = [entry["relative_median_error"] for entry in entries]
            family_accuracy[target] = {
                "programs": len(members),
                "median_program_relative_error": statistics.median(errors),
                "p90_program_relative_error": quantile(errors, 0.9),
                "max_program_relative_error": max(errors),
                "trial_interval_coverage": sum(entry["covered_trials"] for entry in entries) /
                                           sum(entry["trial_count"] for entry in entries),
                "median_interval_upper_to_measured_median": statistics.median(
                    entry["median_interval_upper_to_measured_median"] for entry in entries),
            }
        accuracy[family] = family_accuracy
        if (len(members) < gates["minimum_validation_programs_per_family"] or
            any(entry["targets"]["proof_bytes"]["trial_count"] <
                gates["minimum_validation_trials_per_program"] for entry in members)):
            passed = False
        wall = family_accuracy["paired_prove_and_verify_wall_seconds"]
        if (wall["p90_program_relative_error"] > gates["per_family_whole_wall_program_median_p90_relative_error_max"] or
            wall["trial_interval_coverage"] < gates["per_family_whole_wall_trial_interval_coverage_min"] or
            wall["median_interval_upper_to_measured_median"] > gates["per_family_whole_wall_median_interval_upper_to_measured_median_max"]):
            passed = False
        for target, limit in (("proof_bytes", gates["per_family_proof_bytes_program_median_p90_relative_error_max"]),
                              ("prover_peak_rss_bytes", gates["per_family_prover_rss_program_median_p90_relative_error_max"])):
            stat = family_accuracy[target]
            if (stat["p90_program_relative_error"] > limit or
                stat["trial_interval_coverage"] < gates["per_family_proof_bytes_and_rss_trial_interval_coverage_min"]):
                passed = False
    return {"schema": "s31-whole-prover-cost-evaluation-v3.1",
            "protocol_sha256": corpus["protocol_sha256"],
            "compiler_sha256": model["compiler_sha256"],
            "programs": program_results, "accuracy": accuracy,
            "local_accuracy_gate_pass": passed,
            "automatic_lowering_selection_enabled": False,
            "selection_reason": protocol["selection_policy"],
            "interpretation": "One-host same-compiler prospective check; stochastic-stage intervals are empirical, not calibrated tail bounds."}


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
