"""Predeclared one-host mixed stage predictor; no native work in this module.

The output is a profile-local diagnostic, never an automatic lowering policy.
Training and evaluation consume only a separately audited and anchored corpus.
"""

from __future__ import annotations

import math
import statistics

from cohort import design

PACKAGE_STAGES = (
    "profile_rebuild_ns", "semantic_evaluation_ns", "topology_compile_ns",
    "witness_compile_ns", "native_prove_including_setup_ns",
    "envelope_and_serialization_ns",
)
STAGES = (*PACKAGE_STAGES, "prover_process_residual_ns",
          "external_verifier_process_wall_ns")
TARGETS = ("first_verified_process_wall_ns", "proof_bytes")


def quantile(values: list[float], fraction: float) -> float:
    if not values or not 0 <= fraction <= 1 or any(not math.isfinite(v) for v in values):
        raise ValueError("quantile requires finite values and fraction in [0,1]")
    ordered = sorted(values)
    rank = fraction * (len(ordered) - 1)
    index = int(rank)
    return ordered[index] + (ordered[min(index + 1, len(ordered) - 1)] - ordered[index]) * (rank - index)


def components(report: dict) -> dict[str, int]:
    if report.get("schema") != "s31-mixed-stage-diagnostic-v1" or \
            report.get("external_native_verification_accepted") is not True or \
            report.get("engine_setup_preprocessing_ns", "missing") is not None or \
            report.get("engine_pow_ns", "missing") is not None:
        raise ValueError("trial lacks the accepted mixed stage diagnostic profile")
    stage = report.get("prover_internal_stages_ns")
    if type(stage) is not dict or set(stage) != {*PACKAGE_STAGES, "package_total_ns"} or \
            any(type(value) is not int or value < 0 for value in stage.values()) or \
            stage["package_total_ns"] <= 0 or \
            stage["package_total_ns"] != sum(stage[name] for name in PACKAGE_STAGES):
        raise ValueError("mixed package intervals do not partition the package timer")
    if stage["native_prove_including_setup_ns"] <= 0:
        raise ValueError("accepted mixed proof needs positive native proving work")
    for name in (*TARGETS, "prover_process_wall_ns", "external_verifier_process_wall_ns"):
        if type(report.get(name)) is not int or report[name] <= 0:
            raise ValueError(f"{name} must be a positive nanosecond count or byte size")
    residual = report["prover_process_wall_ns"] - stage["package_total_ns"]
    timing = report.get("process_monotonic_ns")
    if (type(timing) is not dict or
            set(timing) != {"prover_start", "prover_end", "verifier_start", "verifier_end"} or
            any(type(value) is not int or value < 0 for value in timing.values()) or
            not timing["prover_start"] < timing["prover_end"] <=
                timing["verifier_start"] < timing["verifier_end"] or
            timing["prover_end"] - timing["prover_start"] != report["prover_process_wall_ns"] or
            timing["verifier_end"] - timing["verifier_start"] !=
                report["external_verifier_process_wall_ns"]):
        raise ValueError("raw monotonic process endpoints differ from summarized wall time")
    if residual < 0 or report["first_verified_process_wall_ns"] != \
            report["prover_process_wall_ns"] + report["external_verifier_process_wall_ns"]:
        raise ValueError("process and package wall accounting differ")
    return {**{name: stage[name] for name in PACKAGE_STAGES},
            "prover_process_residual_ns": residual,
            "external_verifier_process_wall_ns": report["external_verifier_process_wall_ns"],
            "first_verified_process_wall_ns": report["first_verified_process_wall_ns"],
            "proof_bytes": report["proof_bytes"]}


def _fit_feature(points: list[tuple[int, float]], kind: str) -> dict:
    if len(points) < 3 or any(type(x) is not int or not 1 <= x <= 8 or
                              not math.isfinite(y) or y < 0 for x, y in points):
        raise ValueError("a stage fit requires at least three valid program medians")
    if kind == "constant":
        return {"kind": kind, "intercept": statistics.median(y for _, y in points),
                "slope": 0.0}
    if kind != "call_count" or len({x for x, _ in points}) != len(points):
        raise ValueError("the call-count feature must have distinct sources")
    mx = statistics.mean(x for x, _ in points)
    my = statistics.mean(y for _, y in points)
    denominator = sum((x - mx) ** 2 for x, _ in points)
    slope = sum((x - mx) * (y - my) for x, y in points) / denominator
    if slope <= 0:
        return {"kind": kind, "intercept": my, "slope": 0.0}
    intercept = my - slope * mx
    if intercept < 0:
        slope = sum(x * y for x, y in points) / sum(x * x for x, _ in points)
        intercept = 0.0
    return {"kind": kind, "intercept": intercept, "slope": slope}


def _estimate(fit: dict, count: int) -> float:
    if fit["kind"] not in ("constant", "call_count") or not 1 <= count <= 8:
        raise ValueError("unsupported feature or count")
    value = fit["intercept"] + fit["slope"] * (count if fit["kind"] == "call_count" else 0)
    if not math.isfinite(value) or value < 0:
        raise ValueError("stage model produced invalid cost")
    return value


def _record_values(record: dict) -> dict[str, list[int]]:
    trials = record.get("trials")
    if type(trials) is not list or not trials:
        raise ValueError("source has no audited trials")
    values = [components(report) for report in trials]
    return {name: [item[name] for item in values] for name in (*STAGES, *TARGETS)}


def _fit(records: list[dict], cfg: dict) -> dict:
    per_source = [(record["call_count"], _record_values(record)) for record in records]
    return {name: _fit_feature([(count, statistics.median(values[name]))
                                for count, values in per_source],
                               cfg["model_features"][name])
            for name in (*STAGES, "proof_bytes")}


def _center(fits: dict, count: int) -> dict[str, float]:
    stages = {name: _estimate(fits[name], count) for name in STAGES}
    return {**stages, "first_verified_process_wall_ns": sum(stages.values()),
            "proof_bytes": _estimate(fits["proof_bytes"], count)}


def fit_model(records: list[dict], protocol_sha256: str, inventory_sha256: str,
              host: dict, compiler_sha256: str, engine_gitlink_commit: str) -> dict:
    cfg = design()
    counts = [record.get("call_count") for record in records]
    if sorted(counts) != cfg["train_call_counts"] or len(records) != 4 or \
            len({record.get("source_sha256") for record in records}) != 4:
        raise ValueError("training sources differ from the prospective split")
    for record in records:
        if len(record["trials"]) != cfg["assignments_per_call_count"]:
            raise ValueError("training assignment count differs from prospectus")
    fits = _fit(records, cfg)
    # Leave an entire source out; using per-trial LOO would leak its program median.
    loo_ratios: dict[str, list[float]] = {target: [] for target in TARGETS}
    for held in records:
        others = [record for record in records if record is not held]
        prediction = _center(_fit(others, cfg), held["call_count"])
        observations = _record_values(held)
        for target in TARGETS:
            if prediction[target] <= 0:
                raise ValueError("LOO target prediction is nonpositive")
            loo_ratios[target].extend(value / prediction[target]
                                      for value in observations[target])
    bands = {name: {"lower_ratio": min(1.0, quantile(ratios, 0.05)),
                    "upper_ratio": max(1.0, quantile(ratios, 0.95))}
             for name, ratios in loo_ratios.items()}
    if any(band["lower_ratio"] <= 0 or not math.isfinite(band["upper_ratio"])
           for band in bands.values()):
        raise ValueError("training predictive interval is invalid")
    return {
        "schema": "s31-mixed-stage-cost-v1-model",
        "protocol_sha256": protocol_sha256,
        "inventory_sha256": inventory_sha256,
        "host": host,
        "compiler_sha256": compiler_sha256,
        "engine_gitlink_commit": engine_gitlink_commit,
        "training_source_sha256": sorted(record["source_sha256"] for record in records),
        "training_assignment_sha256": sorted(report["assignment_sha256"] for record in records
                                              for report in record["trials"]),
        "features": cfg["model_features"],
        "fits": fits,
        "predictive_ratio_bands": bands,
        "automatic_lowering_selection_enabled": False,
        "scope": "one host/compiler/engine and pinned record-ABI-v2 16-round repeat-chain source family",
    }


def predict(model: dict, count: int) -> dict:
    if model.get("schema") != "s31-mixed-stage-cost-v1-model" or \
            model.get("features") != design()["model_features"]:
        raise ValueError("model is outside the prospective mixed stage profile")
    values = _center(model["fits"], count)
    bands = model["predictive_ratio_bands"]
    targets = {name: {"center": values[name],
                      "lower": values[name] * bands[name]["lower_ratio"],
                      "upper": values[name] * bands[name]["upper_ratio"]}
               for name in TARGETS}
    return {"call_count": count,
            "stages_ns": {name: values[name] for name in STAGES},
            "targets": targets}


def evaluate(model: dict, records: list[dict], *, protocol_sha256: str,
             inventory_sha256: str, host: dict, compiler_sha256: str,
             engine_gitlink_commit: str) -> dict:
    cfg = design()
    if (model.get("protocol_sha256") != protocol_sha256 or
            model.get("inventory_sha256") != inventory_sha256 or
            model.get("host") != host or
            model.get("compiler_sha256") != compiler_sha256 or
            model.get("engine_gitlink_commit") != engine_gitlink_commit or
            sorted(record.get("call_count") for record in records) != cfg["heldout_call_counts"] or
            len(records) != cfg["accuracy_gate"]["minimum_heldout_programs"]):
        raise ValueError("held-out corpus differs from frozen model identity or split")
    if set(model["training_source_sha256"]) & {record["source_sha256"] for record in records}:
        raise ValueError("training source leaked into held-out evaluation")
    if set(model["training_assignment_sha256"]) & {
            report["assignment_sha256"] for record in records for report in record["trials"]}:
        raise ValueError("training assignment leaked into held-out evaluation")
    programs = []
    for record in records:
        if len(record["trials"]) != cfg["assignments_per_call_count"]:
            raise ValueError("held-out assignment count differs from prospectus")
        count = record["call_count"]
        predicted = predict(model, count)
        observed = _record_values(record)
        targets = {}
        for name in TARGETS:
            median = statistics.median(observed[name])
            band = predicted["targets"][name]
            targets[name] = {
                "measured_median": median,
                "predicted": band,
                "median_relative_error": abs(band["center"] - median) / median,
                "trial_count": len(observed[name]),
                "covered_trials": sum(band["lower"] <= value <= band["upper"]
                                      for value in observed[name]),
                "interval_upper_to_measured_median": band["upper"] / median,
            }
        native_median = statistics.median(observed["native_prove_including_setup_ns"])
        build = record["build_wall_ns"]
        if type(build) is not int or build <= 0:
            raise ValueError("package build wall is missing or invalid")
        programs.append({
            "call_count": count,
            "source_sha256": record["source_sha256"],
            "targets": targets,
            "native_opaque_median_relative_error":
                abs(predicted["stages_ns"]["native_prove_including_setup_ns"] - native_median) /
                native_median,
            "build_accounting": {
                "observed_package_build_wall_ns": build,
                "observed_first_verified_median_ns":
                    targets["first_verified_process_wall_ns"]["measured_median"],
                "observed_build_plus_first_verified_median_ns":
                    build + targets["first_verified_process_wall_ns"]["measured_median"],
                "observed_amortized_per_proof_at_100_reuses_ns":
                    build / 100 + targets["first_verified_process_wall_ns"]["measured_median"],
                "build_modelled": False,
            },
        })
    wall = [row["targets"]["first_verified_process_wall_ns"] for row in programs]
    proof = [row["targets"]["proof_bytes"] for row in programs]
    gate = cfg["accuracy_gate"]
    metrics = {
        "whole_wall_program_median_p90_relative_error": quantile(
            [row["median_relative_error"] for row in wall], 0.9),
        "whole_wall_program_median_max_relative_error": max(
            row["median_relative_error"] for row in wall),
        "whole_wall_trial_interval_coverage": sum(row["covered_trials"] for row in wall) /
                                              sum(row["trial_count"] for row in wall),
        "whole_wall_median_interval_upper_to_measured_median": statistics.median(
            row["interval_upper_to_measured_median"] for row in wall),
        "proof_bytes_program_median_p90_relative_error": quantile(
            [row["median_relative_error"] for row in proof], 0.9),
        "proof_bytes_trial_interval_coverage": sum(row["covered_trials"] for row in proof) /
                                               sum(row["trial_count"] for row in proof),
        "proof_bytes_median_interval_upper_to_measured_median": statistics.median(
            row["interval_upper_to_measured_median"] for row in proof),
        "native_opaque_program_median_p90_relative_error": quantile(
            [row["native_opaque_median_relative_error"] for row in programs], 0.9),
    }
    passed = all((metrics[name] >= bound if gate_name.endswith("_min") else metrics[name] <= bound)
                 for gate_name, bound in gate.items()
                 if gate_name != "minimum_heldout_programs"
                 for name in [gate_name.removesuffix("_max").removesuffix("_min")])
    return {
        "schema": "s31-mixed-stage-cost-v1-evaluation",
        "protocol_sha256": protocol_sha256,
        "inventory_sha256": inventory_sha256,
        "programs": sorted(programs, key=lambda row: row["call_count"]),
        "accuracy": metrics,
        "local_accuracy_gate_pass": passed,
        "automatic_lowering_selection_enabled": False,
        "interpretation": "One-host, one-source-shape diagnostic; empirical intervals are not tail guarantees. Package builds are observed separately, not predicted.",
    }
