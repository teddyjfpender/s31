#!/usr/bin/env python3
"""Pin a portable audit summary of one measured multiscale cost corpus."""

from __future__ import annotations

import argparse
import hashlib
import json
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from whole_prover_predictor import _fit_log_line, _predict, _p90


DIAGNOSTIC_STAGES = (
    "runtime_witness_seconds", "runtime_setup_seconds", "runtime_prove_seconds",
    "runtime_prove_excluding_pow_seconds", "runtime_interaction_pow_seconds",
    "runtime_fri_pow_seconds", "prover_process_unattributed_seconds",
    "native_verify_process_wall_seconds",
)


def _digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _error_summary(values: list[float]) -> dict:
    return ({"predictions": len(values), "median_relative_error": statistics.median(values),
             "p90_relative_error": _p90(values), "max_relative_error": max(values)}
            if values else {"predictions": 0, "median_relative_error": None,
                            "p90_relative_error": None, "max_relative_error": None})


def _stage_diagnostics(cases: dict) -> dict:
    """Exploratory LOO stage errors with the frozen padded-row feature.

    These targets were chosen after the headline model was run. They cannot
    rehabilitate its failed latency gate and never feed automatic selection.
    """
    families = sorted({case["family"] for case in cases.values()})
    result = {}
    for family in families:
        members = [(name, case) for name, case in cases.items() if case["family"] == family]
        per_stage = {}
        for stage in DIAGNOSTIC_STAGES:
            errors = []
            relative_mads = []
            missing = 0
            for held_name, held in members:
                measured = held["observed_cost_model"]["metrics"].get(stage)
                if measured is None or measured["median"] <= 0:
                    missing += 1
                    continue
                scale = sum(held["padded"].values())
                train = [
                    (sum(other["padded"].values()), other_metric["median"])
                    for name, other in members if name != held_name
                    if (other_metric := other["observed_cost_model"]["metrics"].get(stage)) is not None
                    and other_metric["median"] > 0
                ]
                fit = _fit_log_line(train)
                if fit is None:
                    missing += 1
                    continue
                prediction = _predict(fit, scale)
                errors.append(abs(prediction - measured["median"]) / measured["median"])
                if measured.get("median_absolute_deviation") is not None:
                    relative_mads.append(measured["median_absolute_deviation"] / measured["median"])
            per_stage[stage] = {
                **_error_summary(errors),
                "missing_or_unfit_programs": missing,
                "median_observed_relative_mad": statistics.median(relative_mads) if relative_mads else None,
            }
        result[family] = per_stage
    return result


def publish(corpus_path: Path, evaluation_path: Path) -> dict:
    corpus = json.loads(corpus_path.read_text())
    evaluation = json.loads(evaluation_path.read_text())
    if corpus["schema"] != "s31-multiscale-cost-corpus-v1" or evaluation["schema"] != "s31-whole-prover-held-out-evaluation-v1":
        raise ValueError("unsupported corpus or evaluation schema")
    if evaluation["corpus_sha256"] != _digest(corpus_path):
        raise ValueError("evaluation is not bound to the supplied corpus")
    root = corpus_path.parent
    cases = corpus["cases"]
    accepted = rejected = oracle_passed = 0
    case_summaries = {}
    for name, case in sorted(cases.items()):
        trial_paths = sorted((root / name / "trials").glob("*/trial-report.json"))
        if len(trial_paths) != corpus["samples_per_program"]:
            raise ValueError(f"{name}: missing saved trial reports")
        for trial_path in trial_paths:
            trial = json.loads(trial_path.read_text())
            proof = trial_path.parent / "proof.bin"
            if _digest(proof) != trial["proof_sha256"] or proof.stat().st_size != trial["proof_bytes"]:
                raise ValueError(f"{name}: saved proof bytes do not match trial report")
            accepted += trial["native_verifier_accepted"] is True
            rejected += bool(trial["changed_public_statement_rejected"])
            oracle_passed += trial["independent_value_oracle"]["status"] == "passed"
        if not len(set(case["assignment_sha256"])) == len(trial_paths):
            raise ValueError(f"{name}: assignment corpus is not distinct")
        selected_metrics = (
            "paired_prove_and_verify_wall_seconds", "proof_bytes", "prover_peak_rss_bytes",
            "runtime_witness_seconds", "runtime_setup_seconds", "runtime_prove_seconds",
            "runtime_prove_excluding_pow_seconds", "runtime_interaction_pow_seconds",
            "runtime_fri_pow_seconds", "native_verify_process_wall_seconds",
        )
        case_summaries[name] = {
            "family": case["family"], "source_sha256": case["source_sha256"],
            "lowering": case["lowering"], "profile": case["profile"],
            "raw": case["raw"], "padded": case["padded"],
            "preprocessed_cells": case["preprocessed_cells"],
            "package_build": case["package_build"],
            "metrics": {key: case["observed_cost_model"]["metrics"].get(key)
                        for key in selected_metrics},
        }
    trial_count = sum(len(list((root / name / "trials").glob("*/trial-report.json"))) for name in cases)
    if (accepted, rejected, oracle_passed) != (trial_count, trial_count, trial_count):
        raise ValueError("native proof, changed-claim or independent-oracle control failed")
    family_errors = {}
    for family in sorted({case["family"] for case in cases.values()}):
        family_errors[family] = {}
        for metric in evaluation["accuracy"]:
            values = [item["relative_error"] for item in evaluation["predictions"]
                      if item["family"] == family and item["metric"] == metric]
            family_errors[family][metric] = _error_summary(values)
    return {
        "schema": "s31-whole-prover-heldout-pinned-v1",
        "corpus_sha256": _digest(corpus_path),
        "evaluation_sha256": _digest(evaluation_path),
        "host": corpus["host"],
        "compiler_sha256": sorted({case["compiler_sha256"] for case in cases.values()}),
        "programs": len(cases), "trials": trial_count,
        "controls": {"native_accepted": accepted, "changed_claim_rejected": rejected,
                     "independent_oracle_passed": oracle_passed},
        "headline_accuracy": evaluation["accuracy"],
        "per_family_accuracy": family_errors,
        "exploratory_stage_errors": _stage_diagnostics(cases),
        "stage_note": "Stage fits are post hoc diagnostics with the frozen padded-row feature; they are excluded from the cost accuracy gate and are not calibrated predictions.",
        "cost_accuracy_gate_pass": evaluation["cost_accuracy_gate_pass"],
        "automatic_lowering_selection_enabled": evaluation["automatic_lowering_selection_enabled"],
        "selection_reasons": evaluation["selection_reasons"],
        "cases": case_summaries,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("corpus", type=Path)
    parser.add_argument("evaluation", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    result = publish(args.corpus, args.evaluation)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
