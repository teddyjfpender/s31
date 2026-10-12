#!/usr/bin/env python3
"""Score an anchored, native-audited transfer corpus against the frozen v1 fit.

This module never fits or calibrates on transfer observations. Its model file
must have the exact pre-existing training-only SHA-256. An evaluation remains
unpublished until its audit, corpus and evaluation hashes are report-anchored.
"""

from __future__ import annotations

import argparse
import json
import math
import statistics
import subprocess
from datetime import datetime, timezone
from pathlib import Path

from cohort import ROOT, SHAPES, canonical, design, inventory, sha
from protocol import check, path_name
from study import audit as replay_audit
from study import phase_anchor, raw_root

REPORT_ANCHOR = ROOT / "design/s31/measurements/language/mixed-stage-cost-transfer-v1-report-anchor.json"

STAGES = ("profile_rebuild_ns", "semantic_evaluation_ns", "topology_compile_ns",
          "witness_compile_ns", "native_prove_including_setup_ns",
          "envelope_and_serialization_ns", "prover_process_residual_ns",
          "external_verifier_process_wall_ns")
TARGETS = ("first_verified_process_wall_ns", "proof_bytes")


def quantile(values: list[float], fraction: float) -> float:
    if not values or not 0 <= fraction <= 1 or any(not math.isfinite(x) for x in values):
        raise ValueError("quantile needs finite values and fraction in [0,1]")
    ordered = sorted(values)
    rank = fraction * (len(ordered) - 1)
    index = int(rank)
    return ordered[index] + (ordered[min(index + 1, len(ordered) - 1)] - ordered[index]) * (rank - index)


def predict(model: dict, count: int) -> dict:
    if model.get("schema") != "s31-mixed-stage-cost-v1-model" or \
            model.get("automatic_lowering_selection_enabled") is not False or \
            not 1 <= count <= 8:
        raise ValueError("wrong frozen mixed stage model")
    features = model.get("features")
    expected = {name: ("constant" if name in
                        ("prover_process_residual_ns", "external_verifier_process_wall_ns")
                        else "call_count") for name in (*STAGES, "proof_bytes")}
    if features != expected or set(model.get("fits", {})) != set(expected):
        raise ValueError("frozen model features differ from predeclared v1 fit")
    values = {}
    for name, kind in expected.items():
        fit = model["fits"][name]
        if (fit.get("kind") != kind or
                type(fit.get("intercept")) not in (int, float) or
                type(fit.get("slope")) not in (int, float) or
                not math.isfinite(fit["intercept"]) or
                not math.isfinite(fit["slope"]) or
                fit["intercept"] < 0 or fit["slope"] < 0 or
                (kind == "constant" and fit["slope"] != 0)):
            raise ValueError("frozen model fit is malformed")
        values[name] = fit["intercept"] + fit["slope"] * (count if kind == "call_count" else 0)
    centers = {"first_verified_process_wall_ns": sum(values[name] for name in STAGES),
               "proof_bytes": values["proof_bytes"]}
    result = {}
    bands = model.get("predictive_ratio_bands", {})
    if set(bands) != set(TARGETS):
        raise ValueError("frozen model interval bands differ")
    for name in TARGETS:
        band = bands[name]
        if (type(band.get("lower_ratio")) not in (int, float) or
                type(band.get("upper_ratio")) not in (int, float) or
                not 0 < band["lower_ratio"] <= 1 <= band["upper_ratio"] or
                not math.isfinite(band["upper_ratio"]) or centers[name] <= 0):
            raise ValueError("frozen model prediction interval is invalid")
        result[name] = {"center": centers[name],
                        "lower": centers[name] * band["lower_ratio"],
                        "upper": centers[name] * band["upper_ratio"]}
    return result


def evaluate(model: dict, corpus: dict, protocol: dict) -> dict:
    cfg = design()
    roster = inventory(cfg)
    if (corpus.get("schema") != "s31-mixed-stage-cost-transfer-v1-audited-corpus" or
            corpus.get("protocol_sha256") != sha(canonical(protocol)) or
            corpus.get("inventory_sha256") != protocol["inventory_sha256"] or
            corpus.get("host") != protocol["host"] or
            corpus.get("compiler_sha256") != protocol["compiler_sha256"] or
            corpus.get("engine_gitlink_commit") != protocol["engine_gitlink_commit"] or
            len(corpus.get("records", [])) != len(roster)):
        raise ValueError("audited transfer corpus differs from prospective protocol")
    if (model.get("protocol_sha256") != cfg["reference_protocol_sha256"] or
            model.get("engine_gitlink_commit") != protocol["engine_gitlink_commit"]):
        raise ValueError("reference model provenance or engine pin differs")
    rows = []
    for record, (name, expected) in zip(corpus["records"], roster.items()):
        if (record.get("name") != name or record.get("shape") != expected["shape"] or
                record.get("call_count") != expected["call_count"] or
                record.get("source_sha256") != expected["source_sha256"] or
                type(record.get("build_wall_ns")) is not int or
                record["build_wall_ns"] <= 0 or
                len(record.get("trials", [])) != cfg["assignments_per_program"]):
            raise ValueError("audited transfer program differs from frozen roster")
        predicted = predict(model, expected["call_count"])
        targets = {}
        for target in TARGETS:
            actual = [trial.get(target) for trial in record["trials"]]
            if any(type(x) is not int or x <= 0 for x in actual):
                raise ValueError("audited target is missing or nonpositive")
            middle = statistics.median(actual)
            band = predicted[target]
            targets[target] = {"measured_median": middle,
                               "predicted": band,
                               "median_relative_error": abs(band["center"] - middle) / middle,
                               "covered_trials": sum(band["lower"] <= x <= band["upper"]
                                                     for x in actual),
                               "trial_count": len(actual),
                               "interval_upper_to_measured_median": band["upper"] / middle}
        rows.append({"name": name, "shape": expected["shape"],
                     "call_count": expected["call_count"],
                     "source_sha256": expected["source_sha256"],
                     "observed_package_build_wall_ns": record["build_wall_ns"],
                     "targets": targets})
    controls = [row for row in rows if row["shape"] == "control"]
    transfers = [row for row in rows if row["shape"] != "control"]
    gate = cfg["diagnostic_gates"]
    metrics = {
        "control_wall_program_median_p90_relative_error": quantile(
            [row["targets"][TARGETS[0]]["median_relative_error"] for row in controls], .9),
        "control_proof_program_median_p90_relative_error": quantile(
            [row["targets"][TARGETS[1]]["median_relative_error"] for row in controls], .9),
        "transfer_wall_program_median_p90_relative_error": quantile(
            [row["targets"][TARGETS[0]]["median_relative_error"] for row in transfers], .9),
        "transfer_proof_program_median_p90_relative_error": quantile(
            [row["targets"][TARGETS[1]]["median_relative_error"] for row in transfers], .9),
        "wall_trial_interval_coverage_by_shape": {},
        "proof_trial_interval_coverage_by_shape": {},
        "wall_median_interval_upper_to_measured_median": statistics.median(
            row["targets"][TARGETS[0]]["interval_upper_to_measured_median"] for row in rows),
        "proof_median_interval_upper_to_measured_median": statistics.median(
            row["targets"][TARGETS[1]]["interval_upper_to_measured_median"] for row in rows),
    }
    for shape in SHAPES:
        shape_rows = [row for row in rows if row["shape"] == shape]
        if len(shape_rows) != 3:
            raise ValueError("each transfer shape needs all three call counts")
        for target, label in ((TARGETS[0], "wall"), (TARGETS[1], "proof")):
            targets = [row["targets"][target] for row in shape_rows]
            metrics[f"{label}_trial_interval_coverage_by_shape"][shape] = \
                sum(item["covered_trials"] for item in targets) / \
                sum(item["trial_count"] for item in targets)
    passed = {
        "minimum_programs": len(rows) >= gate["minimum_programs"],
        "minimum_verified_trials_per_program": all(
            len(record["trials"]) >= gate["minimum_verified_trials_per_program"]
            for record in corpus["records"]),
    }
    for label in ("control_wall_program_median_p90_relative_error",
                  "control_proof_program_median_p90_relative_error",
                  "transfer_wall_program_median_p90_relative_error",
                  "transfer_proof_program_median_p90_relative_error",
                  "wall_median_interval_upper_to_measured_median",
                  "proof_median_interval_upper_to_measured_median"):
        passed[label] = metrics[label] <= gate[label + "_max"]
    for label in ("wall_trial_interval_coverage_by_shape",
                  "proof_trial_interval_coverage_by_shape"):
        passed[label] = all(value >= gate[label + "_min"]
                            for value in metrics[label].values())
    return {"schema": "s31-mixed-stage-cost-transfer-v1-evaluation",
            "protocol_sha256": corpus["protocol_sha256"],
            "phase_root_sha256": corpus["phase_root_sha256"],
            "reference_train_model_sha256": cfg["reference_train_model_sha256"],
            "reference_compiler_sha256": model["compiler_sha256"],
            "measured_compiler_sha256": corpus["compiler_sha256"],
            "same_compiler_revision": model["compiler_sha256"] == corpus["compiler_sha256"],
            "programs": rows, "metrics": metrics, "gate_pass": passed,
            "cross_shape_diagnostic_gate_pass": all(passed.values()),
            "automatic_lowering_selection_enabled": False,
            "speedup_claim_enabled": False}


def score(out: Path, model_path: Path, protocol_sha256: str, anchor_commit: str,
          root_sha256: str, phase_commit: str) -> dict:
    protocol = check(protocol_sha256, anchor_commit)
    cfg = design()
    if sha(model_path.read_bytes()) != cfg["reference_train_model_sha256"]:
        raise ValueError("model is not the frozen training-only v1 fit")
    model = json.loads(model_path.read_bytes())
    phase_anchor(protocol_sha256, root_sha256, anchor_commit, phase_commit)
    if sha((out / "phase-root.json").read_bytes()) != root_sha256 or \
            (out / "phase-root.json").read_bytes() != canonical(raw_root(out, protocol_sha256)):
        raise ValueError("transfer raw phase changed after anchor")
    audit = json.loads((out / "audit.json").read_bytes())
    corpus_bytes = (out / "corpus.json").read_bytes()
    corpus = json.loads(corpus_bytes)
    if (audit.get("schema") != "s31-mixed-stage-cost-transfer-v1-audit" or
            audit.get("protocol_sha256") != protocol_sha256 or
            audit.get("phase_root_sha256") != root_sha256 or
            audit.get("corpus_sha256") != sha(corpus_bytes) or
            audit.get("native_verified_proofs") != 360 or
            audit.get("changed_input_and_result_rejected") is not True or
            audit.get("raw_build_and_process_endpoints_replayed") is not True or
            audit.get("source_assignment_statement_manifest_and_binary_hashes_replayed") is not True or
            corpus.get("phase_root_sha256") != root_sha256 or
            (out / "evaluation.json").exists()):
        raise ValueError("transfer native audit is incomplete or evaluation already exists")
    result = evaluate(model, corpus, protocol)
    (out / "evaluation.json").write_bytes(canonical(result))
    return result


def report_check(out: Path, model_path: Path, protocol_sha256: str,
                 anchor_commit: str, root_sha256: str, phase_commit: str,
                 report_commit: str) -> dict:
    """Recompute the score after native replay and verify a committed seal."""
    if len(report_commit) != 40 or any(char not in "0123456789abcdef" for char in report_commit):
        raise ValueError("full transfer report anchor commit required")
    if (subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       phase_commit, report_commit], check=False).returncode or
            subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                            report_commit, "HEAD"], check=False).returncode):
        raise ValueError("transfer report anchor must follow the phase anchor")
    protocol = check(protocol_sha256, anchor_commit)
    phase = phase_anchor(protocol_sha256, root_sha256, anchor_commit, phase_commit)
    saved = subprocess.check_output(["git", "-C", str(ROOT), "show",
                                     f"{report_commit}:{path_name(REPORT_ANCHOR)}"])
    if saved != REPORT_ANCHOR.read_bytes():
        raise ValueError("transfer report anchor differs from committed bytes")
    anchor = json.loads(saved)
    try:
        stamp = datetime.fromisoformat(anchor["recorded_at_utc"].replace("Z", "+00:00"))
        phase_stamp = datetime.fromisoformat(phase["recorded_at_utc"].replace("Z", "+00:00"))
    except (KeyError, ValueError, TypeError) as exc:
        raise ValueError("transfer report anchor needs UTC timestamp") from exc
    if (set(anchor) != {"schema", "protocol_sha256", "phase_root_sha256",
                        "phase_anchor_commit", "reference_train_model_sha256",
                        "audit_sha256", "corpus_sha256", "evaluation_sha256",
                        "recorded_at_utc"} or
            anchor["schema"] != "s31-mixed-stage-cost-transfer-v1-report-anchor" or
            anchor["protocol_sha256"] != protocol_sha256 or
            anchor["phase_root_sha256"] != root_sha256 or
            anchor["phase_anchor_commit"] != phase_commit or
            anchor["reference_train_model_sha256"] !=
                design()["reference_train_model_sha256"] or
            stamp.utcoffset() is None or stamp.utcoffset().total_seconds() != 0 or
            stamp < phase_stamp or stamp > datetime.now(timezone.utc)):
        raise ValueError("transfer report anchor differs from frozen protocol or chronology")
    if sha(model_path.read_bytes()) != anchor["reference_train_model_sha256"]:
        raise ValueError("transfer report uses a different model")
    files = {}
    for name in ("audit", "corpus", "evaluation"):
        raw = (out / f"{name}.json").read_bytes()
        value = json.loads(raw)
        if raw != canonical(value) or sha(raw) != anchor[f"{name}_sha256"]:
            raise ValueError(f"transfer {name} differs from committed report seal")
        files[name] = value
    if ((out / "phase-root.json").read_bytes() != canonical(raw_root(out, protocol_sha256)) or
            sha((out / "phase-root.json").read_bytes()) != root_sha256):
        raise ValueError("transfer raw phase differs from report seal")
    replay_audit(out, protocol_sha256, anchor_commit, root_sha256,
                 phase_commit, write=False)
    expected = evaluate(json.loads(model_path.read_bytes()), files["corpus"], protocol)
    if (out / "evaluation.json").read_bytes() != canonical(expected):
        raise ValueError("transfer evaluation differs from frozen model and native corpus")
    return {"schema": "s31-mixed-stage-cost-transfer-v1-report-check",
            "report_anchor_commit": report_commit,
            "report_anchor_sha256": sha(saved),
            "cross_shape_diagnostic_gate_pass": expected["cross_shape_diagnostic_gate_pass"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("score", "report-check"))
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--model", required=True, type=Path)
    parser.add_argument("--expected-protocol-sha256", required=True)
    parser.add_argument("--protocol-anchor-commit", required=True)
    parser.add_argument("--expected-phase-root-sha256", required=True)
    parser.add_argument("--phase-anchor-commit", required=True)
    parser.add_argument("--report-anchor-commit")
    args = parser.parse_args()
    common = (args.out.resolve(), args.model, args.expected_protocol_sha256,
              args.protocol_anchor_commit, args.expected_phase_root_sha256,
              args.phase_anchor_commit)
    if args.command == "report-check":
        if not args.report_anchor_commit:
            parser.error("report-check requires --report-anchor-commit")
        result = report_check(*common, args.report_anchor_commit)
        print(json.dumps(result, sort_keys=True))
    else:
        result = score(*common)
        print(json.dumps({"cross_shape_diagnostic_gate_pass":
                          result["cross_shape_diagnostic_gate_pass"],
                          "evaluation_sha256": sha(canonical(result))}, sort_keys=True))


if __name__ == "__main__":
    main()
