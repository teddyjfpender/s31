#!/usr/bin/env python3
"""Freeze, collect, fit, and independently rescore a local S31 cost holdout."""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
BENCH = HERE.parent
S31 = BENCH.parent
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(BENCH))
sys.path.insert(0, str(BENCH / "fixed_integer_addition"))

import s31
from fixed_integer_addition import paired as addition
from fixed_integer_multiplication import paired as multiplication
from oracle import evaluate_relation
from text_frontend import compile_text

from evidence import analyze, host_identity, stage_parts
from prospective_model import (CALIBRATION_WIDTH, FIT_WIDTHS, HOLDOUT_WIDTH,
                               LOWERINGS, OPS, TRIALS_PER_PROGRAM,
                               fit as fit_model,
                               predict_group, predict_one, score as score_model)

TOOLS = (HERE / "prospective.py", HERE / "prospective_model.py",
         HERE / "evidence.py", HERE / "paired_tune.py",
         BENCH / "fixed_integer_addition/paired.py",
         BENCH / "fixed_integer_multiplication/paired.py")
COUNT = TRIALS_PER_PROGRAM
ADD_SEED = 0x531ADD
MUL_SEED = 0x531A11


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def read(path: Path) -> dict:
    result = json.loads(path.read_text())
    require(isinstance(result, dict), f"{path}: expected JSON object")
    return result


def write_new(path: Path, data: dict) -> None:
    require(not path.exists(), f"refusing to overwrite frozen artifact: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    s31.write_json(path, data)


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def split(width: int) -> str:
    return ("fit" if width in FIT_WIDTHS else
            "calibration" if width == CALIBRATION_WIDTH else
            "holdout" if width == HOLDOUT_WIDTH else "unsupported")


def identity() -> dict:
    return {"compiler_sha256": s31.compiler_fingerprint(),
            "host": host_identity(),
            "engine_gitlink_commit": subprocess.check_output(
                ["git", "-C", str(S31.parents[2] / "deps/stwo-zig"),
                 "rev-parse", "HEAD"], text=True).strip(),
            "tool_sha256": {str(path.relative_to(S31)): sha(path) for path in TOOLS},
            "oracle_provenance": s31.oracle_provenance()}


def source_text(operation: str, width: int) -> str:
    kind = f"u{width}"
    return (f"use std@1;\ncircuit {kind}_checked_{operation}(private a: {kind}, "
            f"private b: {kind}) -> public {kind} "
            f"{{ std::int::{operation}_checked(a, b) }}\n")


def prepare_case(output: Path, operation: str, width: int) -> dict:
    require(operation in OPS and split(width) != "unsupported", "unsupported program")
    directory = output / "inputs" / f"{operation}-u{width}"
    directory.mkdir(parents=True, exist_ok=False)
    if operation == "mul":
        source, assignments, _ = multiplication.prepare(
            f"u{width}", COUNT, MUL_SEED, directory)
    else:
        source = directory / f"u{width}_checked_add.s31"
        source.write_text(source_text(operation, width))
        relation, _ = compile_text(source.read_text(), str(source))
        result_name = relation["public_outputs"][0]
        assignments = []
        for index, (a, b) in enumerate(addition.corpus(f"u{width}", COUNT, ADD_SEED)):
            value = {"public_inputs": {},
                     "private_inputs": {"a": addition.limbs(a, width),
                                        "b": addition.limbs(b, width)},
                     "public_outputs": {result_name: addition.limbs(a + b, width)}}
            require(evaluate_relation(relation, value) == value["public_outputs"],
                    "independent arithmetic oracle rejected planned witness")
            path = directory / "assignments" / f"{index:03d}.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            s31.write_json(path, value)
            assignments.append(path)
    require(source.read_text() == source_text(operation, width),
            "paired source template changed")
    return {"operation": operation, "width": width, "split": split(width),
            "source_sha256": sha(source),
            "assignment_sha256": [s31.assignment_digest(path) for path in assignments]}


def plan(output: Path) -> dict:
    output = output.resolve()
    require(not (output / "plan.json").exists(), "plan already exists")
    cases = [prepare_case(output, op, width)
             for width in (*FIT_WIDTHS, CALIBRATION_WIDTH, HOLDOUT_WIDTH)
             for op in OPS]
    source_assignment_pairs = [(case["source_sha256"], digest)
                               for case in cases for digest in case["assignment_sha256"]]
    require(len(set(source_assignment_pairs)) == len(source_assignment_pairs),
            "the source/assignment split is not disjoint")
    data = {"schema": "s31-fixed-integer-prospective-plan-v1",
            "status": "pre-native-local-freeze", "count_per_source": COUNT,
            "lowerings": list(LOWERINGS), "cases": cases,
            "identity": identity(),
            "measurement": "Each paired runner builds both packages, warms each with one separate native process, then alternates direct/sparse order across eight distinct witnesses. Package build is recorded separately; every measured proof and verifier uses fresh processes with cold native setup.",
            "split_policy": "u16/u32 fit; u64 residual calibration; u128 unseen-width holdout within the same source template. No u128 native build or proof before model.json and model.sha256 are sealed.",
            "limits": "Local freeze needs a commit or external timestamp before collection for stronger chronology; no cross-host transfer or automatic lowering."}
    write_new(output / "plan.json", data)
    (output / "plan.sha256").write_text(sha(output / "plan.json") + "\n")
    return data


def check_plan(output: Path) -> dict:
    output = output.resolve()
    path = output / "plan.json"
    data = read(path)
    require(data.get("schema") == "s31-fixed-integer-prospective-plan-v1" and
            data.get("count_per_source") == COUNT and
            data.get("lowerings") == list(LOWERINGS), "unsupported plan")
    require((output / "plan.sha256").read_text().strip() == sha(path),
            "plan bytes differ from sealed hash")
    require(data.get("identity") == identity(), "compiler, host, engine, tools, or oracle drift")
    expected = {(op, width) for op in OPS
                for width in (*FIT_WIDTHS, CALIBRATION_WIDTH, HOLDOUT_WIDTH)}
    cases = data.get("cases")
    require(isinstance(cases, list) and len(cases) == len(expected) and
            {(case["operation"], case["width"]) for case in cases} == expected,
            "source roster differs")
    source_assignment_pairs = []
    for case in cases:
        op, width = case["operation"], case["width"]
        directory = output / "inputs" / f"{op}-u{width}"
        source = directory / f"u{width}_checked_{op}.s31"
        require(case["split"] == split(width) and
                source.read_text() == source_text(op, width) and
                sha(source) == case["source_sha256"], "planned source changed")
        assignments = [directory / "assignments" / f"{i:03d}.json"
                       for i in range(COUNT)]
        require(set((directory / "assignments").glob("*.json")) == set(assignments),
                "planned assignment roster changed")
        hashes = [s31.assignment_digest(path) for path in assignments]
        require(hashes == case["assignment_sha256"] and len(set(hashes)) == COUNT,
                "planned assignment digest changed")
        source_assignment_pairs.extend((case["source_sha256"], digest)
                                       for digest in hashes)
    require(len(set(source_assignment_pairs)) == len(source_assignment_pairs),
            "training and holdout source/assignment pairs overlap")
    return data


def run_dir(output: Path, operation: str, width: int) -> Path:
    return output / "runs" / f"{operation}-u{width}"


def collect(output: Path, phase: str) -> dict:
    data = check_plan(output)
    if phase == "holdout":
        model = check_model(output)
    else:
        require(phase == "training", "expected training or holdout phase")
        require(not (output / "model.json").exists() and
                not (output / "runs" / "add-u128").exists(),
                "training must precede model and holdout collection")
    selected = [case for case in data["cases"]
                if (case["split"] == "holdout") == (phase == "holdout")]
    completed = []
    for case in selected:
        op, width = case["operation"], case["width"]
        directory = run_dir(output, op, width)
        if directory.exists():
            check_run(output, case)
            if phase == "holdout":
                check_prediction(output, case, model)
            completed.append(f"{op}-u{width} (verified existing run)")
            continue
        runner = addition if op == "add" else multiplication
        callback = (lambda packages, manifests, case=case:
                    seal_preproof_prediction(output, case, model, packages, manifests)) \
            if phase == "holdout" else None
        before_build = (lambda case=case:
                        seal_prebuild_prediction(output, case, model)) \
            if phase == "holdout" else None
        runner.run(f"u{width}", COUNT, ADD_SEED if op == "add" else MUL_SEED,
                   directory, callback, before_build)
        check_run(output, case)
        if phase == "holdout":
            check_prediction(output, case, model)
        check_plan(output)
        completed.append(f"{op}-u{width}")
    return {"phase": phase, "completed": completed}


def build_prediction(model: dict, operation: str, width: int) -> dict:
    result = {}
    for lowering in LOWERINGS:
        center = predict_one(model["groups"][f"{operation}/{lowering}"]["fits"]["build"],
                             {"width": float(width)})
        band = model["bands"]["build"]
        result[lowering] = {"predicted_center": center,
                            "target_interval": [center * band["lower_ratio"],
                                                center * band["upper_ratio"]]}
    return result


def seal_prebuild_prediction(output: Path, case: dict, model: dict) -> None:
    """Persist width-only build predictions before the first package build."""
    op, width = case["operation"], case["width"]
    directory = run_dir(output, op, width)
    require(not any((directory / "tune" / name).exists()
                    for name in ("packages", "warmup", "runs")),
            "prebuild prediction must precede native package build and proof")
    write_new(directory / "prebuild-prediction.json", {
        "schema": "s31-fixed-integer-prebuild-prediction-v1",
        "source_sha256": case["source_sha256"],
        "plan_sha256": sha(output / "plan.json"),
        "model_sha256": sha(output / "model.json"),
        "phase": "before-any-native-package-build",
        "profiles": build_prediction(model, op, width)})


def seal_preproof_prediction(output: Path, case: dict, model: dict,
                             packages: dict, manifests: dict) -> None:
    """Called after native package build and before any native proof process."""
    op, width = case["operation"], case["width"]
    profiles = {}
    for lowering in LOWERINGS:
        manifest = manifests[lowering]
        require(manifest["source_text_sha256"] == case["source_sha256"] and
                manifest["lowering"] == lowering and
                manifest["compiler_sha256"] == model["identity"]["compiler_sha256"],
                "holdout package identity drifted before prediction")
        cost = read(packages[lowering] / "cost-report.json")
        geometry = {name: cost[name] for name in
                    ("raw", "padded", "preprocessed_cells")}
        geometry["visible_fri"] = s31.visible_fri(cost, lowering)
        center = predict_group(model["groups"][f"{op}/{lowering}"],
                               {"width": width, "geometry": geometry})
        profiles[lowering] = {
            "geometry": geometry, "predicted_centers": center,
            "target_intervals": {
                name: [center[name] * band["lower_ratio"],
                       center[name] * band["upper_ratio"]]
                for name, band in model["bands"].items()}}
    write_new(run_dir(output, op, width) / "preproof-prediction.json", {
        "schema": "s31-fixed-integer-preproof-prediction-v1",
        "source_sha256": case["source_sha256"],
        "plan_sha256": sha(output / "plan.json"),
        "model_sha256": sha(output / "model.json"),
        "phase": "after-package-build-before-any-native-proof",
        "profiles": profiles})


def check_prediction(output: Path, case: dict, model: dict) -> None:
    op, width = case["operation"], case["width"]
    prebuild = read(run_dir(output, op, width) / "prebuild-prediction.json")
    require(prebuild == {
        "schema": "s31-fixed-integer-prebuild-prediction-v1",
        "source_sha256": case["source_sha256"],
        "plan_sha256": sha(output / "plan.json"),
        "model_sha256": sha(output / "model.json"),
        "phase": "before-any-native-package-build",
        "profiles": build_prediction(model, op, width)},
        "held-out build prediction differs from sealed training model")
    saved = read(run_dir(output, op, width) / "preproof-prediction.json")
    require(saved.get("schema") == "s31-fixed-integer-preproof-prediction-v1" and
            saved.get("source_sha256") == case["source_sha256"] and
            saved.get("plan_sha256") == sha(output / "plan.json") and
            saved.get("model_sha256") == sha(output / "model.json") and
            saved.get("phase") == "after-package-build-before-any-native-proof" and
            set(saved.get("profiles", {})) == set(LOWERINGS),
            "holdout preproof prediction identity changed")
    tune = read(run_dir(output, op, width) / "tune" / "tune-report.json")
    for lowering in LOWERINGS:
        profile = tune["profiles"][lowering]
        geometry = {name: profile[name] for name in
                    ("raw", "padded", "preprocessed_cells", "visible_fri")}
        center = predict_group(model["groups"][f"{op}/{lowering}"],
                               {"width": width, "geometry": geometry})
        expected = {"geometry": geometry, "predicted_centers": center,
                    "target_intervals": {
                        name: [center[name] * band["lower_ratio"],
                               center[name] * band["upper_ratio"]]
                        for name, band in model["bands"].items()}}
        require(saved["profiles"][lowering] == expected,
                f"{lowering}: preproof prediction differs from model or native geometry")
        require(saved["profiles"][lowering]["predicted_centers"]["build"] ==
                prebuild["profiles"][lowering]["predicted_center"] and
                saved["profiles"][lowering]["target_intervals"]["build"] ==
                prebuild["profiles"][lowering]["target_interval"],
                f"{lowering}: postbuild record changed prebuild prediction")


def check_run(output: Path, case: dict) -> dict:
    op, width = case["operation"], case["width"]
    directory = run_dir(output, op, width)
    audit = analyze(directory)
    summary = read(directory / "summary.json")
    require(audit["operation"] == op and audit["kind"] == f"u{width}" and
            audit["count"] == COUNT and
            summary["source_sha256"] == case["source_sha256"] and
            summary["assignment_sha256"] == case["assignment_sha256"],
            "native evidence differs from predeclared source and witnesses")
    return summary


def extract(output: Path, case: dict) -> list[dict]:
    summary = check_run(output, case)
    op, width = case["operation"], case["width"]
    directory = run_dir(output, op, width)
    tune = read(directory / "tune" / "tune-report.json")
    result = []
    for lowering in LOWERINGS:
        profile = tune["profiles"][lowering]
        trials = []
        for index in range(COUNT):
            raw = read(directory / "tune" / "runs" / lowering /
                       f"{index:03d}" / "trial-report.json")
            parts = stage_parts(raw, f"{op}-u{width}/{lowering}/{index}")
            rss = raw["prover_peak_rss_bytes"]
            require(type(rss) is int and rss > 0,
                    "prover RSS unavailable; this study fails closed")
            trials.append({"stages": {
                "witness": parts["witness"], "setup": parts["setup"],
                "prove_non_pow": parts["prove_non_pow"],
                "interaction_pow": parts["interaction_pow"],
                "fri_pow": parts["fri_pow"],
                "runtime_other": parts["runtime_other"],
                "process_residual": parts["process_residual"],
                "verify": parts["native_verify_process"]},
                "whole": parts["whole_process"],
                "proof_bytes": raw["proof_bytes"], "prover_rss": rss})
        result.append({"operation": op, "width": width, "lowering": lowering,
                       "source_sha256": summary["source_sha256"],
                       "assignment_sha256": case["assignment_sha256"],
                       "geometry": {name: profile[name] for name in
                                    ("raw", "padded", "preprocessed_cells", "visible_fri")},
                       "build_seconds": profile["build_or_load_seconds"],
                       "trials": trials})
    return result


def model_artifacts(output: Path, data: dict) -> dict:
    return {"plan_sha256": sha(output / "plan.json"),
            "evidence_summary_sha256": {
                f"{case['operation']}-u{case['width']}":
                    sha(run_dir(output, case["operation"], case["width"]) / "summary.json")
                for case in data["cases"] if case["split"] != "holdout"}}


def fit(output: Path) -> dict:
    data = check_plan(output)
    require(not (output / "model.json").exists() and
            not any(run_dir(output, op, HOLDOUT_WIDTH).exists() for op in OPS),
            "model must be sealed before any holdout run")
    training = [row for case in data["cases"] if case["split"] != "holdout"
                for row in extract(output, case)]
    model = {**fit_model(training), **model_artifacts(output, data),
             "identity": data["identity"]}
    write_new(output / "model.json", model)
    (output / "model.sha256").write_text(sha(output / "model.json") + "\n")
    return model


def check_model(output: Path) -> dict:
    data = check_plan(output)
    model = read(output / "model.json")
    require((output / "model.sha256").read_text().strip() ==
            sha(output / "model.json"), "model differs from sealed hash")
    require(model.get("schema") == "s31-fixed-integer-prospective-model-v1" and
            model.get("identity") == data["identity"] and
            {key: model.get(key) for key in ("plan_sha256", "evidence_summary_sha256")} ==
            model_artifacts(output, data), "model identity or training evidence drifted")
    training = [row for case in data["cases"] if case["split"] != "holdout"
                for row in extract(output, case)]
    expected = {**fit_model(training), **model_artifacts(output, data),
                "identity": data["identity"]}
    require(model == expected, "sealed model differs from training-only refit")
    return model


def score(output: Path) -> dict:
    data = check_plan(output)
    model = check_model(output)
    for case in data["cases"]:
        if case["split"] == "holdout":
            check_prediction(output, case, model)
    heldout = [row for case in data["cases"] if case["split"] == "holdout"
               for row in extract(output, case)]
    report = {**score_model(model, heldout),
              "plan_sha256": sha(output / "plan.json"),
              "model_sha256": sha(output / "model.json"),
              "holdout_prebuild_prediction_sha256": {
                  f"{case['operation']}-u{case['width']}":
                      sha(run_dir(output, case["operation"], case["width"]) /
                          "prebuild-prediction.json")
                  for case in data["cases"] if case["split"] == "holdout"},
              "holdout_preproof_prediction_sha256": {
                  f"{case['operation']}-u{case['width']}":
                      sha(run_dir(output, case["operation"], case["width"]) /
                          "preproof-prediction.json")
                  for case in data["cases"] if case["split"] == "holdout"},
              "holdout_summary_sha256": {
                  f"{case['operation']}-u{case['width']}":
                      sha(run_dir(output, case["operation"], case["width"]) / "summary.json")
                  for case in data["cases"] if case["split"] == "holdout"}}
    if (output / "score.json").exists():
        require(read(output / "score.json") == report,
                "saved held-out score differs from independent recomputation")
    else:
        write_new(output / "score.json", report)
    return report


def validate(output: Path) -> dict:
    data = check_plan(output)
    states = {}
    for case in data["cases"]:
        name = f"{case['operation']}-u{case['width']}"
        states[name] = "verified" if run_dir(output, case["operation"],
                                             case["width"]).exists() else "pending"
        if states[name] == "verified":
            check_run(output, case)
    if (output / "model.json").exists():
        model = check_model(output)
        for case in data["cases"]:
            if case["split"] == "holdout" and states[
                    f"{case['operation']}-u{case['width']}"] == "verified":
                check_prediction(output, case, model)
    if (output / "score.json").exists():
        score(output)
    return {"schema": "s31-fixed-integer-prospective-validation-v1",
            "plan_sha256": sha(output / "plan.json"),
            "model_sha256": sha(output / "model.json") if
                (output / "model.json").exists() else None,
            "cases": states,
            "holdout_scored": (output / "score.json").exists()}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("plan", "collect-training", "fit",
                                            "collect-holdout", "score", "validate"))
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    action = {"plan": plan,
              "collect-training": lambda path: collect(path, "training"),
              "fit": fit,
              "collect-holdout": lambda path: collect(path, "holdout"),
              "score": score, "validate": validate}[args.command]
    print(json.dumps(action(output), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
