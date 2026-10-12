#!/usr/bin/env python3
"""Prospective local direct-gate geometry transfer diagnostic.

The plan fixes every source, assignment, metric, split, geometry and gate before
native work. Training seals one constant estimate per padded-row stratum before
any held-out package is built. This is not a general whole-prover predictor.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import statistics
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from runtime.cost_model import distribution  # noqa: E402

P = (1 << 31) - 1
SCHEMA = "s31-direct-gate-geometry-transfer-v1"
TRAIN = (32, 192, 384)
HELDOUT = (96, 256, 448)
SAMPLES = 12
GEOMETRY = {32: 512, 96: 512, 192: 512, 256: 1024, 384: 1024, 448: 1024}
METRICS = ("paired_wall_seconds", "paired_after_pow_seconds", "proof_bytes",
           "prover_peak_rss_bytes")
LIMITS = {"paired_wall_seconds": 0.50, "paired_after_pow_seconds": 0.30,
          "proof_bytes": 0.10, "prover_peak_rss_bytes": 0.15}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode()


def source_for(gates: int) -> str:
    if gates not in GEOMETRY:
        raise ValueError("gate count is outside the predeclared roster")
    operations = ["let p1 = x .* x;"]
    for index in range(2, gates + 1):
        op = "+" if index % 2 == 0 else ".*"
        operations.append(f"let p{index} = x {op} p{index - 1};")
    return (f"circuit geometry_transfer_{gates}(public x: [m31; 4]) "
            "-> public [m31; 4] {\n    " + "\n    ".join(operations) +
            f"\n    p{gates}\n}}\n")


def assignment_for(gates: int, sample: int) -> dict:
    if gates not in GEOMETRY or not 0 <= sample < SAMPLES:
        raise ValueError("assignment is outside the predeclared roster")
    words = ([P - 2, P - 1, 0, 1] if sample == 0 else
             [sample * 17 + gates * 5 + lane + 2 for lane in range(4)])
    result = [(word * word) % P for word in words]
    for index in range(2, gates + 1):
        result = [((value + word) if index % 2 == 0 else value * word) % P
                  for value, word in zip(result, words, strict=True)]
    return {"public_inputs": {"x": words}, "private_inputs": {},
            "public_outputs": {f"p{gates}": result}}


def inventory() -> dict:
    return {str(gates): {
        "source_sha256": sha(source_for(gates).encode()),
        "assignment_sha256": [sha(canonical(assignment_for(gates, sample)))
                              for sample in range(SAMPLES)],
        "expected_padded_qm31_rows": GEOMETRY[gates],
    } for gates in (*TRAIN, *HELDOUT)}


def identity() -> dict:
    engine = subprocess.check_output(
        ["git", "-C", str(ROOT / "deps/stwo-zig"), "rev-parse", "HEAD"],
        text=True).strip()
    return {
        "compiler_sha256": s31.compiler_fingerprint(),
        "engine_commit": engine,
        "study_sha256": s31.file_hash(Path(__file__)),
        "independent_scorer_sha256": s31.file_hash(HERE / "independent_score.py"),
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(),
                 "zig": s31.invoke("zig", "version").strip()},
    }


def plan_payload() -> dict:
    return {
        "schema": SCHEMA, "phase": "planned-before-native-work",
        "identity": identity(), "train": list(TRAIN), "heldout": list(HELDOUT),
        "samples_per_program": SAMPLES, "sources": inventory(),
        "lowering": "direct-gate", "build_mode": "ReleaseFast",
        "metrics": list(METRICS), "diagnostic_relative_median_error_limits": LIMITS,
        "estimator": "For each padded-row stratum and metric, the median of its training program medians; no slope, refit, or held-out selection.",
        "scope": "One host/compiler/engine. Above 16 gates is outside the bounded direct-gate release correspondence certificate. Native proof acceptance, changed-claim rejection and independent value checks are required; no automatic lowering decision.",
    }


def checked_plan(out: Path) -> dict:
    plan = json.loads((out / "plan.json").read_bytes())
    if plan != plan_payload():
        raise ValueError("plan, compiler, engine, host, tool, or input roster changed")
    return plan


def create_plan(out: Path) -> None:
    if out.exists():
        raise FileExistsError("plan needs a fresh output directory")
    out.mkdir(parents=True)
    s31.write_json(out / "plan.json", plan_payload())


def metric(trial: dict, name: str) -> float:
    if trial.get("native_verifier_accepted") is not True or not trial.get(
            "changed_public_statement_rejected") or trial.get(
            "independent_value_oracle", {}).get("status") != "passed":
        raise ValueError("trial lacks proof/changed-claim/value controls")
    if name in ("paired_wall_seconds", "paired_after_pow_seconds"):
        value = trial["prove_seconds"] + trial["verify_seconds"]
        if name == "paired_after_pow_seconds":
            stages = trial.get("prover_stages") or {}
            pow_fri = stages.get("fri_pow_seconds")
            pow_interaction = stages.get("interaction_pow_seconds")
            if not all(type(v) in (float, int) and v >= 0
                       for v in (pow_fri, pow_interaction)):
                raise ValueError("after-PoW metric needs both native PoW timers")
            value -= pow_fri + pow_interaction
    else:
        value = trial[name]
    if type(value) not in (int, float) or not math.isfinite(value) or value <= 0:
        raise ValueError(f"invalid measured {name}")
    return float(value)


def read_phase(out: Path, split: str, plan: dict) -> dict[int, list[dict]]:
    counts = TRAIN if split == "train" else HELDOUT
    rows = {}
    for gates in counts:
        directory = out / split / f"gates-{gates}"
        source = directory / f"geometry_transfer_{gates}.s31"
        package = directory / "package"
        if s31.file_hash(source) != plan["sources"][str(gates)]["source_sha256"]:
            raise ValueError("saved source differs from plan")
        manifest = s31.verify_package(package)
        if manifest["compiler_sha256"] != plan["identity"]["compiler_sha256"] or \
                manifest["lowering"] != "direct-gate":
            raise ValueError("saved package differs from compiler/lowering plan")
        cost = json.loads((package / "cost-report.json").read_bytes())
        if cost["padded"]["qm31_ops"] != GEOMETRY[gates]:
            raise ValueError("native padded QM31 geometry differs from plan")
        trials = []
        for sample in range(SAMPLES):
            assignment = directory / "assignments" / f"{sample:03}.json"
            if s31.assignment_digest(assignment) != plan["sources"][str(gates)]["assignment_sha256"][sample]:
                raise ValueError("saved assignment differs from plan")
            report = directory / "trials" / f"{sample:03}" / "trial-report.json"
            trial = json.loads(report.read_bytes())
            if (s31.file_hash(directory / "trials" / f"{sample:03}" / "proof.bin") !=
                    trial["proof_sha256"] or trial["padded"]["qm31_ops"] != GEOMETRY[gates]):
                raise ValueError("saved proof hash or trial geometry differs")
            for name in METRICS:
                metric(trial, name)
            trials.append(trial)
        rows[gates] = trials
    return rows


def calibration(rows: dict[int, list[dict]]) -> dict:
    if set(rows) != set(TRAIN):
        raise ValueError("calibration requires the complete train split")
    result = {}
    for geometry in (512, 1024):
        counts = [g for g in TRAIN if GEOMETRY[g] == geometry]
        result[str(geometry)] = {}
        for name in METRICS:
            medians = {str(g): statistics.median(metric(t, name) for t in rows[g])
                       for g in counts}
            values = [metric(t, name) for g in counts for t in rows[g]]
            result[str(geometry)][name] = {
                "center": statistics.median(medians.values()),
                "training_program_medians": medians,
                "descriptive_training_min": min(values),
                "descriptive_training_max": max(values),
            }
    return result


def score(model: dict, rows: dict[int, list[dict]]) -> dict:
    if set(rows) != set(HELDOUT):
        raise ValueError("score requires the complete held-out split")
    cases = {}
    for gates in HELDOUT:
        geometry = GEOMETRY[gates]
        cases[str(gates)] = {"padded_qm31_rows": geometry, "metrics": {}}
        for name in METRICS:
            values = [metric(t, name) for t in rows[gates]]
            predictor = model[str(geometry)][name]
            observed = statistics.median(values)
            cases[str(gates)]["metrics"][name] = {
                "predicted_center": predictor["center"],
                "observed": distribution(values),
                "relative_median_error": abs(observed - predictor["center"]) / observed,
                "descriptive_training_range_covered_trials": sum(
                    predictor["descriptive_training_min"] <= value <=
                    predictor["descriptive_training_max"] for value in values),
            }
    gates = {name: all(cases[str(g)]["metrics"][name]["relative_median_error"] <= bound
                       for g in HELDOUT) for name, bound in LIMITS.items()}
    return {"cases": cases, "diagnostic_gates": gates,
            "all_diagnostic_gates_pass": all(gates.values())}


def run_phase(out: Path, split: str) -> None:
    plan = checked_plan(out)
    phase_dir = out / split
    if phase_dir.exists():
        raise FileExistsError("phase evidence already exists; use a fresh root")
    if split == "heldout":
        sealed = json.loads((out / "calibration.json").read_bytes())
        if (sealed.get("schema") != SCHEMA or
                sealed.get("phase") != "sealed-before-heldout-build" or
                sealed.get("plan_sha256") != s31.file_hash(out / "plan.json") or
                sealed.get("train_report_sha256") != s31.file_hash(out / "train-report.json") or
                sealed.get("model") != calibration(read_phase(out, "train", plan))):
            raise ValueError("training calibration or evidence changed")
        calibration_sha = s31.file_hash(out / "calibration.json")
    phase_dir.mkdir()
    counts = TRAIN if split == "train" else HELDOUT
    builds = {}
    for gates in counts:
        directory = phase_dir / f"gates-{gates}"
        directory.mkdir()
        source = directory / f"geometry_transfer_{gates}.s31"
        source.write_text(source_for(gates))
        started = time.perf_counter()
        package = s31.build(source, directory / "package", "direct-gate")
        builds[str(gates)] = time.perf_counter() - started
        cost = json.loads((package / "cost-report.json").read_bytes())
        if cost["padded"]["qm31_ops"] != GEOMETRY[gates]:
            raise ValueError("native padded geometry differs from frozen plan")
        for sample in range(SAMPLES):
            assignment = directory / "assignments" / f"{sample:03}.json"
            assignment.parent.mkdir(exist_ok=True)
            s31.write_json(assignment, assignment_for(gates, sample))
            s31.trial(package, assignment, directory / "trials" / f"{sample:03}")
        print(f"{split}: {gates} gates, {SAMPLES} verified proofs", flush=True)
    rows = read_phase(out, split, plan)
    report = {"schema": SCHEMA, "phase": split,
              "plan_sha256": s31.file_hash(out / "plan.json"),
              "package_build_wall_seconds": builds,
              "cases": {str(g): {
                  "source_sha256": s31.file_hash(phase_dir / f"gates-{g}" /
                                                 f"geometry_transfer_{g}.s31"),
                  "package_manifest_sha256": s31.file_hash(
                      phase_dir / f"gates-{g}" / "package" / "manifest.json"),
                  "raw_qm31_rows": rows[g][0]["raw"]["qm31_ops"],
                  "padded_qm31_rows": GEOMETRY[g],
                  "proof_sha256": [t["proof_sha256"] for t in rows[g]],
                  "trial_report_sha256": [s31.file_hash(
                      phase_dir / f"gates-{g}" / "trials" / f"{i:03}" / "trial-report.json")
                      for i in range(SAMPLES)],
              } for g in counts}}
    s31.write_json(out / f"{split}-report.json", report)
    if split == "train":
        s31.write_json(out / "calibration.json", {
            "schema": SCHEMA, "phase": "sealed-before-heldout-build",
            "plan_sha256": s31.file_hash(out / "plan.json"),
            "train_report_sha256": s31.file_hash(out / "train-report.json"),
            "model": calibration(rows),
        })
    else:
        s31.write_json(out / "heldout-score.json", {
            "schema": SCHEMA, "phase": "local-heldout-diagnostic",
            "plan_sha256": s31.file_hash(out / "plan.json"),
            "calibration_sha256_before_heldout": calibration_sha,
            "heldout_report_sha256": s31.file_hash(out / "heldout-report.json"),
            **score(sealed["model"], rows),
        })


def audit(out: Path) -> dict:
    """Recompute sealed scoring and replay saved native proof/claim controls."""
    plan = checked_plan(out)
    train = read_phase(out, "train", plan)
    heldout = read_phase(out, "heldout", plan)
    sealed = json.loads((out / "calibration.json").read_bytes())
    if (sealed.get("schema") != SCHEMA or
            sealed.get("phase") != "sealed-before-heldout-build" or
            sealed.get("plan_sha256") != s31.file_hash(out / "plan.json") or
            sealed.get("train_report_sha256") != s31.file_hash(out / "train-report.json") or
            sealed.get("model") != calibration(train)):
        raise ValueError("saved calibration does not reproduce from training evidence")
    saved_score = json.loads((out / "heldout-score.json").read_bytes())
    expected_score = {
        "schema": SCHEMA, "phase": "local-heldout-diagnostic",
        "plan_sha256": s31.file_hash(out / "plan.json"),
        "calibration_sha256_before_heldout": s31.file_hash(out / "calibration.json"),
        "heldout_report_sha256": s31.file_hash(out / "heldout-report.json"),
        **score(sealed["model"], heldout),
    }
    if saved_score != expected_score:
        raise ValueError("saved held-out score differs from independent recomputation")
    replayed = 0
    for split, rows in (("train", train), ("heldout", heldout)):
        for gates, trials in rows.items():
            directory = out / split / f"gates-{gates}"
            package = directory / "package"
            manifest = json.loads((package / "manifest.json").read_bytes())
            verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
            key = package / "verification-key.json"
            for sample, _ in enumerate(trials):
                saved = directory / "trials" / f"{sample:03}"
                proof = saved / "proof.bin"
                s31.invoke(str(verifier), str(proof), str(saved / "statement.json"), str(key))
                try:
                    s31.invoke(str(verifier), str(proof),
                               str(saved / "changed-statement.json"), str(key))
                except RuntimeError:
                    pass
                else:
                    raise ValueError("native verifier accepted changed public statement")
                replayed += 1
    result = {
        "schema": SCHEMA, "phase": "native-replay-audit",
        "plan_sha256": s31.file_hash(out / "plan.json"),
        "calibration_sha256": s31.file_hash(out / "calibration.json"),
        "heldout_score_sha256": s31.file_hash(out / "heldout-score.json"),
        "replayed_accepted_proofs": replayed,
        "replayed_rejected_changed_claims": replayed,
        "independent_value_checks_in_trial_reports": replayed,
    }
    s31.write_json(out / "audit.json", result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("plan", "train", "heldout", "audit"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    if args.phase == "plan":
        create_plan(out)
    elif args.phase == "audit":
        audit(out)
    else:
        run_phase(out, args.phase)
    print(out / ("plan.json" if args.phase == "plan" else
                 "calibration.json" if args.phase == "train" else
                 "heldout-score.json" if args.phase == "heldout" else "audit.json"))


if __name__ == "__main__":
    main()
