#!/usr/bin/env python3
"""Prospective all-add/all-multiply transfer of a sealed geometry cost model.

The prior model is read-only. `plan` binds it and every new source/assignment
before builds. `heldout` measures six fresh programs without fitting.
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
PRIOR = HERE.parent / "geometry_transfer_v1" / "results-2026-10-11"
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from runtime.cost_model import distribution  # noqa: E402

P = (1 << 31) - 1
SCHEMA = "s31-operation-mix-transfer-v1"
COUNTS = (96, 256, 448)
OPERATIONS = ("add", "mul")
SAMPLES = 12
ROWS = {96: 512, 256: 1024, 448: 1024}
METRICS = ("paired_wall_seconds", "paired_after_pow_seconds", "proof_bytes",
           "prover_peak_rss_bytes")
LIMITS = {"paired_wall_seconds": 0.50, "paired_after_pow_seconds": 0.30,
          "proof_bytes": 0.10, "prover_peak_rss_bytes": 0.15}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode()


def key(op: str, count: int) -> str:
    if op not in OPERATIONS or count not in COUNTS:
        raise ValueError("case is outside the fixed operation mix roster")
    return f"{op}-{count}"


def source_for(op: str, count: int) -> str:
    name = key(op, count)
    symbol = "+" if op == "add" else ".*"
    operations = [f"let p1 = x {symbol} x;"]
    operations.extend(f"let p{i} = x {symbol} p{i - 1};"
                      for i in range(2, count + 1))
    return (f"circuit operation_mix_{name.replace('-', '_')}(public x: [m31; 4]) "
            "-> public [m31; 4] {\n    " + "\n    ".join(operations) +
            f"\n    p{count}\n}}\n")


def assignment_for(op: str, count: int, sample: int) -> dict:
    key(op, count)
    if not 0 <= sample < SAMPLES:
        raise ValueError("sample is outside the fixed roster")
    words = ([P - 2, P - 1, 0, 1] if sample == 0 else
             [sample * 19 + count * 7 + (1000 if op == "mul" else 0) + lane + 3
              for lane in range(4)])
    result = [((word + word) if op == "add" else word * word) % P
              for word in words]
    for _ in range(2, count + 1):
        result = [((word + value) if op == "add" else word * value) % P
                  for word, value in zip(words, result, strict=True)]
    return {"public_inputs": {"x": words}, "private_inputs": {},
            "public_outputs": {f"p{count}": result}}


def inventory() -> dict:
    return {key(op, count): {
        "source_sha256": sha(source_for(op, count).encode()),
        "assignment_sha256": [sha(canonical(assignment_for(op, count, sample)))
                              for sample in range(SAMPLES)],
        "expected_padded_qm31_rows": ROWS[count],
    } for op in OPERATIONS for count in COUNTS}


def prior_calibration() -> tuple[dict, dict, str]:
    plan_path, model_path = PRIOR / "plan.json", PRIOR / "calibration.json"
    old_plan = json.loads(plan_path.read_bytes())
    model = json.loads(model_path.read_bytes())
    if (old_plan.get("schema") != "s31-direct-gate-geometry-transfer-v1" or
            model.get("plan_sha256") != s31.file_hash(plan_path) or
            model.get("phase") != "sealed-before-heldout-build" or
            set(model.get("model", {})) != {"512", "1024"} or
            any(set(model["model"][size]) != set(METRICS)
                for size in ("512", "1024"))):
        raise ValueError("prior sealed geometry calibration is invalid")
    return old_plan, model, s31.file_hash(model_path)


def identity() -> dict:
    engine = subprocess.check_output(
        ["git", "-C", str(ROOT / "deps/stwo-zig"), "rev-parse", "HEAD"],
        text=True).strip()
    return {"compiler_sha256": s31.compiler_fingerprint(),
            "engine_commit": engine,
            "study_sha256": s31.file_hash(Path(__file__)),
            "independent_scorer_sha256": s31.file_hash(HERE / "independent_score.py"),
            "independent_oracle_provenance": s31.oracle_provenance(),
            "host": {"platform": platform.platform(), "machine": platform.machine(),
                     "python": platform.python_version(),
                     "zig": s31.invoke("zig", "version").strip()}}


def plan_payload() -> dict:
    prior_plan, _, calibration_sha = prior_calibration()
    current = identity()
    if current["compiler_sha256"] != prior_plan["identity"]["compiler_sha256"] or \
            current["engine_commit"] != prior_plan["identity"]["engine_commit"] or \
            current["host"] != prior_plan["identity"]["host"]:
        raise ValueError("cross-family transfer requires the calibrated compiler, engine, and host")
    return {
        "schema": SCHEMA, "phase": "planned-before-native-work",
        "identity": current, "prior_plan_sha256": s31.file_hash(PRIOR / "plan.json"),
        "prior_calibration_sha256": calibration_sha,
        "operations": list(OPERATIONS), "counts": list(COUNTS),
        "samples_per_program": SAMPLES, "sources": inventory(),
        "lowering": "direct-gate", "metrics": list(METRICS),
        "diagnostic_relative_median_error_limits": LIMITS,
        "prediction_rule": "Use each metric's frozen 512/1024-row center from the prior mixed-operation calibration for every new program in that stratum; no fit or adjustment.",
        "scope": "One host/compiler/engine direct-gate operation-family transfer. Programs above 16 gates lie outside the bounded release correspondence certificate. No automatic lowering decision.",
    }


def checked_plan(out: Path) -> dict:
    saved = json.loads((out / "plan.json").read_bytes())
    if saved != plan_payload():
        raise ValueError("sealed plan, old calibration, compiler, host, source, or tool changed")
    return saved


def create_plan(out: Path) -> None:
    if out.exists():
        raise FileExistsError("plan needs a fresh output directory")
    out.mkdir(parents=True)
    s31.write_json(out / "plan.json", plan_payload())


def metric(trial: dict, name: str) -> float:
    if (trial.get("native_verifier_accepted") is not True or
            not trial.get("changed_public_statement_rejected") or
            trial.get("independent_value_oracle", {}).get("status") != "passed"):
        raise ValueError("trial lacks native verifier, changed-claim, or value control")
    if name in ("paired_wall_seconds", "paired_after_pow_seconds"):
        result = trial["prove_seconds"] + trial["verify_seconds"]
        if name == "paired_after_pow_seconds":
            stages = trial.get("prover_stages") or {}
            timers = (stages.get("fri_pow_seconds"),
                      stages.get("interaction_pow_seconds"))
            if any(type(v) not in (float, int) or v < 0 for v in timers):
                raise ValueError("both native PoW timers are required")
            result -= sum(timers)
    else:
        result = trial[name]
    if type(result) not in (float, int) or not math.isfinite(result) or result <= 0:
        raise ValueError(f"invalid {name}")
    return float(result)


def read_cases(out: Path, plan: dict) -> dict[str, list[dict]]:
    cases = {}
    for op in OPERATIONS:
        for count in COUNTS:
            label = key(op, count)
            directory = out / "heldout" / label
            source = directory / f"operation_mix_{op}_{count}.s31"
            if s31.file_hash(source) != plan["sources"][label]["source_sha256"]:
                raise ValueError("saved source differs from plan")
            package = directory / "package"
            manifest = s31.verify_package(package)
            if manifest["compiler_sha256"] != plan["identity"]["compiler_sha256"] or \
                    manifest["lowering"] != "direct-gate":
                raise ValueError("saved package differs from compiler plan")
            cost = json.loads((package / "cost-report.json").read_bytes())
            if cost["padded"]["qm31_ops"] != ROWS[count]:
                raise ValueError("native padded geometry differs from sealed plan")
            trials = []
            for sample in range(SAMPLES):
                assignment = directory / "assignments" / f"{sample:03}.json"
                if s31.assignment_digest(assignment) != plan["sources"][label]["assignment_sha256"][sample]:
                    raise ValueError("saved assignment differs from plan")
                trial_dir = directory / "trials" / f"{sample:03}"
                trial = json.loads((trial_dir / "trial-report.json").read_bytes())
                if (s31.file_hash(trial_dir / "proof.bin") != trial["proof_sha256"] or
                        trial["padded"]["qm31_ops"] != ROWS[count] or
                        trial.get("independent_value_oracle_provenance") !=
                        plan["identity"]["independent_oracle_provenance"]):
                    raise ValueError("saved proof hash, geometry, or oracle provenance differs")
                for name in METRICS:
                    metric(trial, name)
                trials.append(trial)
            cases[label] = trials
    return cases


def score(model: dict, cases: dict[str, list[dict]]) -> dict:
    if set(cases) != {key(op, count) for op in OPERATIONS for count in COUNTS}:
        raise ValueError("score requires the complete all-add/all-multiply roster")
    rows = {}
    for op in OPERATIONS:
        for count in COUNTS:
            label = key(op, count)
            size = str(ROWS[count])
            rows[label] = {"operation": op, "gates": count,
                           "padded_qm31_rows": ROWS[count], "metrics": {}}
            for name in METRICS:
                values = [metric(row, name) for row in cases[label]]
                predicted = model[size][name]["center"]
                observed = statistics.median(values)
                rows[label]["metrics"][name] = {
                    "predicted_center": predicted,
                    "observed": distribution(values),
                    "relative_median_error": abs(predicted - observed) / observed,
                }
    gates = {name: all(rows[label]["metrics"][name]["relative_median_error"] <= bound
                       for label in rows) for name, bound in LIMITS.items()}
    by_family = {op: {name: all(rows[key(op, count)]["metrics"][name]["relative_median_error"] <= bound
                            for count in COUNTS) for name, bound in LIMITS.items()}
                 for op in OPERATIONS}
    return {"cases": rows, "diagnostic_gates": gates,
            "operation_family_gates": by_family,
            "all_diagnostic_gates_pass": all(gates.values())}


def run_heldout(out: Path) -> None:
    plan = checked_plan(out)
    if (out / "heldout").exists() or (out / "heldout-score.json").exists():
        raise FileExistsError("held-out evidence already exists; use a new root")
    _, prior_model, prior_sha = prior_calibration()
    if prior_sha != plan["prior_calibration_sha256"]:
        raise ValueError("prior calibration changed before native build")
    phase = out / "heldout"
    phase.mkdir()
    builds = {}
    for op in OPERATIONS:
        for count in COUNTS:
            label = key(op, count)
            directory = phase / label
            directory.mkdir()
            source = directory / f"operation_mix_{op}_{count}.s31"
            source.write_text(source_for(op, count))
            started = time.perf_counter()
            package = s31.build(source, directory / "package", "direct-gate")
            builds[label] = time.perf_counter() - started
            cost = json.loads((package / "cost-report.json").read_bytes())
            if cost["padded"]["qm31_ops"] != ROWS[count]:
                raise ValueError("native padded geometry differs from frozen plan")
            for sample in range(SAMPLES):
                assignment = directory / "assignments" / f"{sample:03}.json"
                assignment.parent.mkdir(exist_ok=True)
                s31.write_json(assignment, assignment_for(op, count, sample))
                s31.trial(package, assignment, directory / "trials" / f"{sample:03}")
            print(f"heldout: {label}, {SAMPLES} verified proofs", flush=True)
    cases = read_cases(out, plan)
    report = {"schema": SCHEMA, "phase": "heldout",
              "plan_sha256": s31.file_hash(out / "plan.json"),
              "prior_calibration_sha256": prior_sha,
              "package_build_wall_seconds": builds,
              "cases": {label: {
                  "source_sha256": s31.file_hash(phase / label /
                                                 f"operation_mix_{label.replace('-', '_')}.s31"),
                  "package_manifest_sha256": s31.file_hash(phase / label / "package" /
                                                            "manifest.json"),
                  "raw_qm31_rows": cases[label][0]["raw"]["qm31_ops"],
                  "padded_qm31_rows": cases[label][0]["padded"]["qm31_ops"],
                  "proof_sha256": [row["proof_sha256"] for row in cases[label]],
                  "trial_report_sha256": [s31.file_hash(phase / label / "trials" /
                                                       f"{i:03}" / "trial-report.json")
                                          for i in range(SAMPLES)],
              } for label in cases}}
    s31.write_json(out / "heldout-report.json", report)
    s31.write_json(out / "heldout-score.json", {
        "schema": SCHEMA, "phase": "no-refit-heldout-transfer",
        "plan_sha256": s31.file_hash(out / "plan.json"),
        "prior_calibration_sha256": prior_sha,
        "heldout_report_sha256": s31.file_hash(out / "heldout-report.json"),
        **score(prior_model["model"], cases),
    })


def audit(out: Path) -> dict:
    plan = checked_plan(out)
    _, prior_model, prior_sha = prior_calibration()
    cases = read_cases(out, plan)
    saved = json.loads((out / "heldout-score.json").read_bytes())
    expected = {"schema": SCHEMA, "phase": "no-refit-heldout-transfer",
                "plan_sha256": s31.file_hash(out / "plan.json"),
                "prior_calibration_sha256": prior_sha,
                "heldout_report_sha256": s31.file_hash(out / "heldout-report.json"),
                **score(prior_model["model"], cases)}
    if saved != expected:
        raise ValueError("held-out score does not reproduce from frozen prior model")
    replayed = 0
    for label, trials in cases.items():
        directory = out / "heldout" / label
        package = directory / "package"
        manifest = json.loads((package / "manifest.json").read_bytes())
        verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        key_path = package / "verification-key.json"
        for sample, _ in enumerate(trials):
            trial_dir = directory / "trials" / f"{sample:03}"
            proof = trial_dir / "proof.bin"
            s31.invoke(str(verifier), str(proof), str(trial_dir / "statement.json"), str(key_path))
            try:
                s31.invoke(str(verifier), str(proof), str(trial_dir / "changed-statement.json"), str(key_path))
            except RuntimeError:
                pass
            else:
                raise ValueError("native verifier accepted changed public claim")
            replayed += 1
    result = {"schema": SCHEMA, "phase": "native-replay-audit",
              "plan_sha256": s31.file_hash(out / "plan.json"),
              "prior_calibration_sha256": prior_sha,
              "heldout_score_sha256": s31.file_hash(out / "heldout-score.json"),
              "replayed_accepted_proofs": replayed,
              "replayed_rejected_changed_claims": replayed}
    s31.write_json(out / "audit.json", result)
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("plan", "heldout", "audit"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    out = args.out.resolve()
    if args.phase == "plan":
        create_plan(out)
    elif args.phase == "heldout":
        run_heldout(out)
    else:
        audit(out)
    print(out / ("plan.json" if args.phase == "plan" else
                 "heldout-score.json" if args.phase == "heldout" else "audit.json"))


if __name__ == "__main__":
    main()
