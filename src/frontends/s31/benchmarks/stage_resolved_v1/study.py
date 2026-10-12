#!/usr/bin/env python3
"""Prospective lagged-alternating test of a sealed stage-resolved cost model."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from extract_history import components  # noqa: E402
from model import COUNTS, LIMITS, STAGES, TARGETS, evaluate, fit, sha  # noqa: E402

P = (1 << 31) - 1
SCHEMA = "s31-stage-resolved-prospective-v1"
SAMPLES = 12
ROWS = {96: 512, 256: 1024, 448: 1024}
LEDGER = HERE / "historical-stage-ledger.json"
CALIBRATION = HERE / "calibration.json"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True).encode()


def source_for(count: int) -> str:
    if count not in COUNTS:
        raise ValueError("gate count is outside the prospective roster")
    statements = ["let p1 = x .* x;", "let p2 = x + p1;"]
    for index in range(3, count + 1):
        symbol = "+" if index % 2 == 0 else ".*"
        statements.append(f"let p{index} = p{index - 2} {symbol} p{index - 1};")
    return (f"circuit lagged_alternating_{count}(public x: [m31; 4]) "
            "-> public [m31; 4] {\n    " + "\n    ".join(statements) +
            f"\n    p{count}\n}}\n")


def assignment_for(count: int, sample: int) -> dict:
    if count not in COUNTS or not 0 <= sample < SAMPLES:
        raise ValueError("assignment is outside the prospective roster")
    words = ([P - 2, P - 1, 0, 1] if sample == 0 else
             [sample * 29 + count * 11 + lane * lane + 5
              for lane in range(4)])
    a = [(value * value) % P for value in words]
    b = [(value + squared) % P for value, squared in zip(words, a, strict=True)]
    for index in range(3, count + 1):
        a, b = b, [((left + right) if index % 2 == 0 else left * right) % P
                   for left, right in zip(a, b, strict=True)]
    return {"public_inputs": {"x": words}, "private_inputs": {},
            "public_outputs": {f"p{count}": b}}


def inventory() -> dict:
    return {str(count): {
        "source_sha256": digest(source_for(count).encode()),
        "assignment_sha256": [digest(canonical(assignment_for(count, sample)))
                              for sample in range(SAMPLES)],
        "expected_padded_qm31_rows": ROWS[count],
    } for count in COUNTS}


def historical_calibration() -> tuple[dict, dict]:
    ledger = json.loads(LEDGER.read_bytes())
    calibration = json.loads(CALIBRATION.read_bytes())
    expected = fit(ledger, sha(LEDGER), sha(HERE / "model.py"))
    if calibration != expected:
        raise ValueError("historical stage calibration differs from frozen inputs or model code")
    return ledger, calibration


def identity() -> dict:
    engine = subprocess.check_output(
        ["git", "-C", str(ROOT / "deps/stwo-zig"), "rev-parse", "HEAD"],
        text=True).strip()
    return {
        "compiler_sha256": s31.compiler_fingerprint(),
        "engine_commit": engine,
        "study_sha256": sha(Path(__file__)),
        "model_sha256": sha(HERE / "model.py"),
        "history_extractor_sha256": sha(HERE / "extract_history.py"),
        "independent_scorer_sha256": sha(HERE / "independent_score.py"),
        "independent_oracle_provenance": s31.oracle_provenance(),
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(),
                 "zig": s31.invoke("zig", "version").strip()},
    }


def plan_payload() -> dict:
    history, calibration = historical_calibration()
    current = identity()
    for field in ("compiler_sha256", "engine_commit", "host"):
        if current[field] != history[field] or current[field] != calibration[field]:
            raise ValueError("new prospective study needs historical compiler, engine, and host")
    return {
        "schema": SCHEMA, "phase": "sealed-before-new-family-native-build",
        "identity": current,
        "historical_stage_ledger_sha256": sha(LEDGER),
        "calibration_sha256": sha(CALIBRATION),
        "family": "lagged-alternating-two-prior-wires",
        "counts": list(COUNTS), "samples_per_program": SAMPLES,
        "sources": inventory(), "lowering": "direct-gate",
        "stage_names": list(STAGES), "targets": list(TARGETS),
        "diagnostic_limits": LIMITS,
        "prediction_rule": "Frozen per-gate stage medians from alternating+add sources; first-use process residual separately modeled; whole-target first/later ratio bands calibrated only from all-multiply sources. No held-out refit.",
        "scope": "One host/compiler/engine direct-gate heldout topology; >16 gates outside bounded release correspondence certificate; no automatic lowering decision.",
    }


def checked_plan(out: Path) -> dict:
    saved = json.loads((out / "plan.json").read_bytes())
    if saved != plan_payload():
        raise ValueError("sealed plan, calibration, compiler, host, or source changed")
    return saved


def create_plan(out: Path) -> None:
    if out.exists():
        raise FileExistsError("plan needs a fresh output directory")
    out.mkdir(parents=True)
    s31.write_json(out / "plan.json", plan_payload())


def read_cases(out: Path, plan: dict) -> list[dict]:
    programs = []
    for count in COUNTS:
        directory = out / "heldout" / f"gates-{count}"
        source = directory / f"lagged_alternating_{count}.s31"
        if sha(source) != plan["sources"][str(count)]["source_sha256"]:
            raise ValueError("saved source differs from plan")
        package = directory / "package"
        manifest = s31.verify_package(package)
        if (manifest["compiler_sha256"] != plan["identity"]["compiler_sha256"] or
                manifest["lowering"] != "direct-gate"):
            raise ValueError("saved package compiler or lowering differs")
        cost = json.loads((package / "cost-report.json").read_bytes())
        if cost["padded"]["qm31_ops"] != ROWS[count]:
            raise ValueError("native padded geometry differs from plan")
        trials = []
        for sample in range(SAMPLES):
            assignment = directory / "assignments" / f"{sample:03}.json"
            if s31.assignment_digest(assignment) != plan["sources"][str(count)]["assignment_sha256"][sample]:
                raise ValueError("saved assignment differs from plan")
            trial_dir = directory / "trials" / f"{sample:03}"
            report_path = trial_dir / "trial-report.json"
            report = json.loads(report_path.read_bytes())
            if (sha(trial_dir / "proof.bin") != report["proof_sha256"] or
                    report["padded"]["qm31_ops"] != ROWS[count] or
                    report.get("independent_value_oracle_provenance") !=
                    plan["identity"]["independent_oracle_provenance"]):
                raise ValueError("saved proof, geometry, or oracle provenance differs")
            trials.append({
                "sample": sample,
                "trial_report_sha256": sha(report_path),
                "proof_sha256": report["proof_sha256"],
                "stages_seconds": components(report),
                "first_verified_wall_seconds": report["prove_seconds"] + report["verify_seconds"],
                "proof_bytes": report["proof_bytes"],
                "prover_peak_rss_bytes": report["prover_peak_rss_bytes"],
            })
        programs.append({
            "gates": count,
            "source_sha256": sha(source),
            "raw_qm31_rows": cost["raw"]["qm31_ops"],
            "padded_qm31_rows": cost["padded"]["qm31_ops"],
            "trials": trials,
        })
    return programs


def run_heldout(out: Path) -> None:
    plan = checked_plan(out)
    if (out / "heldout").exists() or (out / "heldout-score.json").exists():
        raise FileExistsError("heldout evidence already exists")
    _, calibration = historical_calibration()
    if sha(CALIBRATION) != plan["calibration_sha256"]:
        raise ValueError("calibration changed before native build")
    phase = out / "heldout"
    phase.mkdir()
    builds = {}
    for count in COUNTS:
        directory = phase / f"gates-{count}"
        directory.mkdir()
        source = directory / f"lagged_alternating_{count}.s31"
        source.write_text(source_for(count))
        started = time.perf_counter()
        package = s31.build(source, directory / "package", "direct-gate")
        builds[str(count)] = time.perf_counter() - started
        cost = json.loads((package / "cost-report.json").read_bytes())
        if cost["padded"]["qm31_ops"] != ROWS[count]:
            raise ValueError("native padded geometry differs from frozen plan")
        for sample in range(SAMPLES):
            assignment = directory / "assignments" / f"{sample:03}.json"
            assignment.parent.mkdir(exist_ok=True)
            s31.write_json(assignment, assignment_for(count, sample))
            s31.trial(package, assignment, directory / "trials" / f"{sample:03}")
        print(f"heldout: {count} lagged gates, {SAMPLES} verified proofs", flush=True)
    cases = read_cases(out, plan)
    report = {
        "schema": SCHEMA, "phase": "heldout",
        "plan_sha256": sha(out / "plan.json"),
        "calibration_sha256": sha(CALIBRATION),
        "package_build_wall_seconds": builds,
        "cases": {str(p["gates"]): {
            "source_sha256": p["source_sha256"],
            "package_manifest_sha256": sha(phase / f"gates-{p['gates']}" /
                                           "package" / "manifest.json"),
            "raw_qm31_rows": p["raw_qm31_rows"],
            "padded_qm31_rows": p["padded_qm31_rows"],
            "proof_sha256": [t["proof_sha256"] for t in p["trials"]],
            "trial_report_sha256": [t["trial_report_sha256"] for t in p["trials"]],
        } for p in cases},
    }
    s31.write_json(out / "heldout-report.json", report)
    result = evaluate(calibration, cases)
    s31.write_json(out / "heldout-score.json", {
        "schema": SCHEMA, "phase": "no-refit-new-family-heldout",
        "plan_sha256": sha(out / "plan.json"),
        "calibration_sha256": sha(CALIBRATION),
        "heldout_report_sha256": sha(out / "heldout-report.json"),
        "evaluation": result,
    })


def audit(out: Path) -> dict:
    plan = checked_plan(out)
    _, calibration = historical_calibration()
    cases = read_cases(out, plan)
    saved = json.loads((out / "heldout-score.json").read_bytes())
    expected = {"schema": SCHEMA, "phase": "no-refit-new-family-heldout",
                "plan_sha256": sha(out / "plan.json"),
                "calibration_sha256": sha(CALIBRATION),
                "heldout_report_sha256": sha(out / "heldout-report.json"),
                "evaluation": evaluate(calibration, cases)}
    if saved != expected:
        raise ValueError("saved score does not reproduce from frozen calibration")
    replayed = 0
    for program in cases:
        count = program["gates"]
        directory = out / "heldout" / f"gates-{count}"
        package = directory / "package"
        manifest = json.loads((package / "manifest.json").read_bytes())
        verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        key = package / "verification-key.json"
        for sample in range(SAMPLES):
            trial_dir = directory / "trials" / f"{sample:03}"
            proof = trial_dir / "proof.bin"
            s31.invoke(str(verifier), str(proof), str(trial_dir / "statement.json"), str(key))
            try:
                s31.invoke(str(verifier), str(proof),
                           str(trial_dir / "changed-statement.json"), str(key))
            except RuntimeError:
                pass
            else:
                raise ValueError("native verifier accepted changed public statement")
            replayed += 1
    result = {
        "schema": SCHEMA, "phase": "native-replay-audit",
        "plan_sha256": sha(out / "plan.json"),
        "calibration_sha256": sha(CALIBRATION),
        "heldout_score_sha256": sha(out / "heldout-score.json"),
        "replayed_accepted_proofs": replayed,
        "replayed_rejected_changed_claims": replayed,
    }
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
