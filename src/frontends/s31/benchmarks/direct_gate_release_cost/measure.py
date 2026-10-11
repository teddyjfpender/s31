#!/usr/bin/env python3
"""Exploratory whole-process measurements for the 1–16-gate text fragment.

This is a fresh local observation, separate from the frozen V8r1 cost study.
It does not fit a predictor or enable automatic lowering. Each sample proves
a distinct four-lane assignment in fresh native prover and verifier processes.
"""

from __future__ import annotations

import argparse
import json
import platform
import sys
import time
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31
from runtime.cost_model import distribution, observed_cost_model

P = (1 << 31) - 1


def source_for(gates: int) -> str:
    if not 1 <= gates <= 16:
        raise ValueError("bounded direct-gate fragment needs 1–16 gates")
    statements = ["let p1 = x .* x;"]
    for index in range(2, gates + 1):
        operation = "+" if index % 2 == 0 else ".*"
        statements.append(f"let p{index} = x {operation} p{index - 1};")
    return (f"circuit exploratory_{gates}(public x: [m31; 4]) "
            "-> public [m31; 4] {\n    " + "\n    ".join(statements) +
            f"\n    p{gates}\n}}\n")


def output_for(gates: int, values: list[int]) -> list[int]:
    result = [(value * value) % P for value in values]
    for index in range(2, gates + 1):
        result = [((current + value) if index % 2 == 0 else
                   (current * value)) % P
                  for current, value in zip(result, values, strict=True)]
    return result


def assignment_for(gates: int, sample: int) -> dict:
    values = [sample * 17 + lane + 2 for lane in range(4)]
    return {"public_inputs": {"x": values}, "private_inputs": {},
            "public_outputs": {f"p{gates}": output_for(gates, values)}}


def measure(counts: tuple[int, ...], samples: int, output: Path) -> dict:
    if samples < 1 or len(counts) != len(set(counts)) or not all(1 <= n <= 16 for n in counts):
        raise ValueError("requires positive samples and distinct gate counts in 1–16")
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    results = {}
    for gates in counts:
        case_dir = output / f"gates-{gates:02d}"
        case_dir.mkdir(parents=True, exist_ok=True)
        source = case_dir / f"exploratory_{gates}.s31"
        source.write_text(source_for(gates))
        package_reused = (case_dir / "package").exists()
        started = time.perf_counter()
        package = s31.build(source, case_dir / "package", "direct-gate")
        build_wall = time.perf_counter() - started
        cost = json.loads((package / "cost-report.json").read_text())
        manifest = json.loads((package / "manifest.json").read_text())
        trials = []
        assignment_hashes = []
        for sample in range(samples):
            assignment = case_dir / "assignments" / f"{sample:03d}.json"
            assignment.parent.mkdir(parents=True, exist_ok=True)
            s31.write_json(assignment, assignment_for(gates, sample))
            assignment_hashes.append(s31.assignment_digest(assignment))
            trials.append(s31.trial(package, assignment,
                                    case_dir / "trials" / f"{sample:03d}"))
        if any(trial["native_verifier_accepted"] is not True or
               trial["independent_value_oracle"]["status"] != "passed" or
               not trial["changed_public_statement_rejected"] for trial in trials):
            raise ValueError("exploratory cost trial lacks a verification control")
        after_pow = []
        for trial in trials:
            stages = trial.get("prover_stages") or {}
            if (stages.get("interaction_pow_seconds") is not None and
                stages.get("fri_pow_seconds") is not None):
                after_pow.append(trial["prove_seconds"] + trial["verify_seconds"] -
                                 stages["interaction_pow_seconds"] -
                                 stages["fri_pow_seconds"])
        results[str(gates)] = {
            "source": source.relative_to(output).as_posix(),
            "source_sha256": s31.file_hash(source),
            "package_manifest_sha256": s31.file_hash(package / "manifest.json"),
            "compiler_sha256": manifest.get("compiler_sha256"),
            "assignment_sha256": assignment_hashes,
            "proof_sha256": [trial["proof_sha256"] for trial in trials],
            "trial_report_sha256": [s31.file_hash(
                case_dir / "trials" / f"{sample:03d}" / "trial-report.json")
                for sample in range(samples)],
            "package_build_wall_seconds": build_wall,
            "package_reused": package_reused,
            "package_build_cache": "uncontrolled Zig cache",
            "cost_report": {
                "profile": cost["profile"], "raw": cost["raw"],
                "padded": cost["padded"],
                "preprocessed_cells": cost["preprocessed_cells"],
                "fri": cost["fri"],
            },
            "observed_cost_model": observed_cost_model(trials),
            "diagnostic_paired_wall_after_reported_pow_seconds": (
                distribution(after_pow) if len(after_pow) == len(trials) else None),
        }
        print(f"{gates} gates: {samples} verified fresh-process proofs", flush=True)
    comparison = []
    for gate_count, case in results.items():
        metrics = case["observed_cost_model"]["metrics"]

        def median(name: str) -> float | int | None:
            value = metrics[name]
            return None if value is None else value["median"]

        comparison.append({
            "gates": int(gate_count),
            "raw_qm31_ops_rows": case["cost_report"]["raw"]["qm31_ops"],
            "padded_qm31_ops_rows": case["cost_report"]["padded"]["qm31_ops"],
            "preprocessed_cells": case["cost_report"]["preprocessed_cells"],
            "paired_wall_median_seconds": median("paired_prove_and_verify_wall_seconds"),
            "paired_wall_after_reported_pow_median_seconds": (
                case["diagnostic_paired_wall_after_reported_pow_seconds"] or {}).get("median"),
            "proof_bytes_median": median("proof_bytes"),
            "prover_peak_rss_median_bytes": median("prover_peak_rss_bytes"),
        })
    report = {
        "schema": "s31-exploratory-bounded-direct-gate-cost-v1",
        "status": "exploratory-local-observation",
        "measurement_script_sha256": s31.file_hash(Path(__file__)),
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(),
                 "zig": s31.invoke("zig", "version").strip()},
        "scope": ("One host, generated public four-lane +/.* recurrences, fresh native "
                  "prover and verifier processes. Cost reports provide AIR geometry and "
                  "FRI parameters, not wall-time, proof-byte or RSS predictions. No "
                  "held-out calibration, extrapolation or automatic lowering. "
                  "PoW-adjusted wall is a descriptive timer subtraction, not a "
                  "measurement of a separate native process."),
        "samples_per_case": samples, "comparison": comparison, "cases": results,
    }
    s31.write_json(output / "exploratory-report.json", report)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=3)
    parser.add_argument("--gates", type=int, nargs="+", default=[1, 4, 16])
    args = parser.parse_args()
    measure(tuple(args.gates), args.samples, args.out)
    print(args.out.resolve() / "exploratory-report.json")


if __name__ == "__main__":
    main()
