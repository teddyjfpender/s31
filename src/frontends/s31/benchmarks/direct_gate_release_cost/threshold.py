#!/usr/bin/env python3
"""Measure an equivalent addition chain on opposite sides of a Gate AIR pad boundary.

The fast source uses an erasable pure helper and fits the bounded direct-gate
certificate. The 193-gate linear source is an ordinary native package outside
that certificate. This measures an algorithmic difference, not a compiler
optimization or a general predictor.
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
from package.correspondence import parse_source
from runtime.cost_model import distribution, observed_cost_model
from text_frontend import compile_text

P = (1 << 31) - 1


def chain_source(*, helper: bool) -> str:
    prefix = "fn double(a: [m31; 4]) -> [m31; 4] { a + a }\n" if helper else ""
    doubling = ("double(x)", "double(v2)", "double(v4)", "double(v8)",
                "double(v16)", "double(v32)", "double(v64)") if helper else (
                "x + x", "v2 + v2", "v4 + v4", "v8 + v8", "v16 + v16",
                "v32 + v32", "v64 + v64")
    lines = ["circuit scale194(public x: [m31; 4]) -> public [m31; 4] {"]
    for power, expression in zip((2, 4, 8, 16, 32, 64, 128), doubling, strict=True):
        lines.append(f"    let v{power} = {expression};")
    lines.extend(("    let v192 = v64 + v128;", "    let out = v2 + v192;",
                  "    out", "}"))
    return prefix + "\n".join(lines) + "\n"


def linear_source() -> str:
    lines = ["circuit linear194(public x: [m31; 4]) -> public [m31; 4] {"]
    lines.append("    let v1 = x + x;")
    lines.extend(f"    let v{i} = v{i-1} + x;" for i in range(2, 194))
    lines.extend(("    v193", "}"))
    return "\n".join(lines) + "\n"


def assignment(sample: int, output_name: str) -> dict:
    if sample < 0:
        raise ValueError("sample must be nonnegative")
    values = ([0, 1, P - 1, P - 2] if sample == 0 else
              [((sample * 7919 + lane * 104729 + 7) % P) for lane in range(4)])
    return {"public_inputs": {"x": values}, "private_inputs": {},
            "public_outputs": {output_name: [(194 * value) % P for value in values]}}


def _median(metrics: dict, key: str) -> float | int | None:
    value = metrics[key]
    return None if value is None else value["median"]


def measure(samples: int, output: Path) -> dict:
    if samples < 1:
        raise ValueError("at least one sample is required")
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    checked, checked_syntax = parse_source(chain_source(helper=True).encode())
    flat, flat_syntax = parse_source(chain_source(helper=False).encode())
    if checked != flat or checked_syntax != flat_syntax or checked != compile_text(
            chain_source(helper=True))[0] or len(checked["nodes"]) != 9:
        raise ValueError("pure helper did not erase to the independently checked nine-gate relation")

    cases = {}
    for name, source_text, output_name, expected_rows, certified in (
            ("addition-chain", chain_source(helper=True), "out", 512, True),
            ("linear-chain", linear_source(), "v193", 1024, False)):
        case_dir = output / name
        case_dir.mkdir(parents=True, exist_ok=True)
        source = case_dir / f"{name}.s31"
        source.write_text(source_text)
        started = time.perf_counter()
        package = s31.build(source, case_dir / "package", "direct-gate")
        build_wall = time.perf_counter() - started
        cost = json.loads((package / "cost-report.json").read_text())
        manifest = json.loads((package / "manifest.json").read_text())
        if cost["padded"]["qm31_ops"] != expected_rows:
            raise ValueError(f"{name}: unexpected padded trace size")
        if ("correspondence-certificate.json" in manifest["artifacts"]) != certified:
            raise ValueError(f"{name}: unexpected correspondence certificate status")
        trials = []
        for sample in range(samples):
            assignment_path = case_dir / "assignments" / f"{sample:03d}.json"
            assignment_path.parent.mkdir(parents=True, exist_ok=True)
            s31.write_json(assignment_path, assignment(sample, output_name))
            trials.append(s31.trial(package, assignment_path,
                                    case_dir / "trials" / f"{sample:03d}"))
        if any(trial["native_verifier_accepted"] is not True or
               not trial["changed_public_statement_rejected"] or
               trial["independent_value_oracle"]["status"] != "passed"
               for trial in trials):
            raise ValueError(f"{name}: failed proof or negative control")
        after_pow = []
        for trial in trials:
            stages = trial.get("prover_stages") or {}
            if stages.get("interaction_pow_seconds") is not None and stages.get(
                    "fri_pow_seconds") is not None:
                after_pow.append(trial["prove_seconds"] + trial["verify_seconds"] -
                                 stages["interaction_pow_seconds"] -
                                 stages["fri_pow_seconds"])
        measured = observed_cost_model(trials)["metrics"]
        cases[name] = {
            "source_sha256": s31.file_hash(source),
            "manifest_sha256": s31.file_hash(package / "manifest.json"),
            "compiler_sha256": manifest.get("compiler_sha256"),
            "certified_source_correspondence": certified,
            "package_build_wall_seconds": build_wall,
            "cost": {key: cost[key] for key in ("raw", "padded", "preprocessed_cells", "fri")},
            "proof_sha256": [trial["proof_sha256"] for trial in trials],
            "trial_report_sha256": [s31.file_hash(
                case_dir / "trials" / f"{sample:03d}" / "trial-report.json")
                for sample in range(samples)],
            "paired_wall_median_seconds": _median(measured, "paired_prove_and_verify_wall_seconds"),
            "wall_after_reported_pow": (distribution(after_pow)
                                        if len(after_pow) == samples else None),
            "proof_bytes_median": _median(measured, "proof_bytes"),
            "prover_rss_median_bytes": _median(measured, "prover_peak_rss_bytes"),
        }
        print(f"{name}: {samples} verified native proofs", flush=True)
    report = {
        "schema": "s31-direct-gate-addition-chain-threshold-v1",
        "status": "exploratory-local-observation",
        "scope": ("Equivalent four-lane 194*x functions on one host; 9-gate addition chain "
                  "is source-certified, 193-gate linear chain is outside the bounded "
                  "certificate. Each proof uses a fresh native prover and verifier. "
                  "PoW-adjusted wall is timer subtraction, not a separate execution mode."),
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(), "zig": s31.invoke("zig", "version").strip()},
        "samples_per_case": samples,
        "script_sha256": s31.file_hash(Path(__file__)),
        "cases": cases,
    }
    s31.write_json(output / "threshold-report.json", report)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--samples", type=int, default=12)
    args = parser.parse_args()
    measure(args.samples, args.out)
    print(args.out.resolve() / "threshold-report.json")


if __name__ == "__main__":
    main()
