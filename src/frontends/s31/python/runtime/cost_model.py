"""Observed, process-inclusive cost evidence for native S31 proofs.

This module deliberately reports measurements rather than fitting an AIR-row
formula to a small corpus.  A future predictor can consume these records once
its error has been checked against held-out programs and witnesses.
"""

from __future__ import annotations

import math
import platform
import re
import statistics
import subprocess
import tempfile
import time
from pathlib import Path

from package.context import ROOT


def measured_invoke(*args: str) -> dict:
    """Run one command, measuring wall time and OS-reported peak child RSS.

    `/usr/bin/time` measures the command's process tree, unlike a sampled RSS
    poll.  If the host has no supported implementation, RSS stays unavailable.
    Its small wrapper cost is included in wall time and disclosed by the method.
    """
    system = platform.system()
    time_tool = Path("/usr/bin/time")
    method = "unavailable"
    with tempfile.TemporaryDirectory(prefix="s31-process-cost-") as directory:
        report = Path(directory) / "resource.txt"
        command = list(args)
        if time_tool.is_file() and system == "Darwin":
            command = [str(time_tool), "-l", "-o", str(report), *command]
            method = "darwin-time-max-rss-bytes"
        elif time_tool.is_file() and system == "Linux":
            command = [str(time_tool), "-f", "%M", "-o", str(report), *command]
            method = "gnu-time-max-rss-kib"
        started = time.perf_counter()
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        wall = time.perf_counter() - started
        if result.returncode:
            raise RuntimeError(f"{' '.join(args)} failed ({result.returncode})\n{result.stdout}{result.stderr}")
        peak = None
        if report.is_file():
            resource = report.read_text()
            if system == "Darwin":
                matched = re.search(r"^\s*(\d+)\s+maximum resident set size\s*$", resource, re.M)
                if matched:
                    peak = int(matched.group(1))
            elif system == "Linux":
                matched = re.fullmatch(r"\s*(\d+)\s*", resource)
                if matched:
                    peak = int(matched.group(1)) * 1024
        if peak is None:
            method = "unavailable"
        return {
            "output": result.stdout + result.stderr,
            "wall_seconds": wall,
            "peak_rss_bytes": peak,
            "peak_rss_method": method,
        }


def distribution(values: list[float | int]) -> dict | None:
    """Describe observed values; never substitute zero for missing stages."""
    if not values:
        return None
    if not all(math.isfinite(value) and value >= 0 for value in values):
        raise ValueError("cost observations must be finite and nonnegative")
    ordered = sorted(values)
    middle = statistics.median(ordered)
    p90_rank = 0.9 * (len(ordered) - 1)
    lo = int(p90_rank)
    p90 = ordered[lo] + (ordered[min(lo + 1, len(ordered) - 1)] - ordered[lo]) * (p90_rank - lo)
    return {
        "observations": len(ordered),
        "min": ordered[0],
        "median": middle,
        "max": ordered[-1],
        "median_absolute_deviation": statistics.median(abs(value - middle) for value in ordered),
        "p90_interpolated": p90,
    }


def observed_cost_model(trials: list[dict]) -> dict:
    """Account for each measured stage, process boundary, memory and bytes.

    The paired end-to-end sum includes native verification, but excludes
    package compilation, Python oracle/inspection and changed-claim controls.
    Every trial invokes a new prover, so `setup` is cold on every observation.
    """
    if not trials:
        raise ValueError("a cost model needs at least one verified trial")
    if not all(item.get("native_verifier_accepted") is True for item in trials):
        raise ValueError("a cost model requires verified proofs")

    def process_unattributed(item: dict) -> float | None:
        runtime_total = (item.get("prover_stages") or {}).get("total_through_verification_seconds")
        if runtime_total is None:
            return None
        residual = item["prove_seconds"] - runtime_total
        if residual < -0.003:
            raise ValueError("native runtime total exceeds observed prover process wall")
        return max(0.0, residual)

    fields = {
        "prove_process_wall_seconds": lambda item: item.get("prove_seconds"),
        "native_verify_process_wall_seconds": lambda item: item.get("verify_seconds"),
        "paired_prove_and_verify_wall_seconds": lambda item: item["prove_seconds"] + item["verify_seconds"],
        "proof_bytes": lambda item: item.get("proof_bytes"),
        "prover_peak_rss_bytes": lambda item: item.get("prover_peak_rss_bytes"),
        "verifier_peak_rss_bytes": lambda item: item.get("verifier_peak_rss_bytes"),
    }
    for stage in ("witness_seconds", "setup_seconds", "prove_seconds",
                  "interaction_pow_seconds", "fri_pow_seconds",
                  "prove_excluding_pow_seconds", "total_through_verification_seconds",
                  "runtime_other_seconds"):
        fields[f"runtime_{stage}"] = lambda item, stage=stage: (item.get("prover_stages") or {}).get(stage)
    fields["prover_process_unattributed_seconds"] = process_unattributed
    summaries = {}
    for name, getter in fields.items():
        values = [value for item in trials if (value := getter(item)) is not None]
        summaries[name] = distribution(values)
    return {
        "schema": "s31-observed-whole-prover-cost-v1",
        "verified_trials": len(trials),
        "metrics": summaries,
        "measurement_policy": {
            "setup": "cold native setup in every fresh prover process",
            "proof_of_work": "included in prover process wall and runtime prove; separately reported only when native timers exist",
            "process_wall": "includes process startup and resource-wrapper overhead",
            "peak_rss": "OS high-water mark for one native process tree; null if unavailable",
            "paired_total": "prover process wall plus native verifier process wall, excluding package build and audit utilities",
            "uncertainty": "median, median absolute deviation and interpolated p90 describe this observed corpus only",
        },
    }
