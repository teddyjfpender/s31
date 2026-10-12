"""Benchmark-only, balanced-order native profile trials.

This lives outside the compiler fingerprint. It uses the production package,
trial, and observed-cost APIs without changing their semantics.
"""

from __future__ import annotations

import json
import platform
import statistics
import time
from pathlib import Path

import s31
from runtime.cost_model import observed_cost_model


def tune_interleaved(source: Path, assignments: list[Path], output: Path,
                     lowerings: tuple[str, str], before_trials=None) -> dict:
    if len(lowerings) != 2 or len(set(lowerings)) != 2 or not assignments:
        raise ValueError("paired tune requires two distinct lowerings and assignments")
    source = source.resolve()
    assignments = [path.resolve() for path in assignments]
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / "tune-report.json").unlink(missing_ok=True)
    digests = [s31.assignment_digest(path) for path in assignments]
    if len(set(digests)) != len(digests):
        raise ValueError("paired tune requires distinct assignments")
    packages = {}
    build_seconds = {}
    manifests = {}
    for lowering in lowerings:
        started = time.perf_counter()
        packages[lowering] = s31.build(source, output / "packages" / lowering, lowering)
        build_seconds[lowering] = time.perf_counter() - started
        manifests[lowering] = s31.verify_package(packages[lowering])
    programs = {manifest["program_sha256"] for manifest in manifests.values()}
    relations = {manifest["canonical_ir_sha256"] for manifest in manifests.values()}
    if len(programs) != 1 or len(relations) != 1:
        raise ValueError("paired profiles compiled different canonical relations")
    if before_trials is not None:
        # A prospective caller may seal predictions using package geometry
        # here, before warmup or any measured native proof process starts.
        before_trials(packages, manifests)
    for lowering in lowerings:
        s31.trial(packages[lowering], assignments[0], output / "warmup" / lowering)
    trials = {lowering: [] for lowering in lowerings}
    schedule = []
    for index, assignment in enumerate(assignments):
        order = lowerings if index % 2 == 0 else lowerings[::-1]
        for lowering in order:
            trial = s31.trial(packages[lowering], assignment,
                              output / "runs" / lowering / f"{index:03d}")
            trials[lowering].append(trial)
            schedule.append({"assignment_index": index, "lowering": lowering})
    profiles = {}
    for lowering in lowerings:
        package = packages[lowering]
        cost = json.loads((package / "cost-report.json").read_text())
        rows = trials[lowering]
        sizes = [row["proof_bytes"] for row in rows]
        prove = [row["prove_seconds"] for row in rows]
        verify = [row["verify_seconds"] for row in rows]
        non_pow = [(row.get("prover_stages") or {}).get("prove_excluding_pow_seconds")
                   for row in rows]
        profiles[lowering] = {
            "package": str(package),
            "build_or_load_seconds": build_seconds[lowering],
            "profile": cost["profile"],
            "visible_fri": s31.visible_fri(cost, lowering),
            "public_abi": json.loads((package / "public-abi.json").read_text()),
            "raw": cost["raw"], "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "proof_bytes_per_assignment": sizes,
            "median_proof_bytes": statistics.median(sizes),
            "wall_prove_seconds_per_assignment": prove,
            "median_wall_prove_seconds": statistics.median(prove),
            "native_verify_seconds_per_assignment": verify,
            "median_native_verify_seconds": statistics.median(verify),
            "prove_excluding_pow_seconds_per_assignment": (
                non_pow if all(value is not None for value in non_pow) else []),
            "median_prove_excluding_pow_seconds": (
                statistics.median(non_pow) if all(value is not None for value in non_pow)
                else None),
            "native_verifier_accepted_all": all(row["native_verifier_accepted"] is True
                                                for row in rows),
            "changed_public_statement_rejected_all": all(
                bool(row["changed_public_statement_rejected"]) for row in rows),
            "independent_value_oracle_statuses": [
                row["independent_value_oracle"]["status"] for row in rows],
            "observed_cost_model": observed_cost_model(rows),
        }
    fri = {json.dumps(row["visible_fri"], sort_keys=True)
           for row in profiles.values()}
    report = {
        "schema": "s31-tune-v1", "source": str(source),
        "program_sha256": next(iter(programs)),
        "canonical_ir_sha256": next(iter(relations)),
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(),
                 "zig": s31.invoke("zig", "version").strip()},
        "assignment_sha256": digests,
        "distinct_assignment_count": len(digests), "distinct_assignments": True,
        "warmup_assignment_sha256": digests[0],
        "independent_value_oracle_provenance": s31.oracle_provenance(),
        "same_visible_fri_settings": len(fri) == 1,
        "profiles": profiles,
        "measurement_order": "alternating-by-assignment-v1",
        "trial_schedule": schedule,
        "timing_note": ("Fresh native prover and verifier processes for each assignment. "
                        "Within each assignment, direct/sparse order alternates by index. "
                        "Warmups use separate processes. Proof-of-work and external host load "
                        "remain variable; visible FRI equality does not prove equal soundness."),
    }
    s31.write_json(output / "tune-report.json", report)
    return report
