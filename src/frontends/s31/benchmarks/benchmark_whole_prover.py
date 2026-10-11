#!/usr/bin/env python3
"""Native process-inclusive cost corpus: arithmetic, hash, fixed-width math.

This is observational evidence.  It does not fit a cross-program predictor or
choose an AIR automatically.  All samples have distinct valid witnesses.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import struct
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE / "python"))

import s31
from runtime.cost_model import observed_cost_model

P = (1 << 31) - 1


def digest(words: list[int], person: bytes) -> list[int]:
    raw = hashlib.blake2s(b"".join(struct.pack("<I", word) for word in words), person=person).digest()
    return [word % P for word in struct.unpack("<8I", raw)]


def arithmetic_assignment(index: int) -> dict:
    values = [index + 1, index + 2, index + 3, index + 11]
    return {"public_inputs": {}, "private_inputs": {"x": values},
            "public_outputs": {"result": [(value * value + 2 * value) % P for value in values]}}


def hash_assignment(index: int) -> dict:
    left = [index * 17 + j + 1 for j in range(8)]
    right = [index * 19 + j + 101 for j in range(8)]
    root = digest(digest(left, b"S31LEAF1") + digest(right, b"S31LEAF1"), b"S31PAIR1")
    return {"public_inputs": {}, "private_inputs": {"left": left, "right": right},
            "public_outputs": {"root": root}}


def cases(samples: int) -> list[tuple[str, Path, str, list[dict]]]:
    fixtures = sorted((HERE / "examples/math/division/fixtures/i32").glob("*.json"))
    if samples > len(fixtures):
        raise ValueError(f"i32 fixture corpus has only {len(fixtures)} distinct assignments")
    return [
        ("arithmetic_record", HERE / "examples/arithmetic/record_square_sum.s31", "direct-gate",
         [arithmetic_assignment(index) for index in range(samples)]),
        ("blake2s_merkle", HERE / "examples/hashes/merkle2.s31.json", "gate",
         [hash_assignment(index) for index in range(samples)]),
        ("signed_i32_division", HERE / "examples/math/division/i32_div_rem.s31", "direct-gate",
         [json.loads(path.read_text()) for path in fixtures[:samples]]),
    ]


def measured_package_build(source: Path, package_path: Path, lowering: str,
                           builder=None) -> tuple[Path, dict]:
    """Time package materialization; disclose reuse and uncontrolled Zig cache."""
    build_package = s31.build if builder is None else builder
    package_existed = package_path.exists()
    started = time.perf_counter()
    package = build_package(source, package_path, lowering)
    wall_seconds = time.perf_counter() - started
    return package, {
        "package_build_wall_seconds": wall_seconds,
        "package_reused": package_existed,
        "zig_compiler_cache": "uncontrolled host cache; no cache clearing or isolation",
        "package_build_peak_rss_bytes": None,
        "package_build_peak_rss_method": "unavailable: Python build invokes Zig subprocesses",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=3, help="distinct witnesses per workload (1..5)")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if not 1 <= args.samples <= 5:
        parser.error("--samples must be between 1 and 5")
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    results = {}
    for name, source, lowering, assignments in cases(args.samples):
        package, build_measurement = measured_package_build(
            source, output / name / "package", lowering)
        trials = []
        for index, assignment in enumerate(assignments):
            assignment_path = output / name / "assignments" / f"{index:02d}.json"
            assignment_path.parent.mkdir(parents=True, exist_ok=True)
            s31.write_json(assignment_path, assignment)
            trials.append(s31.trial(package, assignment_path, output / name / "trials" / f"{index:02d}"))
        cost = json.loads((package / "cost-report.json").read_text())
        results[name] = {
            "source": str(source.relative_to(s31.ROOT)),
            "source_sha256": s31.file_hash(source),
            "lowering": lowering,
            "profile": cost["profile"],
            "raw": cost["raw"],
            "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "package_build": build_measurement,
            "assignment_sha256": [s31.assignment_digest(output / name / "assignments" / f"{index:02d}.json")
                                  for index in range(args.samples)],
            "observed_cost_model": observed_cost_model(trials),
        }
        print(f"{name}: {args.samples} native proofs verified", flush=True)
    report = {
        "schema": "s31-whole-prover-corpus-v2",
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(), "zig": s31.invoke("zig", "version").strip()},
        "samples_per_case": args.samples,
        "scope": "Fresh prover and verifier processes for distinct valid witnesses; native setup is cold on every sample. No extrapolation or soundness equivalence claim.",
        "cases": results,
    }
    s31.write_json(output / "whole-prover-report.json", report)
    print(output / "whole-prover-report.json")


if __name__ == "__main__":
    main()
