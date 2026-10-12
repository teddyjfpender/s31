#!/usr/bin/env python3
"""Paired worker-count diagnostic over distinct frozen mixed-proof statements.

This is a measurement of the complete native prove interval, including setup.
It does not isolate PoW or train/validate a whole-prover cost predictor.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import statistics
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
PROTOCOL = ROOT / "design/s31/measurements/language/mixed-stage-cost-transfer-v1-protocol.json"
PROTOCOL_SHA256 = "87f0cccb359ab28501ce9f12d99e83fd2090097e16c1ab5f17d52445b664a862"
P = (1 << 31) - 1


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def unique(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def read_json(path: Path) -> dict:
    value = json.loads(path.read_bytes(), object_pairs_hook=unique)
    if type(value) is not dict:
        raise ValueError(f"JSON object required: {path}")
    return value


def preflight(package_root: Path, shapes: list[str], assignments: int,
              protocol_path: Path) -> tuple[dict, list[dict]]:
    protocol_bytes = protocol_path.read_bytes()
    protocol = json.loads(protocol_bytes, object_pairs_hook=unique)
    freeze_path = protocol_path.with_name("mixed-stage-cost-transfer-v1-freeze.json")
    freeze_bytes = freeze_path.read_bytes()
    freeze = json.loads(freeze_bytes, object_pairs_hook=unique)
    if (sha(protocol_bytes) != PROTOCOL_SHA256 or
            protocol.get("schema") != "s31-mixed-stage-cost-transfer-v1-protocol-candidate" or
            protocol.get("status") != "prepared-for-prospective-freeze" or
            not 1 <= assignments <= protocol.get("assignments_per_program", -1) or
            freeze.get("schema") != "s31-mixed-stage-cost-transfer-v1-freeze" or
            freeze.get("protocol_sha256") != sha(protocol_bytes)):
        raise ValueError("wrong frozen protocol or assignment count")
    packages = []
    for shape in shapes:
        expected = protocol["inventory"].get(shape)
        if expected is None:
            raise ValueError(f"shape is absent from frozen protocol: {shape}")
        directory = package_root / shape
        build = read_json(directory / "build.json")
        binary_dir = directory / "mixed/bin"
        binaries = {}
        for role, suffix in (("prover", "-mixed-general-prover"),
                             ("verifier", "-mixed-general-native-verifier")):
            matches = list(binary_dir.glob("*" + suffix))
            if len(matches) != 1:
                raise ValueError(f"{shape}: expected one {role} binary")
            binaries[role] = matches[0]
        identity = {role: sha(path.read_bytes()) for role, path in binaries.items()}
        if (identity != {role: build["binary_sha256"][role] for role in binaries} or
                build["source_sha256"] != expected["source_sha256"] or
                sha((directory / "source.s31.json").read_bytes()) != expected["source_sha256"]):
            raise ValueError(f"{shape}: package differs from frozen source or build")
        cases = []
        for index in range(assignments):
            assignment = directory / f"assignment-{index:02d}.json"
            statement = directory / f"statement-{index:02d}.json"
            assignment_sha = sha(assignment.read_bytes())
            statement_sha = sha(statement.read_bytes())
            if (assignment_sha != expected["assignment_sha256"][index] or
                    statement_sha != expected["typed_statement_sha256"][index]):
                raise ValueError(f"{shape}/{index}: assignment or statement differs from frozen inventory")
            cases.append({"index": index, "assignment": assignment,
                          "statement": statement, "assignment_sha256": assignment_sha,
                          "statement_sha256": statement_sha})
        if (len({case["assignment_sha256"] for case in cases}) != assignments or
                len({case["statement_sha256"] for case in cases}) != assignments):
            raise ValueError(f"{shape}: duplicate statements or assignments")
        packages.append({"shape": shape, "directory": directory, "binaries": binaries,
                         "binary_sha256": identity, "source_sha256": expected["source_sha256"],
                         "cases": cases})
    return {"sha256": sha(protocol_bytes), "freeze_sha256": sha(freeze_bytes),
            "engine_gitlink_commit": protocol["engine_gitlink_commit"],
            "compiler_sha256": protocol["compiler_sha256"]}, packages


def command(args: list[str], env: dict[str, str]) -> tuple[subprocess.CompletedProcess[bytes], int]:
    start = time.perf_counter_ns()
    result = subprocess.run(args, env=env, capture_output=True, check=False)
    return result, time.perf_counter_ns() - start


def stage_time(stderr: bytes, wall_ns: int) -> int:
    lines = [line.split(b" ", 1)[1] for line in stderr.splitlines()
             if line.startswith(b"S31_MIXED_STAGE_V1 ")]
    if len(lines) != 1:
        raise ValueError("exactly one native stage record required")
    stage = json.loads(lines[0], object_pairs_hook=unique)
    native = stage["stages_ns"]["native_prove_including_setup_ns"]
    if type(native) is not int or native <= 0 or native > wall_ns:
        raise ValueError("native prove timer is missing or exceeds process wall")
    return native


def change_result(statement: Path, out: Path) -> None:
    value = read_json(statement)
    if (value.get("version") != 2 or type(value.get("leaves")) is not list or
            len(value["leaves"]) != 2 or type(value["leaves"][-1].get("words")) is not list or
            len(value["leaves"][-1]["words"]) != 4):
        raise ValueError("expected two-leaf public record ABI v2")
    words = value["leaves"][-1]["words"]
    if type(words[0]) is not int or not 0 <= words[0] < P:
        raise ValueError("expected canonical public result")
    words[0] = (words[0] + 1) % P
    out.write_text(json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n")


def balanced_order(workers: list[int], assignment: int, round_id: int) -> list[int]:
    """Rotate each setting through process-order positions across statements."""
    offset = (assignment + round_id) % len(workers)
    return workers[offset:] + workers[:offset]


def summary(records: list[dict], workers: list[int], assignments: int,
            rounds: int) -> dict:
    """Use distinct statements as the aggregation unit, not repeated process runs."""
    cases = sorted({(row["shape"], row["assignment"]) for row in records})
    grouped = {}
    for shape, assignment in cases:
        rows = [row for row in records if (row["shape"], row["assignment"]) ==
                (shape, assignment)]
        if len(rows) != len(workers) * rounds:
            raise ValueError("incomplete paired assignment")
        by_worker = {}
        for worker in workers:
            worker_rows = [row for row in rows if row["workers"] == worker]
            if (len(worker_rows) != rounds or
                    {row["round"] for row in worker_rows} != set(range(rounds))):
                raise ValueError("missing or repeated worker count")
            values = [row["native_prove_including_setup_ns"] for row in worker_rows]
            by_worker[worker] = statistics.median(values)
        grouped[(shape, assignment)] = by_worker
    result = {}
    for shape in sorted({key[0] for key in cases}):
        samples = [value for (name, _), value in grouped.items() if name == shape]
        if len(samples) != assignments:
            raise ValueError("incomplete source assignment roster")
        median_ms = {str(worker): statistics.median(sample[worker] for sample in samples) / 1e6
                     for worker in workers}
        baseline = 18 if 18 in workers else workers[0]
        ratios = {str(worker): statistics.median(sample[worker] / sample[baseline]
                                                 for sample in samples)
                  for worker in workers}
        result[shape] = {"distinct_statements": len(samples),
                         "median_native_prove_including_setup_ms": median_ms,
                         "median_paired_ratio_to_worker_" + str(baseline): ratios}
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package-root", type=Path, required=True)
    parser.add_argument("--protocol", type=Path, default=PROTOCOL)
    parser.add_argument("--shapes", nargs="+", default=["control_n2", "control_n6"])
    parser.add_argument("--workers", nargs="+", type=int, default=[16, 18, 24, 32])
    parser.add_argument("--assignments", type=int, default=30)
    parser.add_argument("--rounds", type=int, default=2)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if (not args.shapes or len(set(args.shapes)) != len(args.shapes) or
            not args.workers or len(set(args.workers)) != len(args.workers) or
            any(not 1 <= worker <= 64 for worker in args.workers) or args.rounds < 1):
        parser.error("distinct shapes and worker counts 1..64, and positive rounds required")
    protocol, packages = preflight(args.package_root, args.shapes, args.assignments, args.protocol)
    args.out.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    rows = []
    negative_checks = {}
    for package in packages:
        shape = package["shape"]
        previous = {}
        for case in package["cases"]:
            index = case["index"]
            for round_id in range(args.rounds):
                for worker in balanced_order(args.workers, index, round_id):
                    env["STWO_ZIG_POW_WORKERS"] = str(worker)
                    stem = f"{shape}-a{index:02d}-r{round_id}-w{worker}"
                    proof, emitted = (args.out / f"{stem}.proof",
                                      args.out / f"{stem}.statement.json")
                    result, wall_ns = command([str(package["binaries"]["prover"]),
                                               str(case["assignment"]), str(proof),
                                               str(emitted), str(case["statement"])], env)
                    if result.returncode or not proof.is_file() or not emitted.is_file():
                        raise RuntimeError(f"{stem}: prover failed: {result.stderr.decode(errors='replace')}")
                    if emitted.read_bytes() != case["statement"].read_bytes():
                        raise RuntimeError(f"{stem}: prover changed frozen public statement")
                    native_ns = stage_time(result.stderr, wall_ns)
                    verify, verify_wall_ns = command([str(package["binaries"]["verifier"]),
                                                      str(proof), str(case["statement"])], env)
                    if verify.returncode or b"verified" not in verify.stderr:
                        raise RuntimeError(f"{stem}: native verifier rejected: {verify.stderr.decode(errors='replace')}")
                    proof_hash = sha(proof.read_bytes())
                    old = previous.setdefault(index, (proof_hash, proof.stat().st_size))
                    if old != (proof_hash, proof.stat().st_size):
                        raise RuntimeError(f"{stem}: proof bytes changed with worker count or rerun")
                    if shape not in negative_checks:
                        altered = args.out / f"{shape}.changed-result.json"
                        change_result(case["statement"], altered)
                        bad, _ = command([str(package["binaries"]["verifier"]),
                                          str(proof), str(altered)], env)
                        altered.unlink()
                        if bad.returncode == 0 or b"InvalidMixedInteractionNonce" not in bad.stderr:
                            raise RuntimeError(f"{shape}: ABI-valid changed claim did not reach the expected proof rejection: {bad.stderr.decode(errors='replace')}")
                        negative_checks[shape] = bad.stderr.decode(errors="replace").strip()
                    rows.append({"shape": shape, "assignment": index, "round": round_id,
                                 "workers": worker, "native_prove_including_setup_ns": native_ns,
                                 "prover_wall_ns": wall_ns, "verifier_wall_ns": verify_wall_ns,
                                 "proof_bytes": proof.stat().st_size, "proof_sha256": proof_hash,
                                 "native_verifier_accepted": True})
                    proof.unlink()
                    emitted.unlink()
            print(f"{shape} assignment {index + 1}/{args.assignments} verified", flush=True)
    report = {"schema": "s31-mixed-pow-workers-fresh-statements-v1",
              "scope": "one host, frozen same binaries, distinct statements; native prove includes setup and both PoW stages; diagnostic only, no predictor or speedup claim",
              "protocol": protocol, "script_sha256": sha(Path(__file__).read_bytes()),
              "package_root": str(args.package_root.resolve()),
              "host_logical_cpus": os.cpu_count(), "workers": args.workers,
              "rounds": args.rounds, "assignments_per_shape": args.assignments,
              "packages": [{"shape": item["shape"], "source_sha256": item["source_sha256"],
                            "binary_sha256": item["binary_sha256"]} for item in packages],
              "changed_claim_verifier_diagnostics": negative_checks,
              "summary": summary(rows, args.workers, args.assignments, args.rounds),
              "records": rows}
    (args.out / "diagnostic.json").write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report["summary"], sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
