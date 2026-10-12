#!/usr/bin/env python3
"""Post-hoc matched bare-vs-time process method diagnostic, never V11 scoring.

Run only after the single prospective V11 result is frozen. Uses the exact
saved source-pinned package, public statement, and native verifier. New proof
samples are diagnostic and cannot alter the V11 result, score, or model.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import random
import statistics
import subprocess
import time
from pathlib import Path

import protocol as p

RESULT = p.LANGUAGE / "mixed-cost-v11-unseen-result.json"
SCORE = p.LANGUAGE / "mixed-cost-v11-unseen-score.json"
REPORT = p.LANGUAGE / "mixed-cost-v11-posthoc-method-check.json"
SOURCES = ("gate_surge_n1", "joint_surge_n1")
PROVER_PAIRS = 16
VERIFIER_PAIRS = 24


def timed(command: list[str], wrapped: bool, resource: Path | None,
          env: dict[str, str]) -> tuple[subprocess.CompletedProcess[bytes], int]:
    actual = command
    if wrapped:
        if resource is None:
            raise ValueError("wrapped process needs a resource report")
        if platform.system() == "Darwin":
            actual = ["/usr/bin/time", "-l", "-o", str(resource), *command]
        elif platform.system() == "Linux":
            actual = ["/usr/bin/time", "-f", "%M", "-o", str(resource), *command]
        else:
            raise RuntimeError("/usr/bin/time process RSS method unavailable")
    start = time.perf_counter_ns()
    result = subprocess.run(actual, cwd=p.ROOT, env=env, capture_output=True,
                            check=False, timeout=120)
    duration = time.perf_counter_ns() - start
    if result.returncode:
        raise RuntimeError(f"diagnostic native command failed: {result.stderr[-1000:]!r}")
    if wrapped and (not resource.is_file() or not resource.read_bytes()):
        raise RuntimeError("wrapped invocation omitted OS time report")
    return result, duration


def orders(count: int, seed: int) -> list[tuple[bool, bool]]:
    result = [(False, True)] * (count // 2) + [(True, False)] * (count // 2)
    random.Random(seed).shuffle(result)
    return result


def run(out: Path) -> dict:
    protocol_raw = p.PROTOCOL.read_bytes()
    protocol = json.loads(protocol_raw)
    protocol_hash = p.sha(protocol_raw)
    if (protocol_raw != p.canonical(protocol) or
            p.v2.git("show", f"HEAD:{p.PROTOCOL.relative_to(p.ROOT).as_posix()}") !=
            protocol_raw):
        raise ValueError("diagnostic protocol differs from committed V11 freeze")
    result_raw = RESULT.read_bytes()
    score_raw = SCORE.read_bytes()
    result = json.loads(result_raw)
    score = json.loads(score_raw)
    if (REPORT.exists() or out.exists() or
            result["protocol_sha256"] != protocol_hash or
            score["result_sha256"] != p.sha(result_raw) or
            result["verified_proofs"] != 88 or
            score["all_gates_pass"]):
        raise ValueError("diagnostic requires the saved single failed V11 run")
    if not Path("/usr/bin/time").is_file():
        raise RuntimeError("OS time executable unavailable")
    out.mkdir(parents=True)
    records = {row["name"]: row for row in result["records"]}
    env = os.environ.copy()
    env.pop("STWO_ZIG_POW_WORKERS", None)
    env["S31_MIXED_NATIVE_PHASES"] = "1"
    reports = {}
    for source_index, name in enumerate(SOURCES):
        record = records[name]
        directory = out / name
        directory.mkdir()
        package = out.parent / name / "package/bin"
        base = f"s31-mixed_cost_v11_unseen_{name}-mixed-general-"
        prover = package / (base + "prover")
        verifier = package / (base + "native-verifier")
        if (p.sha(prover.read_bytes()) != record["binary_sha256"]["prover"] or
                p.sha(verifier.read_bytes()) != record["binary_sha256"]["verifier"]):
            raise ValueError("diagnostic binaries differ from V11 scored run")
        scored_dir = out.parent / name
        assignment = scored_dir / "a01r0.assignment.json"
        statement = scored_dir / "a01r0.statement.json"
        fixed_proof = scored_dir / "a01r0.proof"
        if (p.sha(assignment.read_bytes()) != protocol["source_roster"][name]["assignment_sha256"][1] or
                p.sha(statement.read_bytes()) != protocol["source_roster"][name]["statement_sha256"][1] or
                p.sha(fixed_proof.read_bytes()) != record["trials"][2]["proof_sha256"]):
            raise ValueError("diagnostic claim differs from scored claim 1")
        prover_pairs = []
        for index, order in enumerate(orders(PROVER_PAIRS, 1200 + source_index)):
            row = {}
            for wrapped in order:
                label = "time" if wrapped else "bare"
                prefix = f"p{index:02d}-{label}"
                proof = directory / f"{prefix}.proof"
                emitted = directory / f"{prefix}.emitted.json"
                resource = directory / f"{prefix}.resource.txt" if wrapped else None
                process, duration = timed([str(prover), str(assignment), str(proof),
                                           str(emitted), str(statement)], wrapped, resource, env)
                if emitted.read_bytes() != statement.read_bytes():
                    raise ValueError("diagnostic prover emitted a changed statement")
                phase = p.v2.tagged(process.stderr, b"S31_MIXED_NATIVE_PHASE_V1")
                stage = p.v2.tagged(process.stderr, b"S31_MIXED_STAGE_V1")
                if (phase["source_sha256"] != record["source_sha256"] or
                        stage["proof_bytes"] != proof.stat().st_size):
                    raise ValueError("diagnostic proof/native phase differs")
                accepted = subprocess.run([str(verifier), str(proof), str(statement)],
                                          cwd=p.ROOT, env=env, capture_output=True, check=False)
                if accepted.returncode or b"verified" not in accepted.stderr:
                    raise ValueError("diagnostic honest proof rejected")
                row[label] = {"process_wall_ns": duration,
                              "fri_pow_ns": phase["fri_pow_ns"],
                              "interaction_pow_ns": phase["interaction_pow_ns"],
                              "wall_minus_reported_pow_ns": duration - phase["fri_pow_ns"] -
                                  phase["interaction_pow_ns"],
                              "proof_bytes": proof.stat().st_size,
                              "proof_sha256": p.sha(proof.read_bytes()),
                              "resource_sha256": p.sha(resource.read_bytes()) if resource else None}
            prover_pairs.append(row)
        verifier_pairs = []
        for index, order in enumerate(orders(VERIFIER_PAIRS, 2200 + source_index)):
            row = {}
            for wrapped in order:
                label = "time" if wrapped else "bare"
                resource = directory / f"v{index:02d}-{label}.resource.txt" if wrapped else None
                process, duration = timed([str(verifier), str(fixed_proof), str(statement)],
                                          wrapped, resource, env)
                if b"verified" not in process.stderr:
                    raise ValueError("diagnostic native verifier omitted acceptance")
                row[label] = {"process_wall_ns": duration,
                              "resource_sha256": p.sha(resource.read_bytes()) if resource else None}
            verifier_pairs.append(row)
        reports[name] = {
            "source_sha256": record["source_sha256"],
            "prover_binary_sha256": record["binary_sha256"]["prover"],
            "verifier_binary_sha256": record["binary_sha256"]["verifier"],
            "assignment_sha256": p.sha(assignment.read_bytes()),
            "statement_sha256": p.sha(statement.read_bytes()),
            "fixed_verifier_proof_sha256": p.sha(fixed_proof.read_bytes()),
            "prover_pairs": prover_pairs,
            "verifier_pairs": verifier_pairs,
            "prover_paired_wall_delta_median_ns": statistics.median(
                row["time"]["process_wall_ns"] - row["bare"]["process_wall_ns"]
                for row in prover_pairs),
            "prover_paired_residual_delta_median_ns": statistics.median(
                row["time"]["wall_minus_reported_pow_ns"] -
                row["bare"]["wall_minus_reported_pow_ns"] for row in prover_pairs),
            "verifier_paired_wall_delta_median_ns": statistics.median(
                row["time"]["process_wall_ns"] - row["bare"]["process_wall_ns"]
                for row in verifier_pairs),
        }
    report = {"schema": "s31-mixed-cost-v11-posthoc-method-check",
              "role": "diagnostic-only-no-v11-score-or-fit-update",
              "protocol_sha256": protocol_hash, "result_sha256": p.sha(result_raw),
              "score_sha256": p.sha(score_raw),
              "sample": "saved claim 1 and source-pinned binaries; balanced randomized bare/time invocation order",
              "prover_pairs_per_source": PROVER_PAIRS,
              "verifier_pairs_per_source": VERIFIER_PAIRS,
              "sources": reports}
    raw = p.canonical(report)
    (out / "report.json").write_bytes(raw)
    REPORT.write_bytes(raw)
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--scored-out", type=Path, required=True)
    args = parser.parse_args()
    out = args.scored_out / "posthoc_method_check"
    report = run(out)
    print(json.dumps({"schema": report["schema"], "sources": {
        name: {key: value for key, value in source.items() if key.endswith("delta_median_ns")}
        for name, source in report["sources"].items()}}, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
