#!/usr/bin/env python3
"""One-attempt prospective build, cold, and whole-workload holdout."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import subprocess
import time
from pathlib import Path

import freeze as f
import lifecycle

# Reuse the already audited V18 measurement and manifest readers. Import by
# absolute path so importing this module as `study` cannot resolve to itself.
_spec = importlib.util.spec_from_file_location(
    "s31_v18_cost_study", f.HERE.parent / "mixed_cost_v18_topology_transfer/study.py")
if _spec is None or _spec.loader is None:
    raise RuntimeError("V18 cost study module unavailable")
old_study = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(old_study)

v18 = f.v18
v2 = v18.v2
RESULT = f.LANGUAGE / "mixed-cost-v23-n8-holdout-result.json"
SCORE = f.LANGUAGE / "mixed-cost-v23-n8-holdout-score.json"
ATTEMPT = f.LANGUAGE / "mixed-cost-v23-n8-holdout-attempt.jsonl"


def blockers(snapshot: bytes, exempt_pid: int) -> list[str]:
    """Reject compiler work and sustained high-CPU processes before the attempt."""
    found = []
    for raw in snapshot.decode("utf-8", errors="replace").splitlines():
        fields = raw.strip().split(maxsplit=3)
        if len(fields) < 3:
            continue
        name = Path(fields[1]).name.lower()
        if name in {"lean", "leanchecker", "lake", "zig", "zig2"}:
            found.append(raw)
        elif fields[0].isdigit() and int(fields[0]) != exempt_pid and name != "ps":
            try:
                if float(fields[2]) >= 10.0:
                    found.append(raw)
            except ValueError:
                found.append(raw)
    return found


def quiet_host_snapshot() -> bytes:
    snapshots = []
    for index in range(2):
        proc = subprocess.run(["ps", "-axo", "pid=,comm=,%cpu=,args="],
                              capture_output=True, check=False)
        if proc.returncode or not proc.stdout:
            raise RuntimeError("quiet-host ps preflight unavailable")
        if active := blockers(proc.stdout, os.getpid()):
            raise RuntimeError("quiet-host preflight found compiler or busy CPU work: " +
                               repr(active[:8]))
        snapshots.append(proc.stdout)
        if index == 0:
            time.sleep(1)
    return b"\n".join(snapshots)




def bins(directory: Path) -> dict[str, Path]:
    base = f"s31-mixed_cost_v23_n8_holdout_{f.NAME}-mixed-general-"
    binary = directory / "package/bin"
    return {role: binary / (base + suffix) for role, suffix in (
        ("prover", "prover"), ("verifier", "native-verifier"),
        ("manifest", "manifest"))}

def append_marker(event: dict) -> None:
    with ATTEMPT.open("ab") as marker:
        marker.write(f.canonical({**event, "time_ns": time.time_ns()}))
        marker.flush()
        os.fsync(marker.fileno())


def run(out: Path) -> dict:
    protocol, protocol_sha = f.frozen()
    if out.exists() or RESULT.exists() or SCORE.exists():
        raise ValueError("one-run output already exists")
    # This is outside the attempt: a busy host consumes no native attempt.
    snapshot = quiet_host_snapshot()
    fd = os.open(ATTEMPT, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o644)
    with os.fdopen(fd, "wb") as marker:
        marker.write(f.canonical({"schema": "s31-v23-quiet-holdout-attempt-v1",
                                  "event": "started", "protocol_sha256": protocol_sha,
                                  "output_dir": str(out.resolve()),
                                  "preflight_pid": os.getpid(),
                                  "quiet_host_ps_sha256": f.sha(snapshot),
                                  "time_ns": time.time_ns()}))
        marker.flush()
        os.fsync(marker.fileno())
    try:
        score = run_after_marker(out, protocol, protocol_sha, snapshot)
    except BaseException as exc:
        append_marker({"event": "failed", "error_type": type(exc).__name__,
                       "error_message": str(exc)})
        raise
    append_marker({"event": "completed", "score_sha256": f.sha(SCORE.read_bytes()),
                   "all_gates_pass": score["all_gates_pass"]})
    return score


def run_after_marker(out: Path, protocol: dict, protocol_sha: str,
                     snapshot: bytes) -> dict:
    out.mkdir(parents=True)
    (out / "quiet-host-preflight.ps").write_bytes(snapshot)
    source = f.case(0)[0]
    source_path = out / "source.s31.json"
    source_path.write_bytes(source)
    expected = protocol["expected"]
    if f.sha(source) != protocol["source_sha256"]:
        raise ValueError("frozen source identity changed")
    env = os.environ.copy()
    env.pop("STWO_ZIG_POW_WORKERS", None)
    env["S31_MIXED_NATIVE_PHASES"] = "1"
    package = out / "package"
    built, build_wall = v2.process([
        "zig", "build", "--build-file", str(f.S31 / "build.zig"), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=2",
        "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
        f"-Ds31-name=mixed_cost_v23_n8_holdout_{f.NAME}", "-j1",
        "--prefix", str(package)])
    (out / "build.stdout").write_bytes(built.stdout)
    (out / "build.stderr").write_bytes(built.stderr)
    if built.returncode:
        raise RuntimeError("native package build failed")
    binaries = bins(out)
    binary_sha = {role: f.sha(path.read_bytes()) for role, path in binaries.items()}
    manifest_process, _ = v2.process([str(binaries["manifest"])])
    (out / "manifest.stdout").write_bytes(manifest_process.stdout)
    (out / "manifest.stderr").write_bytes(manifest_process.stderr)
    if manifest_process.returncode:
        raise RuntimeError("native manifest executable failed")
    manifest = v2.parse(manifest_process.stdout)
    (out / "manifest.json").write_bytes(f.canonical(manifest))
    old_study.check_manifest(manifest, expected)
    trials = []

    def claim(index: int, repeat: int) -> None:
        _, assignment, statement = f.case(index)
        prefix = f"a{index:02d}r{repeat}"
        paths = {key: out / f"{prefix}.{key}" for key in
                 ("assignment.json", "statement.json", "changed.json",
                  "proof", "emitted.json", "prove.stderr", "verify.stderr", "changed.stderr")}
        paths["assignment.json"].write_bytes(assignment)
        paths["statement.json"].write_bytes(statement)
        changed_statement = v2.changed_result(source, statement)
        paths["changed.json"].write_bytes(changed_statement)
        if {role: f.sha(path.read_bytes()) for role, path in binaries.items()} != binary_sha:
            raise ValueError("native binary changed during timing")
        proved, prove_wall = old_study.timed_rss([
            str(binaries["prover"]), str(paths["assignment.json"]),
            str(paths["proof"]), str(paths["emitted.json"]),
            str(paths["statement.json"])], env)
        paths["prove.stderr"].write_bytes(proved.stderr)
        if (proved.returncode or not paths["proof"].is_file() or
                paths["emitted.json"].read_bytes() != statement):
            raise RuntimeError(f"honest native prover or statement failed at {prefix}")
        verified, verify_wall = old_study.timed_rss([
            str(binaries["verifier"]), str(paths["proof"]),
            str(paths["statement.json"])], env)
        paths["verify.stderr"].write_bytes(verified.stderr)
        changed, _ = v2.process([str(binaries["verifier"]), str(paths["proof"]),
                                 str(paths["changed.json"])], env)
        paths["changed.stderr"].write_bytes(changed.stderr)
        if (verified.returncode or b"verified" not in verified.stderr or
                not v2.proof_layer_rejection(changed)):
            raise RuntimeError(f"native verifier controls failed at {prefix}")
        stage = v2.tagged(proved.stderr, b"S31_MIXED_STAGE_V1")
        phase = v2.tagged(proved.stderr, b"S31_MIXED_NATIVE_PHASE_V1")
        total_wall = prove_wall["duration"] + verify_wall["duration"]
        if (stage["source_sha256"] != protocol["source_sha256"] or
                stage["proof_bytes"] != paths["proof"].stat().st_size or
                phase["fri_pow_ns"] <= 0 or phase["interaction_pow_ns"] <= 0 or
                phase["fri_pow_ns"] + phase["interaction_pow_ns"] >= total_wall):
            raise ValueError(f"native phase or proof accounting failed at {prefix}")
        trials.append({
            "ordinal": len(trials), "claim_index": index, "repeat": repeat,
            "assignment_sha256": f.sha(assignment),
            "statement_sha256": f.sha(statement),
            "proof_sha256": f.sha(paths["proof"].read_bytes()),
            "proof_bytes": paths["proof"].stat().st_size,
            "prover_process_monotonic_ns": prove_wall,
            "external_verifier_process_monotonic_ns": verify_wall,
            "first_verified_process_wall_ns": total_wall,
            "package_stages_ns": stage["stages_ns"],
            "native_phases_ns": phase,
            "changed_result_rejected_at_interaction_nonce": True,
        })

    claim(0, 0)
    claim(0, 1)
    for index in protocol["claim_order"]:
        claim(index, 0)
    record = {"name": f.NAME, "source_sha256": protocol["source_sha256"],
              "build_wall_ns": build_wall, "binary_sha256": binary_sha,
              "manifest_sha256": f.sha(manifest_process.stdout), "trials": trials}
    result = {"schema": "s31-mixed-cost-v23-n8-holdout-result",
              "protocol_sha256": protocol_sha, "record": record,
              "verified_proofs": len(trials),
              "changed_result_rejections": len(trials)}
    raw_result = f.canonical(result)
    (out / "result.json").write_bytes(raw_result)
    RESULT.write_bytes(raw_result)
    metrics = old_study.score_record(record, expected, v2.parse(v18.PROTOCOL.read_bytes())["gates"])
    mandatory = {
        "sample20_wall_median_in_band": metrics["wall_sample20_median_in_band"],
        "wall_one_draw_hits": metrics["wall_one_draw_interval_hits"] >= 14,
        "proof_interval_hits": metrics["proof_interval_coverage"] >= 0.8,
    }
    lifecycle_metrics = lifecycle.score(record, protocol["lifecycle_forecast"],
                                        protocol["gates"])
    score = {"schema": "s31-mixed-cost-v23-n8-holdout-score",
             "protocol_sha256": protocol_sha, "result_sha256": f.sha(raw_result),
             "metrics": metrics, "extra_gates": mandatory,
             "lifecycle": lifecycle_metrics,
             "all_gates_pass": metrics["all_gates_pass"] and
                 all(mandatory.values()) and lifecycle_metrics["all_gates_pass"]}
    SCORE.write_bytes(f.canonical(score))
    return score


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("run", choices=("run",))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(run(args.out), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
