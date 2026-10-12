#!/usr/bin/env python3
"""Recompute V21 scores, check raw artifact identities, and replay verifiers."""

from __future__ import annotations

import argparse
import importlib.util
import json
import statistics
import subprocess
from pathlib import Path

import freeze as f
import lifecycle

_study_spec = importlib.util.spec_from_file_location(
    "s31_v21_cost_study", f.HERE / "study.py")
if _study_spec is None or _study_spec.loader is None:
    raise RuntimeError("V21 study module unavailable")
s = importlib.util.module_from_spec(_study_spec)
_study_spec.loader.exec_module(s)

_spec = importlib.util.spec_from_file_location(
    "s31_v18_cost_audit", f.HERE.parent / "mixed_cost_v18_topology_transfer/audit.py")
if _spec is None or _spec.loader is None:
    raise RuntimeError("V18 independent audit module unavailable")
old_audit = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(old_audit)

AUDIT = f.LANGUAGE / "mixed-cost-v21-unseen-topology-audit.json"


def run(out: Path, native: bool) -> dict:
    # Replay may run on a later checkout. The native attempt itself still
    # required the stricter current-stack `frozen()` preflight.
    protocol, protocol_sha = f.frozen_record()
    result_raw = s.RESULT.read_bytes()
    score_raw = s.SCORE.read_bytes()
    result = f.v18.v2.parse(result_raw)
    score = f.v18.v2.parse(score_raw)
    if (result_raw != f.canonical(result) or score_raw != f.canonical(score) or
            (out / "result.json").read_bytes() != result_raw or
            result["protocol_sha256"] != protocol_sha or
            score["protocol_sha256"] != protocol_sha or
            score["result_sha256"] != f.sha(result_raw) or
            result["schema"] != "s31-mixed-cost-v21-unseen-topology-result" or
            score["schema"] != "s31-mixed-cost-v21-unseen-topology-score"):
        raise ValueError("canonical protocol, result, or score linkage differs")
    marker_raw = s.ATTEMPT.read_bytes()
    marker_lines = marker_raw.splitlines(keepends=True)
    if len(marker_lines) != 2:
        raise ValueError("one-attempt marker must have start and terminal records")
    started, ended = (f.v18.v2.parse(line) for line in marker_lines)
    if (started["event"] != "started" or ended["event"] != "completed" or
            started["protocol_sha256"] != protocol_sha or
            started["output_dir"] != str(out.resolve()) or
            ended["score_sha256"] != f.sha(score_raw) or
            ended["all_gates_pass"] != score["all_gates_pass"] or
            any(line != f.canonical(value) for line, value in zip(
                marker_lines, (started, ended), strict=True))):
        raise ValueError("one-attempt marker differs")
    source = (out / "source.s31.json").read_bytes()
    record = result["record"]
    if (source != f.source() or f.sha(source) != protocol["source_sha256"] or
            record["source_sha256"] != protocol["source_sha256"] or
            len(record["trials"]) != f.CLAIMS + 2):
        raise ValueError("source or claim count differs")
    binaries = s.bins(out)
    if {role: f.sha(path.read_bytes()) for role, path in binaries.items()} != record[
            "binary_sha256"]:
        raise ValueError("native binary hashes differ")
    manifest_raw = (out / "manifest.stdout").read_bytes()
    if f.sha(manifest_raw) != record["manifest_sha256"]:
        raise ValueError("native manifest hash differs")
    manifest = f.v18.v2.parse(manifest_raw)
    old_expected = protocol["expected"]
    s.old_study.check_manifest(manifest, old_expected)
    if manifest != f.v18.v2.parse((out / "manifest.json").read_bytes()):
        raise ValueError("frozen manifest admission differs")
    starts = []
    for ordinal, row in enumerate(record["trials"]):
        index = 0 if ordinal < 2 else protocol["claim_order"][ordinal - 2]
        repeat = ordinal if ordinal < 2 else 0
        prefix = f"a{index:02d}r{repeat}"
        raw_source, assignment, statement = f.case(index)
        proof_path = out / f"{prefix}.proof"
        proof = proof_path.read_bytes()
        if (raw_source != source or row["ordinal"] != ordinal or
                row["claim_index"] != index or row["repeat"] != repeat or
                (out / f"{prefix}.assignment.json").read_bytes() != assignment or
                (out / f"{prefix}.statement.json").read_bytes() != statement or
                (out / f"{prefix}.changed.json").read_bytes() !=
                f.v18.v2.changed_result(source, statement) or
                (out / f"{prefix}.emitted.json").read_bytes() != statement or
                row["assignment_sha256"] != protocol["assignment_sha256"][index] or
                row["statement_sha256"] != protocol["statement_sha256"][index] or
                f.sha(proof) != row["proof_sha256"] or len(proof) != row["proof_bytes"]):
            raise ValueError(f"claim or proof bytes differ at {prefix}")
        stderr = (out / f"{prefix}.prove.stderr").read_bytes()
        stage = f.v18.v2.tagged(stderr, b"S31_MIXED_STAGE_V1")
        phase = f.v18.v2.tagged(stderr, b"S31_MIXED_NATIVE_PHASE_V1")
        if (stage["source_sha256"] != protocol["source_sha256"] or
                stage["stages_ns"] != row["package_stages_ns"] or
                stage["proof_bytes"] != len(proof) or
                phase != row["native_phases_ns"] or
                (out / f"{prefix}.changed.stderr").read_bytes().strip() !=
                b"error: InvalidMixedInteractionNonce" or
                b"verified" not in (out / f"{prefix}.verify.stderr").read_bytes()):
            raise ValueError(f"native stage or control report differs at {prefix}")
        prove = row["prover_process_monotonic_ns"]
        verify = row["external_verifier_process_monotonic_ns"]
        for endpoint in (prove, verify):
            if (endpoint["end"] - endpoint["start"] != endpoint["duration"] or
                    endpoint["duration"] <= 0 or endpoint["peak_rss_bytes"] <= 0):
                raise ValueError(f"invalid process endpoint at {prefix}")
        if (prove["duration"] + verify["duration"] != row[
                "first_verified_process_wall_ns"] or
                phase["fri_pow_ns"] + phase["interaction_pow_ns"] >= row[
                    "first_verified_process_wall_ns"]):
            raise ValueError(f"invalid wall/PoW residual at {prefix}")
        if ordinal >= 2:
            starts.append(prove["start"])
        if native:
            honest = subprocess.run([str(binaries["verifier"]), str(proof_path),
                                     str(out / f"{prefix}.statement.json")],
                                    capture_output=True, check=False)
            changed = subprocess.run([str(binaries["verifier"]), str(proof_path),
                                      str(out / f"{prefix}.changed.json")],
                                     capture_output=True, check=False)
            if (honest.returncode or b"verified" not in honest.stderr or
                    not f.v18.v2.proof_layer_rejection(changed)):
                raise ValueError(f"independent verifier replay failed at {prefix}")
    if starts != sorted(starts):
        raise ValueError("physical timing order differs from frozen claim order")
    independently = old_audit.calculated_score(
        record["trials"], protocol["expected"]["prediction"], f.v18.v2.parse(f.v18.PROTOCOL.read_bytes())["gates"])
    official = score["metrics"]
    mapped = {"wall_median_ns": "observed_warm_wall_median_ns",
              "proof_median_bytes": "observed_proof_median_bytes"}
    for key, value in independently.items():
        if key in ("gates", "all_gates_pass"):
            continue
        if key in official and official[key] != value:
            raise ValueError(f"independently recomputed score differs: {key}")
        if key in mapped and official[mapped[key]] != value:
            raise ValueError(f"independent score differs: {key}")
    if (official["gates"] != independently["gates"] or
            official["all_gates_pass"] != independently["all_gates_pass"] or
            official["observed_warm_wall_median_ns"] != statistics.median(
                row["first_verified_process_wall_ns"] for row in record["trials"][2:]) or
            score["lifecycle"] != lifecycle.score(record,
                protocol["lifecycle_forecast"], protocol["gates"]) or
            score["all_gates_pass"] != (official["all_gates_pass"] and
                all(score["extra_gates"].values()) and
                score["lifecycle"]["all_gates_pass"])):
        raise ValueError("independent gate outcome differs")
    return {"schema": "s31-mixed-cost-v21-unseen-topology-audit",
            "protocol_sha256": protocol_sha, "attempt_sha256": f.sha(marker_raw),
            "result_sha256": f.sha(result_raw), "score_sha256": f.sha(score_raw),
            "native_replayed": native, "proofs_and_controls_checked": len(record["trials"]),
            "all_gates_pass": score["all_gates_pass"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    report = run(args.out, args.native)
    if args.write:
        with AUDIT.open("xb") as file:
            file.write(f.canonical(report))
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
