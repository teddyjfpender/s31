#!/usr/bin/env python3
"""Independent post-run checks for the frozen V10 geometry transfer.

This file is deliberately outside the V10 protocol's pinned tool roster. It
does not modify the prospective model, protocol, runner, or score. In
particular it reconstructs each ABI-valid negative statement from the saved
honest statement, rather than accepting any verifier-rejected file as a
changed-result control.
"""

from __future__ import annotations

import argparse
import json
import statistics
import subprocess
from pathlib import Path

import protocol as p

RESULT = p.LANGUAGE / "mixed-cost-v10-geometry-transfer-result.json"
SCORE = p.LANGUAGE / "mixed-cost-v10-geometry-transfer-score.json"
AUDIT = p.LANGUAGE / "mixed-cost-v10-geometry-independent-audit.json"


def calculated_score(rows: list[dict], prediction: dict, gates: dict) -> dict:
    scored = rows[2:]
    if len(scored) != p.CLAIMS or [row["claim_index"] for row in scored] != list(
            range(1, p.CLAIMS + 1)):
        raise ValueError("scored roster is not claims 1 through 80 in order")
    walls = [row["first_verified_process_wall_ns"] for row in scored]
    sizes = [row["proof_bytes"] for row in scored]
    observed_wall = statistics.median(walls)
    observed_size = statistics.median(sizes)
    expected_wall = prediction["warm_wall_quantile_ns"]["0.5"]
    expected_size = prediction["proof_bytes_center"]
    wall_low = prediction["warm_wall_quantile_ns"]["0.05"]
    wall_high = prediction["warm_wall_quantile_ns"]["0.95"]
    size_low, size_high = prediction["proof_bytes_interval"]
    wall_error = abs(observed_wall - expected_wall) / observed_wall
    size_error = abs(observed_size - expected_size) / observed_size
    wall_coverage = sum(wall_low <= value <= wall_high for value in walls) / len(walls)
    size_coverage = sum(size_low <= value <= size_high for value in sizes) / len(sizes)
    checks = {
        "wall_median_error": wall_error <= gates["wall_median_relative_error_per_source_max"],
        "wall_interval_coverage": wall_coverage >= gates["wall_90_interval_coverage_per_source_min"],
        "proof_median_error": size_error <= gates["proof_median_relative_error_per_source_max"],
        "proof_interval_coverage": size_coverage >= gates["proof_90_interval_coverage_per_source_min"],
    }
    return {"wall_median_ns": observed_wall, "proof_median_bytes": observed_size,
            "wall_median_relative_error": wall_error,
            "wall_interval_coverage": wall_coverage,
            "proof_median_relative_error": size_error,
            "proof_interval_coverage": size_coverage,
            "gates": checks, "all_gates_pass": all(checks.values())}


def run(out: Path, native: bool) -> dict:
    protocol_raw = p.PROTOCOL.read_bytes()
    model_raw = p.MODEL.read_bytes()
    result_raw = RESULT.read_bytes()
    score_raw = SCORE.read_bytes()
    protocol = p.v2.parse(protocol_raw)
    result = p.v2.parse(result_raw)
    score = p.v2.parse(score_raw)
    if (protocol_raw != p.canonical(protocol) or
            model_raw != p.canonical(p.v2.parse(model_raw)) or
            result_raw != p.canonical(result) or
            score_raw != p.canonical(score) or
            protocol.get("schema") != "s31-mixed-cost-v10-geometry-transfer-protocol" or
            result.get("schema") != "s31-mixed-cost-v10-geometry-transfer-result" or
            score.get("schema") != "s31-mixed-cost-v10-geometry-transfer-score" or
            p.sha(model_raw) != protocol["v10_model_sha256"] or
            p.sha(protocol_raw) != result["protocol_sha256"] or
            p.sha(protocol_raw) != score["protocol_sha256"] or
            p.sha(result_raw) != score["result_sha256"] or
            (out / "result.json").read_bytes() != result_raw or
            set(score["sources"]) != set(protocol["source_roster"])):
        raise ValueError("frozen identity or canonical result/score differs")
    checked = 0
    scored = {}
    if [row["name"] for row in result["records"]] != list(protocol["source_roster"]):
        raise ValueError("result source roster/order differs from protocol")
    for record in result["records"]:
        name = record["name"]
        expected = protocol["source_roster"][name]
        directory = out / name
        source = (directory / "source.s31.json").read_bytes()
        if (source != (p.SOURCE_DIR / f"{name}.json").read_bytes() or
                source != p.source(name) or
                p.sha(source) != expected["source_sha256"] or
                record["source_sha256"] != expected["source_sha256"] or
                len(record["trials"]) != p.CLAIMS + 2):
            raise ValueError(f"source or trial roster differs: {name}")
        binaries = {role: directory / "package/bin" /
                    f"s31-mixed_cost_v10_geometry_transfer_{name}-mixed-general-{suffix}"
                    for role, suffix in (("prover", "prover"),
                                         ("verifier", "native-verifier"),
                                         ("manifest", "manifest"))}
        if {role: p.sha(path.read_bytes()) for role, path in binaries.items()} != record[
                "binary_sha256"]:
            raise ValueError(f"saved binary hashes differ: {name}")
        manifest_raw = (directory / "manifest.stdout").read_bytes()
        manifest = p.v2.parse(manifest_raw)
        geometry = expected["expected_geometry"]
        if (manifest != record["native_manifest"] or
                p.sha(manifest_raw) != record["manifest_sha256"] or
                manifest["source_sha256"] != expected["source_sha256"] or
                manifest["call_count"] != expected["call_count"] or
                manifest["slot_count"] != geometry["slots"] or
                manifest["total_constraints"] != geometry["constraints"] or
                manifest["tree_columns"] != geometry["tree_columns"] or
                [slot["trace_log_size"] for slot in manifest["slots"]] !=
                geometry["slot_trace_logs"] or
                manifest["max_column_log_size"] != geometry["max_column_log_size"] or
                manifest["composition_log_size"] != geometry["composition_log_size"] or
                manifest["calls"][0]["rounds"] != expected["chip_rounds"] or
                manifest["interaction_pow_bits"] != 20 or
                manifest["pcs"]["fri_config"]["pow_bits"] != 26):
            raise ValueError(f"saved native manifest differs: {name}")
        for ordinal, row in enumerate(record["trials"]):
            index = 0 if ordinal < 2 else ordinal - 1
            repeat = ordinal if ordinal < 2 else 0
            prefix = f"a{index:02d}r{repeat}"
            assignment = (directory / f"{prefix}.assignment.json").read_bytes()
            statement = (directory / f"{prefix}.statement.json").read_bytes()
            changed = (directory / f"{prefix}.changed.json").read_bytes()
            proof_path = directory / f"{prefix}.proof"
            proof = proof_path.read_bytes()
            recomputed_source, recomputed_assignment, recomputed_statement = p.case(
                name, index)
            if (row["ordinal"] != ordinal or row["claim_index"] != index or
                    row["repeat"] != repeat or
                    (source, assignment, statement) !=
                    (recomputed_source, recomputed_assignment, recomputed_statement) or
                    changed != p.v2.changed_result(source, statement) or
                    p.sha(assignment) != expected["assignment_sha256"][index] or
                    p.sha(statement) != expected["statement_sha256"][index] or
                    p.sha(assignment) != row["assignment_sha256"] or
                    p.sha(statement) != row["statement_sha256"] or
                    p.sha(proof) != row["proof_sha256"] or
                    len(proof) != row["proof_bytes"] or
                    (directory / f"{prefix}.emitted.json").read_bytes() != statement):
                raise ValueError(f"claim, changed-result, or proof differs: {name}/{prefix}")
            stage = p.v2.tagged((directory / f"{prefix}.prove.stderr").read_bytes(),
                                b"S31_MIXED_STAGE_V1")
            phase = p.v2.tagged((directory / f"{prefix}.prove.stderr").read_bytes(),
                                b"S31_MIXED_NATIVE_PHASE_V1")
            if (stage["source_sha256"] != expected["source_sha256"] or
                    stage["proof_bytes"] != len(proof) or
                    stage["stages_ns"] != row["package_stages_ns"] or
                    phase != row["native_phases_ns"] or
                    phase["source_sha256"] != expected["source_sha256"] or
                    b"verified" not in (directory / f"{prefix}.verified.stderr").read_bytes() or
                    (directory / f"{prefix}.changed.stderr").read_bytes().strip() !=
                    b"error: InvalidMixedInteractionNonce"):
                raise ValueError(f"native report/control differs: {name}/{prefix}")
            prove = row["prover_process_monotonic_ns"]
            verify = row["external_verifier_process_monotonic_ns"]
            if any(set(endpoint) != {"start", "end", "duration"} or
                   endpoint["end"] - endpoint["start"] != endpoint["duration"] or
                   endpoint["duration"] <= 0 for endpoint in (prove, verify)) or \
                    prove["duration"] + verify["duration"] != row[
                        "first_verified_process_wall_ns"]:
                raise ValueError(f"monotonic timing endpoints differ: {name}/{prefix}")
            if native:
                honest = subprocess.run([str(binaries["verifier"]), str(proof_path),
                                         str(directory / f"{prefix}.statement.json")],
                                        capture_output=True, check=False)
                negative = subprocess.run([str(binaries["verifier"]), str(proof_path),
                                           str(directory / f"{prefix}.changed.json")],
                                          capture_output=True, check=False)
                if (honest.returncode or b"verified" not in honest.stderr or
                        not p.v2.proof_layer_rejection(negative)):
                    raise ValueError(f"independent native replay differs: {name}/{prefix}")
            checked += 1
        scored[name] = calculated_score(record["trials"], expected["prediction"],
                                        protocol["gates"])
        official = score["sources"][name]
        for key in ("observed_warm_wall_median_ns", "observed_proof_median_bytes",
                    "wall_median_relative_error", "wall_interval_coverage",
                    "proof_median_relative_error", "proof_interval_coverage"):
            independent_key = "wall_median_ns" if key == "observed_warm_wall_median_ns" \
                else "proof_median_bytes" if key == "observed_proof_median_bytes" else key
            if official[key] != scored[name][independent_key]:
                raise ValueError(f"independent score differs: {name}/{key}")
        if (official["gates"] != scored[name]["gates"] or
                official["all_gates_pass"] != scored[name]["all_gates_pass"]):
            raise ValueError(f"independent gates differ: {name}")
    if (checked != 3 * (p.CLAIMS + 2) or
            checked != result["verified_proofs"] or
            checked != result["changed_claim_proof_rejections"] or
            score["all_gates_pass"] != all(row["all_gates_pass"] for row in scored.values())):
        raise ValueError("proof totals or aggregate gate differ")
    return {"schema": "s31-mixed-cost-v10-geometry-independent-audit",
            "protocol_sha256": p.sha(protocol_raw),
            "model_sha256": p.sha(model_raw),
            "result_sha256": p.sha(result_raw),
            "score_sha256": p.sha(score_raw),
            "exact_changed_result_files": checked,
            "exact_claim_and_proof_files": checked,
            "native_reports_and_timing_endpoints": checked,
            "native_replay": native,
            "native_replayed_proofs": checked if native else 0,
            "source_scores": scored,
            "all_gates_pass": score["all_gates_pass"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--write", action="store_true")
    args = parser.parse_args()
    report = run(args.out, args.native)
    if args.write:
        if AUDIT.exists():
            raise ValueError("independent audit artifact already exists")
        AUDIT.write_bytes(p.canonical(report))
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
