#!/usr/bin/env python3
"""Prospective same-host transfer check for the frozen V6 whole-prover model.

Freeze and commit the protocol before ``run``. This diagnostic never refits V6
and never enables automatic lowering. Raw proof artifacts stay under --out.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import statistics
import subprocess
import sys
from pathlib import Path

S31_DIR = Path(__file__).resolve().parents[2]
ROOT = S31_DIR.parents[2]
BENCH = S31_DIR / "benchmarks"
sys.path.insert(0, str(BENCH))
sys.path.insert(0, str(S31_DIR / "python"))

import s31
from benchmark_arithmetic_rss_v2 import assignment as recurrence_assignment
from benchmark_arithmetic_rss_v2 import program as recurrence_program
from benchmark_whole_prover import measured_package_build
from benchmark_whole_prover_cost_v3 import (
    chip_manifest_binding, compact_trial, host_identity, quotient_source,
    signed_assignment,
)
from benchmark_whole_prover_multiscale import hash_assignment, hash_program
from stage_aware_predictor_v1 import TARGETS, actual_target, changed_claim_field
from whole_prover_predictor_v3 import case_features
from whole_prover_predictor_v6 import predict_rss_interval, wall_center
from whole_prover_predictor_v3 import predict_stage

PROTOCOL = ROOT / "design/s31/measurements/language/whole-prover-transfer-v1.json"
V6_AUDIT = ROOT / "design/s31/measurements/language/whole-prover-cost-v6-audit.json"
TOOL_PATHS = (
    Path(__file__),
    BENCH / "benchmark_arithmetic_rss_v2.py",
    BENCH / "benchmark_whole_prover.py",
    BENCH / "benchmark_whole_prover_cost_v3.py",
    BENCH / "benchmark_whole_prover_multiscale.py",
    BENCH / "stage_aware_predictor_v1.py",
    BENCH / "whole_prover_predictor_v3.py",
    BENCH / "whole_prover_predictor_v6.py",
)
SCHEMA = "s31-whole-prover-v6-transfer-protocol-v1"
SAMPLES = 10
SEED = 1_410_000
MIN_FREE_BYTES = 8 * 1024 ** 3
SPECS = (
    ("arithmetic", 96, "direct-gate"),
    ("arithmetic", 1536, "direct-gate"),
    ("chip", 16, "direct-chip"),
    ("chip", 1024, "direct-chip"),
    ("hash", 2, "gate"),
    ("hash", 6, "gate"),
    ("fixed_width", 16, "direct-gate"),
    ("fixed_width", 64, "direct-gate"),
)
GATES = {
    "max_program_point_error": {
        "paired_prove_and_verify_wall_seconds": .25,
        "proof_bytes": .10,
        "prover_peak_rss_bytes": .10,
    },
    "min_pooled_trial_coverage": {
        "paired_prove_and_verify_wall_seconds": .70,
        "proof_bytes": .80,
        "prover_peak_rss_bytes": .80,
    },
}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def tool_digest() -> str:
    digest = hashlib.sha256()
    for path in sorted(TOOL_PATHS):
        digest.update(path.relative_to(ROOT).as_posix().encode())
        digest.update(b"\0")
        digest.update(bytes.fromhex(s31.file_hash(path)))
    return digest.hexdigest()


def git(*args: str, cwd: Path = ROOT) -> str:
    return subprocess.check_output(["git", "-C", str(cwd), *args], text=True).strip()


def workloads(output: Path) -> list[dict]:
    sources = output / "sources"
    sources.mkdir(parents=True, exist_ok=True)
    result = []
    for family, size, lowering in SPECS:
        name = f"transfer_{family}_{size}"
        if family in {"arithmetic", "chip"}:
            source = sources / f"{name}.s31.json"
            body = [{"op": "square"}, {"op": "add_const", "constant": 47}]
            s31.write_json(source, recurrence_program(name, size, body))
            assignments = [recurrence_assignment(size, body, SEED +
                           (100_000 if family == "chip" else 0) + i)
                           for i in range(SAMPLES)]
        elif family == "hash":
            source = sources / f"{name}.s31.json"
            relation = hash_program(size)
            relation["name"] = f"blake_chain_transfer_v1_{size}"
            s31.write_json(source, relation)
            assignments = [hash_assignment(size, SEED + 200_000 + i)
                           for i in range(SAMPLES)]
        else:
            source = sources / f"{name}.s31"
            source.write_text(quotient_source(size).replace("_cost_v1", "_transfer_v1"))
            from package.context import lower_text
            relation, _, _ = lower_text(source)
            if len(relation["public_outputs"]) != 1:
                raise ValueError("transfer quotient expects one public output")
            assignments = [signed_assignment(size, SEED + 300_000 + i,
                           True, relation["public_outputs"][0])
                           for i in range(SAMPLES)]
        paths = []
        for index, assignment in enumerate(assignments):
            path = output / name / "assignments" / f"{index:02d}.json"
            path.parent.mkdir(parents=True, exist_ok=True)
            s31.write_json(path, assignment)
            paths.append(path)
        result.append({"name": name, "family": family, "size": size,
                       "lowering": lowering, "source": source,
                       "assignments": paths})
    return result


def inventory(entries: list[dict], model: dict, audit: dict) -> dict:
    old_sources = set(model["training_source_sha256"]) | {
        item["source_sha256"] for item in audit["programs"]}
    old_assignments = set(model["training_assignment_sha256"])
    sources = {item["name"]: s31.file_hash(item["source"]) for item in entries}
    assignments = {item["name"]: [s31.assignment_digest(path)
                   for path in item["assignments"]] for item in entries}
    all_assignments = [digest for group in assignments.values() for digest in group]
    if (len(set(sources.values())) != len(entries) or
        len(set(all_assignments)) != len(all_assignments) or
        set(sources.values()) & old_sources or
        set(all_assignments) & old_assignments):
        raise ValueError("transfer source or assignment overlaps a frozen V6 input")
    return {"source_sha256": sources, "assignment_sha256": assignments}


def freeze(output: Path) -> None:
    if PROTOCOL.exists():
        raise ValueError("transfer protocol already exists; do not refreeze")
    audit_bytes = V6_AUDIT.read_bytes()
    audit = json.loads(audit_bytes)
    model = audit["model"]
    entries = workloads(output)
    protocol = {
        "schema": SCHEMA,
        "status": "frozen-before-native-transfer-observation",
        "source_base_commit": git("rev-parse", "HEAD"),
        "engine_gitlink_commit": git("rev-parse", "HEAD", cwd=ROOT / "deps/stwo-zig"),
        "compiler_sha256": s31.compiler_fingerprint(),
        "tool_sha256": tool_digest(),
        "tool_paths": [path.relative_to(ROOT).as_posix() for path in sorted(TOOL_PATHS)],
        "v6_audit_sha256": sha(audit_bytes),
        "v6_compiler_sha256": model["compiler_sha256"],
        "host": host_identity(),
        "samples_per_program": SAMPLES,
        "seed": SEED,
        "programs": [{"name": f"transfer_{family}_{size}", "family": family,
                      "size": size, "lowering": lowering}
                     for family, size, lowering in SPECS],
        "inventory": inventory(entries, model, audit),
        "diagnostic_gates": GATES,
        "automatic_lowering_selection_enabled": False,
    }
    s31.write_json(PROTOCOL, protocol)
    print(f"freeze protocol SHA-256: {s31.file_hash(PROTOCOL)}")
    print("Commit the protocol before any native transfer build.")


def require_freeze(output: Path) -> tuple[dict, dict, list[dict]]:
    protocol_bytes = PROTOCOL.read_bytes()
    protocol = json.loads(protocol_bytes)
    if protocol.get("schema") != SCHEMA or protocol.get("status") != "frozen-before-native-transfer-observation":
        raise ValueError("wrong transfer protocol or freeze status")
    relative = PROTOCOL.relative_to(ROOT).as_posix()
    if git("show", f"HEAD:{relative}").encode() + b"\n" != protocol_bytes:
        raise ValueError("transfer protocol bytes must be committed before native work")
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       protocol["source_base_commit"], "HEAD"], check=False).returncode:
        raise ValueError("frozen source base is not an ancestor")
    if (protocol["compiler_sha256"] != s31.compiler_fingerprint() or
        protocol["engine_gitlink_commit"] != git("rev-parse", "HEAD", cwd=ROOT / "deps/stwo-zig") or
        protocol["tool_sha256"] != tool_digest() or
        protocol["host"] != host_identity() or
        protocol["samples_per_program"] != SAMPLES or
        protocol["seed"] != SEED or
        protocol["diagnostic_gates"] != GATES or
        protocol["tool_paths"] != [path.relative_to(ROOT).as_posix() for path in sorted(TOOL_PATHS)]):
        raise ValueError("frozen source, tool, host, or gate pins changed")
    audit_bytes = V6_AUDIT.read_bytes()
    if protocol["v6_audit_sha256"] != sha(audit_bytes):
        raise ValueError("frozen V6 audit changed")
    audit = json.loads(audit_bytes)
    entries = workloads(output)
    if (protocol["programs"] != [{"name": item["name"], "family": item["family"],
                                  "size": item["size"], "lowering": item["lowering"]}
                                 for item in entries] or
        protocol["inventory"] != inventory(entries, audit["model"], audit)):
        raise ValueError("generated transfer sources or assignments changed")
    return protocol, audit, entries


def predict(policy: dict, features: dict) -> dict:
    wall = wall_center(policy["wall_stages"], features)
    ratio = policy["wall_interval"]
    return {
        TARGETS[0]: {"center": wall, "lower": wall * ratio["ratio_p05"],
                     "upper": wall * ratio["ratio_p95"]},
        TARGETS[1]: predict_stage(policy["proof_bytes"], features),
        TARGETS[2]: predict_rss_interval(policy["prover_peak_rss_bytes"], features),
    }


def evaluate_case(trials: list[dict], predictions: dict) -> dict:
    result = {}
    for target in TARGETS:
        values = [actual_target(trial, target) for trial in trials]
        point = (statistics.mean(values) if target == TARGETS[0]
                 else statistics.median(values))
        predicted = predictions[target]
        result[target] = {
            "prediction": predicted,
            "measured_point": point,
            "relative_point_error": abs(predicted["center"] - point) / point,
            "covered_trials": sum(predicted["lower"] <= value <= predicted["upper"]
                                  for value in values),
            "trial_count": len(values),
        }
    return result


def run(output: Path) -> None:
    protocol, audit, entries = require_freeze(output)
    if shutil.disk_usage(output).free < MIN_FREE_BYTES:
        raise ValueError("transfer run needs at least 8 GiB free")
    model = audit["model"]
    if model["training_host"] != protocol["host"] or model["compiler_sha256"] == protocol["compiler_sha256"]:
        raise ValueError("this must be a same-host, changed-compiler transfer")
    cases = {}
    for item in entries:
        if shutil.disk_usage(output).free < MIN_FREE_BYTES:
            raise ValueError("transfer artifacts depleted the 8 GiB reserve")
        name = item["name"]
        package_path = output / name / "package"
        if package_path.exists():
            raise ValueError(f"{name}: transfer requires a fresh package path")
        package, build = measured_package_build(item["source"], package_path,
                                                item["lowering"])
        manifest = json.loads((package / "manifest.json").read_text())
        cost = json.loads((package / "cost-report.json").read_text())
        policy = model["families"][item["family"]]
        visible = s31.visible_fri(cost, item["lowering"])
        if (manifest["compiler_sha256"] != protocol["compiler_sha256"] or
            policy["lowering"] != item["lowering"] or
            policy["profile"] != cost["profile"] or
            policy["visible_fri"] != visible):
            raise ValueError(f"{name}: V6 model profile/FRI is inapplicable on this head")
        case = {"family": item["family"], "raw": cost["raw"],
                "padded": cost["padded"],
                "preprocessed_cells": cost["preprocessed_cells"],
                "chip_manifest_binding": (chip_manifest_binding(package)
                                          if item["family"] == "chip" else None)}
        predictions = predict(policy, case_features(case))
        trials = []
        for index, assignment in enumerate(item["assignments"]):
            if shutil.disk_usage(output).free < MIN_FREE_BYTES:
                raise ValueError("transfer artifacts depleted the 8 GiB reserve")
            trial = s31.trial(package, assignment,
                              output / name / "trials" / f"{index:02d}")
            if (trial["native_verifier_accepted"] is not True or
                trial["independent_value_oracle"]["status"] != "passed"):
                raise ValueError(f"{name}[{index}]: native verifier or oracle failed")
            changed_claim_field(trial["changed_public_statement_rejected"])
            trials.append(compact_trial(trial))
        cases[name] = {"family": item["family"], "size": item["size"],
                       "source_sha256": s31.file_hash(item["source"]),
                       "assignment_sha256": protocol["inventory"]["assignment_sha256"][name],
                       "profile": cost["profile"], "visible_fri": visible,
                       "features": case_features(case), "build": build,
                       "targets": evaluate_case(trials, predictions), "trials": trials}
        print(f"{name}: {len(trials)} native proofs and controls passed", flush=True)
    corpus = {"schema": "s31-whole-prover-v6-transfer-corpus-v1",
              "protocol_sha256": s31.file_hash(PROTOCOL),
              "v6_audit_sha256": protocol["v6_audit_sha256"],
              "compiler_sha256": protocol["compiler_sha256"],
              "engine_gitlink_commit": protocol["engine_gitlink_commit"],
              "host": protocol["host"], "cases": cases}
    s31.write_json(output / "corpus.json", corpus)
    family_results = {}
    for family in model["families"]:
        members = [case for case in cases.values() if case["family"] == family]
        family_results[family] = {}
        for target in TARGETS:
            values = [case["targets"][target] for case in members]
            error = max(value["relative_point_error"] for value in values)
            coverage = sum(value["covered_trials"] for value in values) / sum(
                value["trial_count"] for value in values)
            family_results[family][target] = {
                "max_program_point_error": error,
                "pooled_trial_coverage": coverage,
                "diagnostic_gate_pass": (
                    error <= GATES["max_program_point_error"][target] and
                    coverage >= GATES["min_pooled_trial_coverage"][target]),
            }
    summary = {
        "schema": "s31-whole-prover-v6-transfer-audit-v1",
        "protocol_sha256": s31.file_hash(PROTOCOL),
        "corpus_sha256": s31.file_hash(output / "corpus.json"),
        "v6_audit_sha256": protocol["v6_audit_sha256"],
        "compiler_sha256": protocol["compiler_sha256"],
        "host": protocol["host"], "family_results": family_results,
        "diagnostic_gate_pass": all(result["diagnostic_gate_pass"]
                                    for family in family_results.values()
                                    for result in family.values()),
        "automatic_lowering_selection_enabled": False,
        "scope": "Same-host cross-revision diagnostic; 2 programs/family and 10 trials/program. No cross-host or tail guarantee.",
    }
    s31.write_json(output / "audit.json", summary)
    print(json.dumps(summary, indent=2, sort_keys=True))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=("freeze", "run"))
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=True)
    if args.phase == "freeze":
        freeze(output)
    else:
        run(output)


if __name__ == "__main__":
    main()
