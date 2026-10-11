#!/usr/bin/env python3
"""Prospective v4 whole-prover distribution study with a committed model handoff.

Chronology: commit tools, prepare+commit protocol, train+audit, fit+commit
train/model/anchor, heldout+audit, evaluate. Never refit from heldout data.
"""

from __future__ import annotations

import argparse
import json
import os
import statistics
import subprocess
from pathlib import Path

import model
import prospective as p

v3 = p.v3
v2 = v3.v2
ROOT, S31 = p.ROOT, p.S31
LANGUAGE = ROOT / "design/s31/measurements/language"
INVENTORY = p.OUTPUT
PROTOCOL = LANGUAGE / "mixed-cost-v4-protocol.json"
TRAIN = LANGUAGE / "mixed-cost-v4-train.json"
HELDOUT = LANGUAGE / "mixed-cost-v4-heldout.json"
MODEL = LANGUAGE / "mixed-cost-v4-model.json"
ANCHOR = LANGUAGE / "mixed-cost-v4-model-anchor.json"
EVALUATION = LANGUAGE / "mixed-cost-v4-evaluation.json"
TOOL_PATHS = (
    "src/frontends/s31/benchmarks/mixed_cost_v4/prospective.py",
    "src/frontends/s31/benchmarks/mixed_cost_v4/model.py",
    "src/frontends/s31/benchmarks/mixed_cost_v4/study.py",
)
DIAGNOSTIC = ((0, 0), (0, 1))
SCORED = tuple((i, 0) for i in range(1, p.CLAIMS))
TRIALS = DIAGNOSTIC + SCORED


def digest(path: Path) -> str:
    return v2.sha(path.read_bytes())


def committed(path: Path, revision: str = "HEAD") -> bool:
    try:
        return v2.git("show", f"{revision}:{path.relative_to(ROOT).as_posix()}") == path.read_bytes()
    except (subprocess.CalledProcessError, OSError):
        return False


def pins() -> dict:
    return {**v3.pins(),
            "v4_tool_sha256": {path: digest(ROOT / path) for path in TOOL_PATHS},
            "v4_prospective_inventory_sha256": digest(INVENTORY)}


def inventory() -> dict:
    raw = INVENTORY.read_bytes()
    value = v2.parse(raw)
    if raw != v2.canonical(value) or value != p.inventory() or not committed(INVENTORY):
        raise ValueError("prospective source/claim inventory changed or is uncommitted")
    return value


def protocol_value() -> dict:
    prospective = inventory()
    return {
        "schema": "s31-mixed-cost-v4-protocol", "status": "pre-native-frozen",
        "lowering": "direct-mixed-general", "build_mode": "ReleaseFast",
        "proof_negative_error": "InvalidMixedInteractionNonce",
        "manifest_interaction_pow_bits": 20, "manifest_fri_pow_bits": 26,
        "claims_per_source": p.CLAIMS, "fresh_processes_per_source": len(TRIALS),
        "process_order": "index-0 twice adjacent, then indices 1..79 once ascending",
        "first_claim_pair": "diagnostic-only first post-build and immediate same-claim repeat",
        "fit_indices": [1, 40], "calibration_indices": [41, 79],
        "heldout_score_indices": [1, 79],
        "model": {
            "nonpow_base": "ols-of-four-fit-program-medians-with-declared-constant-fallback",
            "pow": "two-independent-exponential-clocks-fit-from-training-median-intervals",
            "wall": "equal-mixture-of-156-calibration-residuals-plus-two-exponential-convolution",
            "proof": "ols-four-program-median-center-and-split-conformal-rank-142-interval",
            "cold_and_build": "descriptive-only-no-accuracy-gate"},
        "gates": p.GATES, "speedup_claim_enabled": False,
        "automatic_lowering_enabled": False,
        "split": prospective["split"], **pins()}


def prepare() -> dict:
    if PROTOCOL.exists():
        raise ValueError("v4 final protocol already exists")
    # A changed compiler, engine gitlink, or tool invalidates the final freeze.
    if v2.git("status", "--porcelain", "--", "src/frontends/s31", "deps/stwo-zig").strip():
        raise ValueError("commit frontend and native engine changes before freeze")
    for relative in TOOL_PATHS:
        if not committed(ROOT / relative):
            raise ValueError(f"commit v4 tool before freeze: {relative}")
    value = protocol_value()
    PROTOCOL.write_bytes(v2.canonical(value))
    return {"protocol_sha256": digest(PROTOCOL), "sources": 8, "proofs_planned": 648}


def frozen() -> tuple[dict, str]:
    raw = PROTOCOL.read_bytes()
    value = v2.parse(raw)
    if (raw != v2.canonical(value) or not committed(PROTOCOL) or
            value != protocol_value()):
        raise ValueError("v4 protocol not frozen or pinned stack changed")
    for relative in TOOL_PATHS:
        if not committed(ROOT / relative):
            raise ValueError(f"v4 tool changed: {relative}")
    return value, v2.sha(raw)


def binary_paths(directory: Path, name: str) -> dict[str, Path]:
    base = f"s31-mixed_cost_v4_{name}-mixed-general-"
    root = directory / "package/bin"
    return {"prover": root / (base + "prover"),
            "verifier": root / (base + "native-verifier"),
            "manifest": root / (base + "manifest")}


def check_manifest(data: dict, expected: dict, protocol: dict) -> None:
    if type(data) is not dict:
        raise ValueError("native manifest object required")
    pcs = data.get("pcs", {})
    fri = pcs.get("fri_config", {}) if type(pcs) is dict else {}
    if type(fri) is not dict:
        raise ValueError("native FRI config object required")
    calls, slots, trees = data.get("calls"), data.get("slots"), data.get("tree_columns")
    if (data.get("source_sha256") != expected["source_sha256"] or
            data.get("call_count") != expected["call_count"] or
            data.get("schema") != "s31-mixed-component-inspection-general-v3" or
            data.get("interaction_pow_bits") != protocol["manifest_interaction_pow_bits"] or
            fri.get("pow_bits") != protocol["manifest_fri_pow_bits"] or
            type(calls) is not list or len(calls) != expected["call_count"] or
            any(type(call) is not dict for call in calls) or
            [call.get("call_id") for call in calls] != list(range(expected["call_count"])) or
            type(slots) is not list or len(slots) != data.get("slot_count") or
            any(type(slot) is not dict or type(slot.get("n_constraints")) is not int or
                slot["n_constraints"] < 0 for slot in slots) or
            type(trees) is not list or len(trees) != 4 or
            not all(type(x) is int and x > 0 for x in trees) or
            type(data.get("slot_count")) is not int or data["slot_count"] <= 0 or
            type(data.get("total_constraints")) is not int or data["total_constraints"] <= 0 or
            sum(slot.get("n_constraints", 0) for slot in slots) != data["total_constraints"] or
            data.get("main_columns") != trees[1] or
            data.get("interaction_columns") != trees[2]):
        raise ValueError("native manifest identity, geometry or PoW difficulty differs")


def flat(trial: dict) -> dict:
    return {**trial, **trial["partition_ns"],
            "native_prove_including_setup_ns":
                trial["package_stages_ns"]["native_prove_including_setup_ns"]}


def study_environment() -> dict[str, str]:
    """Use the same explicit environment for measured and replayed verifiers."""
    env = os.environ.copy()
    env.pop("STWO_ZIG_POW_WORKERS", None)
    env["S31_MIXED_NATIVE_PHASES"] = "1"
    return env


def run(split: str, out: Path, model_sha: str | None = None,
        anchor_commit: str | None = None) -> dict:
    if split not in p.SPLITS:
        raise ValueError("invalid split")
    protocol, protocol_sha = frozen()
    if split == "heldout":
        anchor_required(protocol_sha, model_sha, anchor_commit)
    target = out / split
    target.mkdir(parents=True, exist_ok=False)
    env = study_environment()
    records = []
    for shape, count in p.SPLITS[split]:
        name = f"{shape}_n{count}"
        expected = protocol["split"][split][name]
        directory = target / name
        directory.mkdir()
        raw_source = p.source(shape, count)
        source_path = directory / "source.s31.json"
        source_path.write_bytes(raw_source)
        built, build_wall = v2.process([
            "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=2",
            "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
            f"-Ds31-name=mixed_cost_v4_{name}", "-j1", "--prefix",
            str(directory / "package")])
        (directory / "build.stdout").write_bytes(built.stdout)
        (directory / "build.stderr").write_bytes(built.stderr)
        if built.returncode:
            raise RuntimeError(f"{name} package build failed")
        bins = binary_paths(directory, name)
        bin_hashes = {role: digest(path) for role, path in bins.items()}
        manifest_result, _ = v2.process([str(bins["manifest"])])
        (directory / "manifest.stdout").write_bytes(manifest_result.stdout)
        (directory / "manifest.stderr").write_bytes(manifest_result.stderr)
        if manifest_result.returncode:
            raise ValueError("manifest executable failed")
        native_manifest = v2.parse(manifest_result.stdout)
        check_manifest(native_manifest, expected, protocol)
        trials = []
        for ordinal, (index, repeat) in enumerate(TRIALS):
            _, assignment, statement = p.case(shape, count, index)
            prefix = f"a{index:02d}r{repeat}"
            assignment_path = directory / f"{prefix}.assignment.json"
            statement_path = directory / f"{prefix}.statement.json"
            changed_path = directory / f"{prefix}.changed.json"
            proof_path = directory / f"{prefix}.proof"
            emitted_path = directory / f"{prefix}.emitted.json"
            assignment_path.write_bytes(assignment)
            statement_path.write_bytes(statement)
            changed_path.write_bytes(v2.changed_result(raw_source, statement))
            if {role: digest(path) for role, path in bins.items()} != bin_hashes:
                raise ValueError("binary changed during measurement")
            proved, prove_wall = v3.timed([str(bins["prover"]), str(assignment_path),
                                           str(proof_path), str(emitted_path),
                                           str(statement_path)], env)
            (directory / f"{prefix}.stderr").write_bytes(proved.stderr)
            if (proved.returncode or not proof_path.exists() or
                    not emitted_path.exists() or emitted_path.read_bytes() != statement):
                raise RuntimeError(f"{name}/{prefix} prover or statement failed")
            verified, verify_wall = v3.timed([str(bins["verifier"]), str(proof_path),
                                               str(statement_path)], env)
            changed, _ = v2.process([str(bins["verifier"]), str(proof_path),
                                      str(changed_path)], env)
            (directory / f"{prefix}.verified.stderr").write_bytes(verified.stderr)
            (directory / f"{prefix}.changed.stderr").write_bytes(changed.stderr)
            if (verified.returncode or b"verified" not in verified.stderr or
                    not v2.proof_layer_rejection(changed)):
                raise RuntimeError(f"{name}/{prefix} verifier controls failed")
            stage = v2.tagged(proved.stderr, b"S31_MIXED_STAGE_V1")
            phase = v2.tagged(proved.stderr, b"S31_MIXED_NATIVE_PHASE_V1")
            if (stage["source_sha256"] != expected["source_sha256"] or
                    stage["proof_bytes"] != proof_path.stat().st_size):
                raise ValueError("source/proof differs from native report")
            partition = v3.project(stage, phase, prove_wall["duration"],
                                   verify_wall["duration"])
            trials.append({"ordinal": ordinal, "claim_index": index, "repeat": repeat,
                           "assignment_sha256": v2.sha(assignment),
                           "statement_sha256": v2.sha(statement),
                           "proof_sha256": digest(proof_path),
                           "proof_bytes": proof_path.stat().st_size,
                           "package_stages_ns": stage["stages_ns"],
                           "native_phases_ns": phase, "partition_ns": partition,
                           "prover_process_monotonic_ns": prove_wall,
                           "external_verifier_process_monotonic_ns": verify_wall,
                           "prover_process_wall_ns": prove_wall["duration"],
                           "external_verifier_process_wall_ns": verify_wall["duration"],
                           "first_verified_process_wall_ns":
                               prove_wall["duration"] + verify_wall["duration"],
                           "changed_result_rejected_at_interaction_nonce": True})
        records.append({"name": name, "shape": shape, "call_count": count,
                        "source_sha256": expected["source_sha256"],
                        "binary_sha256": bin_hashes,
                        "manifest_sha256": v2.sha(manifest_result.stdout),
                        "native_manifest": native_manifest,
                        "build_wall_ns": build_wall,
                        "cold_warm": v3.cold_warm([flat(t) for t in trials]),
                        "trials": trials})
    if any(protocol[key] != pin for key, pin in pins().items()):
        raise ValueError("stack changed during measurement")
    corpus = {"schema": f"s31-mixed-cost-v4-{split}-corpus",
              "protocol_sha256": protocol_sha, "split": split,
              "host": protocol["host"],
              "engine_gitlink_commit": protocol["engine_gitlink_commit"],
              "records": records, "native_verified_proofs": len(records) * len(TRIALS),
              "changed_result_rejections": len(records) * len(TRIALS)}
    raw = v2.canonical(corpus)
    (out / f"{split}.json").write_bytes(raw)
    (TRAIN if split == "train" else HELDOUT).write_bytes(raw)
    return {"split": split, "corpus_sha256": v2.sha(raw),
            "verified_proofs": corpus["native_verified_proofs"]}


def check_corpus(corpus: dict, protocol: dict, split: str) -> None:
    expected = protocol["split"][split]
    total = len(expected) * len(TRIALS)
    if (corpus.get("schema") != f"s31-mixed-cost-v4-{split}-corpus" or
            corpus.get("protocol_sha256") != digest(PROTOCOL) or
            corpus.get("split") != split or corpus.get("host") != protocol["host"] or
            corpus.get("engine_gitlink_commit") != protocol["engine_gitlink_commit"] or
            corpus.get("native_verified_proofs") != total or
            corpus.get("changed_result_rejections") != total or
            len(corpus.get("records", [])) != len(expected)):
        raise ValueError("corpus identity or count differs")
    for record, (name, roster) in zip(corpus["records"], expected.items()):
        if (record.get("name") != name or record.get("shape") != roster["shape"] or
                record.get("call_count") != roster["call_count"] or
                record.get("source_sha256") != roster["source_sha256"] or
                len(record.get("trials", [])) != len(TRIALS)):
            raise ValueError("corpus source differs")
        check_manifest(record.get("native_manifest", {}), roster, protocol)
        if type(record.get("build_wall_ns")) is not int or record["build_wall_ns"] <= 0:
            raise ValueError("missing package build wall")
        for ordinal, (index, repeat) in enumerate(TRIALS):
            trial = record["trials"][ordinal]
            if (trial.get("ordinal") != ordinal or trial.get("claim_index") != index or
                    trial.get("repeat") != repeat or
                    trial.get("assignment_sha256") != roster["assignment_sha256"][index] or
                    trial.get("statement_sha256") != roster["statement_sha256"][index] or
                    trial.get("changed_result_rejected_at_interaction_nonce") is not True or
                    type(trial.get("proof_bytes")) is not int or trial["proof_bytes"] <= 0):
                raise ValueError("trial order, claim or proof control differs")
            for role, wall_key in (("prover", "prover_process_wall_ns"),
                                   ("external_verifier", "external_verifier_process_wall_ns")):
                endpoints = trial.get(f"{role}_process_monotonic_ns")
                if (type(endpoints) is not dict or set(endpoints) != {"start", "end", "duration"} or
                        any(type(x) is not int or x <= 0 for x in endpoints.values()) or
                        endpoints["end"] - endpoints["start"] != endpoints["duration"] or
                        endpoints["duration"] != trial.get(wall_key)):
                    raise ValueError("monotonic endpoints differ")
            if trial.get("first_verified_process_wall_ns") != (trial["prover_process_wall_ns"] +
                                                               trial["external_verifier_process_wall_ns"]):
                raise ValueError("first verified process wall differs")
            stage = {"schema": "s31-mixed-general-prover-stages-v1",
                     "source_sha256": roster["source_sha256"],
                     "circuit_identity_sha256": trial["native_phases_ns"]["circuit_identity_sha256"],
                     "stages_ns": trial["package_stages_ns"]}
            if v3.project(stage, trial["native_phases_ns"],
                          trial["prover_process_wall_ns"],
                          trial["external_verifier_process_wall_ns"]) != trial["partition_ns"]:
                raise ValueError("disjoint timing partition differs")
        if record.get("cold_warm") != v3.cold_warm([flat(t) for t in record["trials"]]):
            raise ValueError("cold/warm partition differs")


def audit(out: Path, split: str, protocol: dict) -> dict:
    path = TRAIN if split == "train" else HELDOUT
    raw = (out / f"{split}.json").read_bytes()
    if raw != path.read_bytes():
        raise ValueError("raw and tracked corpus differ")
    corpus = v2.parse(raw)
    check_corpus(corpus, protocol, split)
    env = study_environment()
    checked = 0
    for record in corpus["records"]:
        name, shape, count = record["name"], record["shape"], record["call_count"]
        directory = out / split / name
        source_bytes = p.source(shape, count)
        if (directory / "source.s31.json").read_bytes() != source_bytes:
            raise ValueError("raw source changed")
        bins = binary_paths(directory, name)
        if {role: digest(path) for role, path in bins.items()} != record["binary_sha256"]:
            raise ValueError("raw package binary changed")
        manifest_bytes = (directory / "manifest.stdout").read_bytes()
        if (v2.sha(manifest_bytes) != record["manifest_sha256"] or
                v2.parse(manifest_bytes) != record["native_manifest"]):
            raise ValueError("raw manifest changed")
        manifested, _ = v2.process([str(bins["manifest"])])
        if (manifested.returncode or manifested.stdout != manifest_bytes or
                manifested.stderr != (directory / "manifest.stderr").read_bytes()):
            raise ValueError("native manifest replay failed")
        for trial in record["trials"]:
            index, repeat = trial["claim_index"], trial["repeat"]
            _, assignment, statement = p.case(shape, count, index)
            prefix = f"a{index:02d}r{repeat}"
            proof_path = directory / f"{prefix}.proof"
            statement_path = directory / f"{prefix}.statement.json"
            changed_path = directory / f"{prefix}.changed.json"
            proof = proof_path.read_bytes()
            if ((directory / f"{prefix}.assignment.json").read_bytes() != assignment or
                    statement_path.read_bytes() != statement or
                    changed_path.read_bytes() != v2.changed_result(source_bytes, statement) or
                    (directory / f"{prefix}.emitted.json").read_bytes() != statement or
                    v2.sha(proof) != trial["proof_sha256"] or len(proof) != trial["proof_bytes"]):
                raise ValueError("raw trial evidence differs")
            stderr = (directory / f"{prefix}.stderr").read_bytes()
            stage = v2.tagged(stderr, b"S31_MIXED_STAGE_V1")
            phase = v2.tagged(stderr, b"S31_MIXED_NATIVE_PHASE_V1")
            if (stage["source_sha256"] != record["source_sha256"] or
                    stage["proof_bytes"] != len(proof) or
                    stage["stages_ns"] != trial["package_stages_ns"] or
                    phase != trial["native_phases_ns"] or
                    v3.project(stage, phase, trial["prover_process_wall_ns"],
                               trial["external_verifier_process_wall_ns"]) != trial["partition_ns"]):
                raise ValueError("raw native timing report differs")
            accepted, _ = v2.process([str(bins["verifier"]), str(proof_path),
                                       str(statement_path)], env)
            rejected, _ = v2.process([str(bins["verifier"]), str(proof_path),
                                       str(changed_path)], env)
            if (accepted.stderr != (directory / f"{prefix}.verified.stderr").read_bytes() or
                    rejected.stderr != (directory / f"{prefix}.changed.stderr").read_bytes() or
                    accepted.returncode or b"verified" not in accepted.stderr or
                    not v2.proof_layer_rejection(rejected)):
                raise ValueError("native verifier replay failed")
            checked += 1
    return {"schema": "s31-mixed-cost-v4-native-audit", "split": split,
            "corpus_sha256": v2.sha(raw), "proofs_checked": checked}


def model_from_training(corpus: dict, protocol_sha: str, raw: bytes) -> dict:
    fit_rows, cal_rows = [], []
    for record in corpus["records"]:
        for trial in record["trials"][2:]:
            row = {"program": record["name"], "call_count": record["call_count"],
                   "wall_ns": trial["first_verified_process_wall_ns"],
                   "fri_pow_ns": trial["partition_ns"]["fri_pow_ns"],
                   "interaction_pow_ns": trial["partition_ns"]["interaction_pow_ns"],
                   "proof_bytes": trial["proof_bytes"]}
            (fit_rows if trial["claim_index"] <= 40 else cal_rows).append(row)
    value = model.fit(fit_rows, cal_rows)
    value.update({"protocol_sha256": protocol_sha, "train_corpus_sha256": v2.sha(raw),
                  "training_source_sha256": [r["source_sha256"] for r in corpus["records"]],
                  "training_assignment_sha256": [t["assignment_sha256"]
                                                  for r in corpus["records"] for t in r["trials"]],
                  "training_statement_sha256": [t["statement_sha256"]
                                                 for r in corpus["records"] for t in r["trials"]],
                  "speedup_claim_enabled": False, "automatic_lowering_enabled": False})
    return value


def fit(out: Path) -> dict:
    protocol, protocol_sha = frozen()
    if MODEL.exists() or ANCHOR.exists() or (out / "heldout").exists():
        raise ValueError("model exists or heldout started")
    raw = (out / "train.json").read_bytes()
    if raw != TRAIN.read_bytes():
        raise ValueError("tracked training corpus differs")
    corpus = v2.parse(raw)
    check_corpus(corpus, protocol, "train")
    audit(out, "train", protocol)
    value = model_from_training(corpus, protocol_sha, raw)
    MODEL.write_bytes(v2.canonical(value))
    anchor = {"schema": "s31-mixed-cost-v4-model-anchor",
              "status": "commit-training-model-anchor-before-heldout-build",
              "protocol_sha256": protocol_sha,
              "train_corpus_sha256": v2.sha(raw), "model_sha256": digest(MODEL)}
    ANCHOR.write_bytes(v2.canonical(anchor))
    return {"train_corpus_sha256": v2.sha(raw), "model_sha256": digest(MODEL)}


def anchor_required(protocol_sha: str, model_sha: str | None,
                    anchor_commit: str | None) -> dict:
    if model_sha is None or len(model_sha) != 64 or anchor_commit is None or len(anchor_commit) != 40:
        raise ValueError("full model SHA-256 and anchor commit required before heldout build")
    train_raw, model_raw, anchor_raw = TRAIN.read_bytes(), MODEL.read_bytes(), ANCHOR.read_bytes()
    train, value, anchor = map(v2.parse, (train_raw, model_raw, anchor_raw))
    protocol = v2.parse(PROTOCOL.read_bytes())
    check_corpus(train, protocol, "train")
    expected = model_from_training(train, protocol_sha, train_raw)
    if (model_raw != v2.canonical(expected) or
            anchor_raw != v2.canonical({"schema": "s31-mixed-cost-v4-model-anchor",
                                        "status": "commit-training-model-anchor-before-heldout-build",
                                        "protocol_sha256": protocol_sha,
                                        "train_corpus_sha256": v2.sha(train_raw),
                                        "model_sha256": model_sha}) or
            v2.sha(model_raw) != model_sha or
            any(not committed(path, anchor_commit) for path in (TRAIN, MODEL, ANCHOR)) or
            subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                            anchor_commit, "HEAD"], check=False).returncode):
        raise ValueError("model is not the committed training-only anchor")
    return value


def evaluate(out: Path, model_sha: str, anchor_commit: str) -> dict:
    protocol, protocol_sha = frozen()
    fitted = anchor_required(protocol_sha, model_sha, anchor_commit)
    if EVALUATION.exists():
        raise ValueError("evaluation already exists")
    train_raw, heldout_raw = TRAIN.read_bytes(), HELDOUT.read_bytes()
    train, heldout = v2.parse(train_raw), v2.parse(heldout_raw)
    check_corpus(train, protocol, "train")
    check_corpus(heldout, protocol, "heldout")
    audit(out, "heldout", protocol)
    if ((out / "train.json").read_bytes() != train_raw or
            (out / "heldout.json").read_bytes() != heldout_raw or
            set(fitted["training_source_sha256"]) &
                {r["source_sha256"] for r in heldout["records"]} or
            set(fitted["training_assignment_sha256"]) &
                {t["assignment_sha256"] for r in heldout["records"] for t in r["trials"]} or
            set(fitted["training_statement_sha256"]) &
                {t["statement_sha256"] for r in heldout["records"] for t in r["trials"]}):
        raise ValueError("corpus changed or heldout leaked into training")
    rows = []
    for record in heldout["records"]:
        predicted = model.prediction(fitted, record["call_count"])
        warm = record["trials"][2:]
        walls = [t["first_verified_process_wall_ns"] for t in warm]
        proofs = [t["proof_bytes"] for t in warm]
        wall_low = predicted["warm_wall_quantile_ns"]["0.05"]
        wall_center = predicted["warm_wall_quantile_ns"]["0.5"]
        wall_high = predicted["warm_wall_quantile_ns"]["0.95"]
        proof_center = predicted["proof_bytes_center"]
        proof_low, proof_high = predicted["proof_bytes_interval"]
        rows.append({"name": record["name"], "shape": record["shape"],
                     "call_count": record["call_count"], "prediction": predicted,
                     "wall_observed_median_ns": statistics.median(walls),
                     "wall_median_relative_error": abs(wall_center - statistics.median(walls)) /
                         statistics.median(walls),
                     "wall_covered": sum(wall_low <= x <= wall_high for x in walls),
                     "proof_observed_median_bytes": statistics.median(proofs),
                     "proof_median_relative_error": abs(proof_center - statistics.median(proofs)) /
                         statistics.median(proofs),
                     "proof_covered": sum(proof_low <= x <= proof_high for x in proofs),
                     "scored_trials": len(warm), "cold_warm": record["cold_warm"],
                     "build_wall_ns": record["build_wall_ns"]})
    total = sum(r["scored_trials"] for r in rows)
    metrics = {
        "wall_program_p90_median_relative_error": v2.quantile(
            [r["wall_median_relative_error"] for r in rows], .9),
        "wall_nominal_90_interval_coverage": sum(r["wall_covered"] for r in rows) / total,
        "wall_nominal_90_interval_coverage_per_source_min": min(
            r["wall_covered"] / r["scored_trials"] for r in rows),
        "proof_program_p90_median_relative_error": v2.quantile(
            [r["proof_median_relative_error"] for r in rows], .9),
        "proof_nominal_90_interval_coverage": sum(r["proof_covered"] for r in rows) / total,
        "proof_nominal_90_interval_coverage_per_source_min": min(
            r["proof_covered"] / r["scored_trials"] for r in rows)}
    gates = protocol["gates"]
    passes = {"wall_error": metrics["wall_program_p90_median_relative_error"] <=
              gates["wall_program_p90_median_relative_error_max"],
              "wall_coverage": metrics["wall_nominal_90_interval_coverage"] >=
              gates["wall_nominal_90_interval_coverage_min"],
              "wall_per_source": metrics["wall_nominal_90_interval_coverage_per_source_min"] >=
              gates["wall_nominal_90_interval_coverage_per_source_min"],
              "proof_error": metrics["proof_program_p90_median_relative_error"] <=
              gates["proof_program_p90_median_relative_error_max"],
              "proof_coverage": metrics["proof_nominal_90_interval_coverage"] >=
              gates["proof_nominal_90_interval_coverage_min"],
              "proof_per_source": metrics["proof_nominal_90_interval_coverage_per_source_min"] >=
              gates["proof_nominal_90_interval_coverage_per_source_min"]}
    value = {"schema": "s31-mixed-cost-v4-heldout-evaluation",
             "protocol_sha256": protocol_sha, "model_sha256": model_sha,
             "model_anchor_commit": anchor_commit,
             "train_corpus_sha256": v2.sha(train_raw),
             "heldout_corpus_sha256": v2.sha(heldout_raw),
             "rows": rows, "metrics": metrics, "gate_pass": passes,
             "all_gates_pass": all(passes.values()),
             "cold_accuracy_claim_enabled": False, "speedup_claim_enabled": False,
             "automatic_lowering_enabled": False}
    EVALUATION.write_bytes(v2.canonical(value))
    return {"evaluation_sha256": digest(EVALUATION),
            "all_gates_pass": value["all_gates_pass"], "metrics": metrics}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    sub.add_parser("prepare")
    for name in ("train", "audit-train", "fit", "heldout", "audit-heldout", "evaluate"):
        command = sub.add_parser(name)
        command.add_argument("--out", type=Path, required=True)
        if name in ("heldout", "evaluate"):
            command.add_argument("--model-sha256", required=True)
            command.add_argument("--model-anchor-commit", required=True)
    args = parser.parse_args()
    if args.action == "prepare":
        result = prepare()
    elif args.action in ("train", "heldout"):
        result = run(args.action, args.out.resolve(),
                     getattr(args, "model_sha256", None),
                     getattr(args, "model_anchor_commit", None))
    elif args.action.startswith("audit-"):
        result = audit(args.out.resolve(), args.action.split("-", 1)[1], frozen()[0])
    elif args.action == "fit":
        result = fit(args.out.resolve())
    else:
        result = evaluate(args.out.resolve(), args.model_sha256, args.model_anchor_commit)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
