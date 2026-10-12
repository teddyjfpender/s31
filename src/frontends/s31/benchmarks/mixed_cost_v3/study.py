#!/usr/bin/env python3
"""Prospective mixed cost v3: separate first post-build and warm process walls."""

from __future__ import annotations

import argparse
import importlib.util
import json
import os
import statistics
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
LANGUAGE = ROOT / "design/s31/measurements/language"
sys.path.insert(0, str(HERE))
from accounting import cold_warm, project  # noqa: E402

_spec = importlib.util.spec_from_file_location(
    "mixed_cost_v2_base", HERE.parent / "mixed_cost_v2/study.py")
if _spec is None or _spec.loader is None:
    raise RuntimeError("mixed cost v2 helpers unavailable")
v2 = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(v2)

PROTOCOL = LANGUAGE / "mixed-cost-v3-protocol.json"
TRAIN = LANGUAGE / "mixed-cost-v3-train.json"
HELDOUT = LANGUAGE / "mixed-cost-v3-heldout.json"
MODEL = LANGUAGE / "mixed-cost-v3-model.json"
ANCHOR = LANGUAGE / "mixed-cost-v3-model-anchor.json"
EVALUATION = LANGUAGE / "mixed-cost-v3-evaluation.json"
SPLITS = v2.SPLITS
CLAIMS = 8
REPEATS = 2
SEED = 202610119803
P = (1 << 31) - 1
TOOL_PATHS = (
    "src/frontends/s31/benchmarks/mixed_cost_v3/accounting.py",
    "src/frontends/s31/benchmarks/mixed_cost_v3/study.py",
    "src/frontends/s31/benchmarks/mixed_cost_v2/study.py",
)
GATES = {"warm_wall_program_p90_relative_error_max": 0.30,
         "proof_program_p90_relative_error_max": 0.10,
         "warm_wall_trial_band_coverage_min": 0.70,
         "proof_trial_band_coverage_min": 0.80}


def case(shape: str, count: int, index: int) -> tuple[bytes, bytes, bytes]:
    if (shape, count) not in SPLITS["train"] + SPLITS["heldout"] or not 0 <= index < CLAIMS:
        raise ValueError("case outside prospective v3 roster")
    raw_source = v2.source(shape, count, v2.source_design())
    relation = v2.parse(raw_source)
    family = [item for split in SPLITS.values() for item in split].index((shape, count))
    seed = SEED + family * 10_000_000 + count * 100_000 + index * 41
    words = [(seed * (lane + 23) + lane * lane + 13) % P for lane in range(4)]
    result = v2.output_words(shape, count, words)
    assignment = {"public_inputs": {relation["inputs"][0]["name"]: words},
                  "private_inputs": {},
                  "public_outputs": {relation["public_outputs"][0]: result}}
    if v2.evaluate_relation(v2.flat(relation), assignment) != assignment["public_outputs"]:
        raise ValueError("independent oracle disagrees with source")
    statement = v2.statement_from_assignment(relation, assignment)
    v2.changed_result(raw_source, statement)
    return raw_source, v2.canonical(assignment), statement


def pins() -> dict:
    return {**v2.pins(), "v3_tool_sha256": {
        path: v2.sha((ROOT / path).read_bytes()) for path in TOOL_PATHS},
        "v2_protocol_sha256": v2.sha(v2.PROTOCOL.read_bytes())}


def roster() -> dict:
    result = {}
    assignments, statements = set(), set()
    previous = v2.prior_claim_hashes()
    prior_v2 = v2.parse(v2.PROTOCOL.read_bytes())
    for group in prior_v2["split"].values():
        for row in group.values():
            previous.update(row["assignment_sha256"])
            previous.update(row["statement_sha256"])
    for split, sources in SPLITS.items():
        group = {}
        for shape, count in sources:
            rows = [case(shape, count, index) for index in range(CLAIMS)]
            assignment_hashes = [v2.sha(row[1]) for row in rows]
            statement_hashes = [v2.sha(row[2]) for row in rows]
            if ((set(assignment_hashes) | set(statement_hashes)) & previous or
                    set(assignment_hashes) & assignments or
                    set(statement_hashes) & statements):
                raise ValueError("prospective claim reused prior evidence")
            assignments.update(assignment_hashes)
            statements.update(statement_hashes)
            name = f"{shape}_n{count}"
            group[name] = {"shape": shape, "call_count": count,
                           "source_sha256": v2.sha(rows[0][0]),
                           "assignment_sha256": assignment_hashes,
                           "statement_sha256": statement_hashes}
        result[split] = group
    if (len(assignments) != 8 * CLAIMS or len(statements) != 8 * CLAIMS or
            len(assignments | statements) != 16 * CLAIMS):
        raise ValueError("duplicate claim in v3 roster")
    return result


def prepare() -> dict:
    if PROTOCOL.exists():
        raise ValueError("v3 protocol already exists")
    if v2.git("status", "--porcelain", "--", "src/frontends/s31").strip():
        raise ValueError("commit compiler, runtime and study tools before freeze")
    for path in TOOL_PATHS:
        raw = (ROOT / path).read_bytes()
        if v2.git("show", f"HEAD:{path}") != raw:
            raise ValueError(f"commit study dependency before freeze: {path}")
    value = {
        "schema": "s31-mixed-cost-v3-protocol", "status": "pre-native-frozen",
        "assignment_seed": SEED, "claims_per_source": CLAIMS,
        "fresh_processes_per_claim": REPEATS,
        "process_order": "claim-index-ascending, two adjacent fresh processes per claim",
        "cold_definition": "first prover and verifier processes after package build",
        "warm_definition": "all later fresh prover and verifier processes for the same package",
        "first_claim_pair": "same assignment and public statement, separate proof processes",
        "lowering": "direct-mixed-general", "build_mode": "ReleaseFast",
        "timed_native_phases": True, "proof_negative_error": "InvalidMixedInteractionNonce",
        "source_overlap_with_v2": True,
        "model": {
            "warm_wall": "median-of-four-training-program-warm-medians",
            "proof_bytes": "ordinary-least-squares-linear-in-call-count-on-four-training-program-warm-medians",
            "band": "training-warm-trial-5th-and-95th-ratios-clamped-to-include-one",
            "cold": "descriptive-only-no-accuracy-gate"},
        "gates": GATES, "speedup_claim_enabled": False,
        "automatic_lowering_enabled": False, "split": roster(), **pins()}
    PROTOCOL.write_bytes(v2.canonical(value))
    return {"protocol_sha256": v2.sha(PROTOCOL.read_bytes()),
            "programs": sum(map(len, value["split"].values()))}


def frozen() -> tuple[dict, str]:
    raw = PROTOCOL.read_bytes()
    value = v2.parse(raw)
    expected_fields = {
        "schema", "status", "assignment_seed", "claims_per_source",
        "fresh_processes_per_claim", "process_order", "cold_definition",
        "warm_definition", "first_claim_pair", "lowering", "build_mode",
        "timed_native_phases", "proof_negative_error", "source_overlap_with_v2",
        "model", "gates", "speedup_claim_enabled", "automatic_lowering_enabled",
        "split", *pins(),
    }
    if (raw != v2.canonical(value) or set(value) != expected_fields or
            value.get("schema") != "s31-mixed-cost-v3-protocol" or
            value.get("status") != "pre-native-frozen" or
            value.get("assignment_seed") != SEED or
            value.get("claims_per_source") != CLAIMS or
            value.get("fresh_processes_per_claim") != REPEATS or
            value.get("process_order") !=
                "claim-index-ascending, two adjacent fresh processes per claim" or
            value.get("cold_definition") !=
                "first prover and verifier processes after package build" or
            value.get("warm_definition") !=
                "all later fresh prover and verifier processes for the same package" or
            value.get("first_claim_pair") !=
                "same assignment and public statement, separate proof processes" or
            value.get("lowering") != "direct-mixed-general" or
            value.get("build_mode") != "ReleaseFast" or
            value.get("timed_native_phases") is not True or
            value.get("proof_negative_error") != "InvalidMixedInteractionNonce" or
            value.get("source_overlap_with_v2") is not True or
            value.get("gates") != GATES or
            value.get("model") != {
                "warm_wall": "median-of-four-training-program-warm-medians",
                "proof_bytes": "ordinary-least-squares-linear-in-call-count-on-four-training-program-warm-medians",
                "band": "training-warm-trial-5th-and-95th-ratios-clamped-to-include-one",
                "cold": "descriptive-only-no-accuracy-gate"} or
            value.get("speedup_claim_enabled") is not False or
            value.get("automatic_lowering_enabled") is not False or
            value.get("split") != roster() or
            v2.git("show", f"HEAD:{PROTOCOL.relative_to(ROOT).as_posix()}") != raw):
        raise ValueError("v3 protocol is not frozen and committed unchanged")
    for key, expected in pins().items():
        if value.get(key) != expected:
            raise ValueError(f"v3 stack pin changed: {key}")
    for path in TOOL_PATHS:
        if v2.git("show", f"HEAD:{path}") != (ROOT / path).read_bytes():
            raise ValueError(f"v3 tool is not committed unchanged: {path}")
    return value, v2.sha(raw)


def binary_paths(directory: Path, name: str) -> dict[str, Path]:
    base = f"s31-mixed_cost_v3_{name}-mixed-general-"
    return {"prover": directory / "package/bin" / (base + "prover"),
            "verifier": directory / "package/bin" / (base + "native-verifier")}


def timed(command: list[str], env: dict[str, str]) -> tuple[subprocess.CompletedProcess[bytes], dict]:
    start = time.perf_counter_ns()
    result = subprocess.run(command, env=env, capture_output=True, check=False)
    end = time.perf_counter_ns()
    return result, {"start": start, "end": end, "duration": end - start}


def anchor_required(protocol_sha: str, model_sha: str | None,
                    anchor_commit: str | None) -> dict:
    if model_sha is None or anchor_commit is None or len(anchor_commit) != 40:
        raise ValueError("full model SHA-256 and anchor commit required before heldout build")
    model_raw, anchor_raw, train_raw = MODEL.read_bytes(), ANCHOR.read_bytes(), TRAIN.read_bytes()
    model, anchor = v2.parse(model_raw), v2.parse(anchor_raw)
    protocol = v2.parse(PROTOCOL.read_bytes())
    train = v2.parse(train_raw)
    check_corpus(train, protocol, "train")
    expected_model = model_from_training(train, protocol_sha, train_raw)
    if (model.get("schema") != "s31-mixed-cost-v3-model" or
            anchor.get("schema") != "s31-mixed-cost-v3-model-anchor" or
            anchor.get("status") != "commit-model-and-anchor-before-heldout-build" or
            model_raw != v2.canonical(expected_model) or
            v2.sha(model_raw) != model_sha or anchor.get("model_sha256") != model_sha or
            model.get("protocol_sha256") != protocol_sha or
            anchor.get("protocol_sha256") != protocol_sha or
            model.get("train_corpus_sha256") != v2.sha(train_raw) or
            anchor.get("train_corpus_sha256") != v2.sha(train_raw) or
            any(v2.git("show", f"{anchor_commit}:{path.relative_to(ROOT).as_posix()}") != raw
                for path, raw in ((MODEL, model_raw), (ANCHOR, anchor_raw), (TRAIN, train_raw))) or
            subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                            anchor_commit, "HEAD"], check=False).returncode):
        raise ValueError("model is not the committed training-only anchor")
    return model


def run(split: str, out: Path, model_sha: str | None, anchor_commit: str | None) -> dict:
    if split not in SPLITS:
        raise ValueError("invalid split")
    protocol, protocol_sha = frozen()
    if split == "heldout":
        anchor_required(protocol_sha, model_sha, anchor_commit)
    target = out / split
    target.mkdir(parents=True, exist_ok=False)
    env = os.environ.copy()
    env.pop("STWO_ZIG_POW_WORKERS", None)
    env["S31_MIXED_NATIVE_PHASES"] = "1"
    records = []
    for shape, count in SPLITS[split]:
        name = f"{shape}_n{count}"
        expected = protocol["split"][split][name]
        directory = target / name
        directory.mkdir()
        raw_source = case(shape, count, 0)[0]
        source_path = directory / "source.s31.json"
        source_path.write_bytes(raw_source)
        built, build_wall = v2.process([
            "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=2",
            "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
            f"-Ds31-name=mixed_cost_v3_{name}", "-j1", "--prefix",
            str(directory / "package")])
        (directory / "build.stdout").write_bytes(built.stdout)
        (directory / "build.stderr").write_bytes(built.stderr)
        if built.returncode:
            raise RuntimeError(f"{name} package build failed")
        bins = binary_paths(directory, name)
        binary_hashes = {role: v2.sha(path.read_bytes()) for role, path in bins.items()}
        trials = []
        for index in range(CLAIMS):
            _, assignment, statement = case(shape, count, index)
            for repeat in range(REPEATS):
                ordinal = index * REPEATS + repeat
                prefix = f"a{index:02d}r{repeat}"
                assignment_path = directory / f"{prefix}.assignment.json"
                statement_path = directory / f"{prefix}.statement.json"
                changed_path = directory / f"{prefix}.changed.json"
                proof_path = directory / f"{prefix}.proof"
                emitted_path = directory / f"{prefix}.emitted.json"
                assignment_path.write_bytes(assignment)
                statement_path.write_bytes(statement)
                changed_path.write_bytes(v2.changed_result(raw_source, statement))
                if {role: v2.sha(path.read_bytes()) for role, path in bins.items()} != binary_hashes:
                    raise ValueError("binary changed during study")
                proved, prove_wall = timed([str(bins["prover"]), str(assignment_path),
                                            str(proof_path), str(emitted_path),
                                            str(statement_path)], env)
                (directory / f"{prefix}.stderr").write_bytes(proved.stderr)
                if proved.returncode or not proof_path.exists() or emitted_path.read_bytes() != statement:
                    raise RuntimeError(f"{name}/{prefix} prover or statement failed")
                verified, verify_wall = timed([str(bins["verifier"]), str(proof_path),
                                               str(statement_path)], env)
                changed, _ = v2.process([str(bins["verifier"]), str(proof_path),
                                         str(changed_path)], env)
                (directory / f"{prefix}.verified.stderr").write_bytes(verified.stderr)
                (directory / f"{prefix}.changed.stderr").write_bytes(changed.stderr)
                if (verified.returncode or b"verified" not in verified.stderr or
                        not v2.proof_layer_rejection(changed)):
                    raise RuntimeError(f"{name}/{prefix} native verifier controls failed")
                stage = v2.tagged(proved.stderr, b"S31_MIXED_STAGE_V1")
                phase = v2.tagged(proved.stderr, b"S31_MIXED_NATIVE_PHASE_V1")
                if stage["source_sha256"] != expected["source_sha256"] or \
                        stage["proof_bytes"] != proof_path.stat().st_size:
                    raise ValueError("source/proof differs from native report")
                partition = project(stage, phase, prove_wall["duration"], verify_wall["duration"])
                trials.append({
                    "ordinal": ordinal, "claim_index": index, "repeat": repeat,
                    "assignment_sha256": v2.sha(assignment),
                    "statement_sha256": v2.sha(statement),
                    "proof_sha256": v2.sha(proof_path.read_bytes()),
                    "proof_bytes": proof_path.stat().st_size,
                    "package_stages_ns": stage["stages_ns"],
                    "native_phases_ns": phase,
                    "partition_ns": partition,
                    "prover_process_monotonic_ns": prove_wall,
                    "external_verifier_process_monotonic_ns": verify_wall,
                    "prover_process_wall_ns": prove_wall["duration"],
                    "external_verifier_process_wall_ns": verify_wall["duration"],
                    "first_verified_process_wall_ns":
                        prove_wall["duration"] + verify_wall["duration"],
                    "changed_result_rejected_at_interaction_nonce": True,
                })
        summary = cold_warm([flatten(t) for t in trials])
        records.append({"name": name, "shape": shape, "call_count": count,
                        "source_sha256": expected["source_sha256"],
                        "binary_sha256": binary_hashes, "build_wall_ns": build_wall,
                        "cold_warm": summary, "trials": trials})
    if any(protocol[key] != value for key, value in pins().items()):
        raise ValueError("stack changed during measurement")
    corpus = {"schema": f"s31-mixed-cost-v3-{split}-corpus",
              "protocol_sha256": protocol_sha, "split": split,
              "host": protocol["host"], "engine_gitlink_commit": protocol["engine_gitlink_commit"],
              "records": records, "native_verified_proofs": len(records) * CLAIMS * REPEATS,
              "changed_result_rejections": len(records) * CLAIMS * REPEATS}
    raw = v2.canonical(corpus)
    (out / f"{split}.json").write_bytes(raw)
    (TRAIN if split == "train" else HELDOUT).write_bytes(raw)
    return {"split": split, "corpus_sha256": v2.sha(raw),
            "verified_proofs": corpus["native_verified_proofs"]}


def flatten(trial: dict) -> dict:
    return {**trial, **trial["partition_ns"],
            "native_prove_including_setup_ns":
                trial["package_stages_ns"]["native_prove_including_setup_ns"]}


def check_corpus(corpus: dict, protocol: dict, split: str) -> None:
    expected = protocol["split"][split]
    total = len(expected) * CLAIMS * REPEATS
    if (corpus.get("schema") != f"s31-mixed-cost-v3-{split}-corpus" or
            corpus.get("protocol_sha256") != v2.sha(PROTOCOL.read_bytes()) or
            corpus.get("split") != split or corpus.get("host") != protocol["host"] or
            corpus.get("engine_gitlink_commit") != protocol["engine_gitlink_commit"] or
            corpus.get("native_verified_proofs") != total or
            corpus.get("changed_result_rejections") != total or
            len(corpus.get("records", [])) != len(expected)):
        raise ValueError("corpus identity or count differs")
    for record, (name, roster_entry) in zip(corpus["records"], expected.items()):
        if (record.get("name") != name or record.get("shape") != roster_entry["shape"] or
                record.get("call_count") != roster_entry["call_count"] or
                record.get("source_sha256") != roster_entry["source_sha256"] or
                len(record.get("trials", [])) != CLAIMS * REPEATS):
            raise ValueError("corpus source differs")
        for ordinal, trial in enumerate(record["trials"]):
            index, repeat = divmod(ordinal, REPEATS)
            if (trial.get("ordinal") != ordinal or trial.get("claim_index") != index or
                    trial.get("repeat") != repeat or
                    trial.get("assignment_sha256") != roster_entry["assignment_sha256"][index] or
                    trial.get("statement_sha256") != roster_entry["statement_sha256"][index] or
                    trial.get("changed_result_rejected_at_interaction_nonce") is not True or
                    type(trial.get("proof_bytes")) is not int or trial["proof_bytes"] <= 0):
                raise ValueError("trial source, order or proof control differs")
            for role, wall_key in (("prover", "prover_process_wall_ns"),
                                   ("external_verifier", "external_verifier_process_wall_ns")):
                endpoints = trial.get(f"{role}_process_monotonic_ns")
                if (type(endpoints) is not dict or set(endpoints) != {"start", "end", "duration"} or
                        any(type(value) is not int or value <= 0 for value in endpoints.values()) or
                        endpoints["end"] - endpoints["start"] != endpoints["duration"] or
                        endpoints["duration"] != trial.get(wall_key)):
                    raise ValueError("monotonic endpoints differ")
            if trial.get("first_verified_process_wall_ns") != (trial["prover_process_wall_ns"] +
                                                               trial["external_verifier_process_wall_ns"]):
                raise ValueError("first verified wall differs")
            stage = {"schema": "s31-mixed-general-prover-stages-v1",
                     "source_sha256": roster_entry["source_sha256"],
                     "circuit_identity_sha256": trial["native_phases_ns"]["circuit_identity_sha256"],
                     "stages_ns": trial["package_stages_ns"]}
            partition = project(stage, trial["native_phases_ns"],
                                trial["prover_process_wall_ns"],
                                trial["external_verifier_process_wall_ns"])
            if partition != trial.get("partition_ns"):
                raise ValueError("disjoint wall accounting differs")
        if record.get("cold_warm") != cold_warm([flatten(t) for t in record["trials"]]):
            raise ValueError("cold/warm partition differs")


def audit(out: Path, split: str, protocol: dict) -> dict:
    raw = (out / f"{split}.json").read_bytes()
    if raw != (TRAIN if split == "train" else HELDOUT).read_bytes():
        raise ValueError("raw and tracked corpus differ")
    corpus = v2.parse(raw)
    check_corpus(corpus, protocol, split)
    checked = 0
    for record in corpus["records"]:
        name, shape, count = record["name"], record["shape"], record["call_count"]
        directory = out / split / name
        source_bytes = case(shape, count, 0)[0]
        if (directory / "source.s31.json").read_bytes() != source_bytes:
            raise ValueError("raw source changed")
        bins = binary_paths(directory, name)
        if {role: v2.sha(path.read_bytes()) for role, path in bins.items()} != record["binary_sha256"]:
            raise ValueError("raw package binary changed")
        for trial in record["trials"]:
            index, repeat = trial["claim_index"], trial["repeat"]
            _, assignment, statement = case(shape, count, index)
            prefix = f"a{index:02d}r{repeat}"
            proof_path = directory / f"{prefix}.proof"
            proof = proof_path.read_bytes()
            statement_path = directory / f"{prefix}.statement.json"
            changed_path = directory / f"{prefix}.changed.json"
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
                    project(stage, phase, trial["prover_process_wall_ns"],
                            trial["external_verifier_process_wall_ns"]) != trial["partition_ns"]):
                raise ValueError("raw timing report differs")
            accepted, _ = v2.process([str(bins["verifier"]), str(proof_path),
                                       str(statement_path)])
            rejected, _ = v2.process([str(bins["verifier"]), str(proof_path),
                                       str(changed_path)])
            if (accepted.stderr != (directory / f"{prefix}.verified.stderr").read_bytes() or
                    rejected.stderr != (directory / f"{prefix}.changed.stderr").read_bytes() or
                    accepted.returncode or b"verified" not in accepted.stderr or
                    not v2.proof_layer_rejection(rejected)):
                raise ValueError("native verifier replay failed")
            checked += 1
    return {"schema": "s31-mixed-cost-v3-native-audit", "split": split,
            "corpus_sha256": v2.sha(raw), "proofs_checked": checked}


def prediction(model: dict, count: int) -> dict[str, float]:
    values = {"warm_first_verified_wall_ns": model["warm_wall_constant_ns"],
              "proof_bytes": model["proof_intercept_bytes"] +
                  count * model["proof_slope_bytes_per_call"]}
    if any(value <= 0 for value in values.values()):
        raise ValueError("nonpositive prediction")
    return values


def model_from_training(corpus: dict, protocol_sha: str, raw: bytes) -> dict:
    """The only accepted fit; anchor replay recomputes these exact bytes."""
    records = corpus["records"]
    xs = [record["call_count"] for record in records]
    wall_medians = [statistics.median(t["first_verified_process_wall_ns"]
                  for t in record["trials"][1:]) for record in records]
    proof_medians = [statistics.median(t["proof_bytes"]
                   for t in record["trials"][1:]) for record in records]
    mx, my = statistics.mean(xs), statistics.mean(proof_medians)
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, proof_medians)) / \
        sum((x - mx) ** 2 for x in xs)
    intercept = my - slope * mx
    if slope <= 0 or intercept <= 0:
        raise ValueError("predeclared positive proof fit failed")
    model = {"schema": "s31-mixed-cost-v3-model", "protocol_sha256": protocol_sha,
             "train_corpus_sha256": v2.sha(raw),
             "training_source_sha256": [r["source_sha256"] for r in records],
             "training_assignment_sha256": [t["assignment_sha256"]
                                             for r in records for t in r["trials"]],
             "training_statement_sha256": [t["statement_sha256"]
                                            for r in records for t in r["trials"]],
             "warm_wall_constant_ns": statistics.median(wall_medians),
             "proof_intercept_bytes": intercept,
             "proof_slope_bytes_per_call": slope,
             "speedup_claim_enabled": False, "automatic_lowering_enabled": False}
    ratios = {target: [] for target in ("warm_first_verified_wall_ns", "proof_bytes")}
    for record in records:
        predicted = prediction(model, record["call_count"])
        for trial in record["trials"][1:]:
            ratios["warm_first_verified_wall_ns"].append(
                trial["first_verified_process_wall_ns"] / predicted["warm_first_verified_wall_ns"])
            ratios["proof_bytes"].append(trial["proof_bytes"] / predicted["proof_bytes"])
    model["training_warm_empirical_ratio_band"] = {
        key: {"lower": min(1.0, v2.quantile(values, .05)),
              "upper": max(1.0, v2.quantile(values, .95))}
        for key, values in ratios.items()}
    return model


def fit(out: Path) -> dict:
    protocol, protocol_sha = frozen()
    if MODEL.exists() or ANCHOR.exists() or (out / "heldout").exists():
        raise ValueError("model exists or heldout started")
    raw = (out / "train.json").read_bytes()
    if raw != TRAIN.read_bytes():
        raise ValueError("training corpus differs from raw")
    corpus = v2.parse(raw)
    check_corpus(corpus, protocol, "train")
    audit(out, "train", protocol)
    model = model_from_training(corpus, protocol_sha, raw)
    MODEL.write_bytes(v2.canonical(model))
    anchor = {"schema": "s31-mixed-cost-v3-model-anchor",
              "protocol_sha256": protocol_sha, "train_corpus_sha256": v2.sha(raw),
              "model_sha256": v2.sha(MODEL.read_bytes()),
              "status": "commit-model-and-anchor-before-heldout-build"}
    ANCHOR.write_bytes(v2.canonical(anchor))
    return {"model_sha256": anchor["model_sha256"],
            "train_corpus_sha256": anchor["train_corpus_sha256"]}


def evaluate(out: Path, model_sha: str, anchor_commit: str) -> dict:
    protocol, protocol_sha = frozen()
    model = anchor_required(protocol_sha, model_sha, anchor_commit)
    if EVALUATION.exists():
        raise ValueError("evaluation already exists")
    train_raw, heldout_raw = TRAIN.read_bytes(), HELDOUT.read_bytes()
    train, heldout = v2.parse(train_raw), v2.parse(heldout_raw)
    check_corpus(train, protocol, "train")
    check_corpus(heldout, protocol, "heldout")
    audit(out, "heldout", protocol)
    if ((out / "train.json").read_bytes() != train_raw or
            (out / "heldout.json").read_bytes() != heldout_raw or
            set(model["training_source_sha256"]) &
                {r["source_sha256"] for r in heldout["records"]} or
            set(model["training_assignment_sha256"]) &
                {t["assignment_sha256"] for r in heldout["records"] for t in r["trials"]} or
            set(model["training_statement_sha256"]) &
                {t["statement_sha256"] for r in heldout["records"] for t in r["trials"]}):
        raise ValueError("corpus changed or heldout leaked into training")
    rows = []
    for record in heldout["records"]:
        predicted = prediction(model, record["call_count"])
        warm = record["trials"][1:]
        targets = {}
        for target, field in (("warm_first_verified_wall_ns", "first_verified_process_wall_ns"),
                              ("proof_bytes", "proof_bytes")):
            values = [trial[field] for trial in warm]
            middle, center = statistics.median(values), predicted[target]
            band = model["training_warm_empirical_ratio_band"][target]
            lower, upper = center * band["lower"], center * band["upper"]
            targets[target] = {"observed_median": middle, "predicted_center": center,
                               "median_relative_error": abs(center - middle) / middle,
                               "covered_warm_trials": sum(lower <= x <= upper for x in values),
                               "warm_trial_count": len(values), "lower": lower, "upper": upper}
        rows.append({"name": record["name"], "shape": record["shape"],
                     "call_count": record["call_count"], "targets": targets,
                     "cold_warm": record["cold_warm"], "build_wall_ns": record["build_wall_ns"]})
    wall, proof = "warm_first_verified_wall_ns", "proof_bytes"
    total = len(rows) * (CLAIMS * REPEATS - 1)
    metrics = {
        "warm_wall_program_p90_relative_error": v2.quantile(
            [row["targets"][wall]["median_relative_error"] for row in rows], .9),
        "proof_program_p90_relative_error": v2.quantile(
            [row["targets"][proof]["median_relative_error"] for row in rows], .9),
        "warm_wall_trial_band_coverage": sum(
            row["targets"][wall]["covered_warm_trials"] for row in rows) / total,
        "proof_trial_band_coverage": sum(
            row["targets"][proof]["covered_warm_trials"] for row in rows) / total,
    }
    gate = protocol["gates"]
    passes = {
        "warm_wall_error": metrics["warm_wall_program_p90_relative_error"] <=
            gate["warm_wall_program_p90_relative_error_max"],
        "proof_error": metrics["proof_program_p90_relative_error"] <=
            gate["proof_program_p90_relative_error_max"],
        "warm_wall_coverage": metrics["warm_wall_trial_band_coverage"] >=
            gate["warm_wall_trial_band_coverage_min"],
        "proof_coverage": metrics["proof_trial_band_coverage"] >=
            gate["proof_trial_band_coverage_min"],
    }
    value = {"schema": "s31-mixed-cost-v3-heldout-evaluation",
             "protocol_sha256": protocol_sha, "model_sha256": model_sha,
             "model_anchor_commit": anchor_commit,
             "train_corpus_sha256": v2.sha(train_raw),
             "heldout_corpus_sha256": v2.sha(heldout_raw),
             "rows": rows, "metrics": metrics, "gate_pass": passes,
             "all_gates_pass": all(passes.values()),
             "cold_accuracy_claim_enabled": False,
             "speedup_claim_enabled": False, "automatic_lowering_enabled": False}
    EVALUATION.write_bytes(v2.canonical(value))
    return {"evaluation_sha256": v2.sha(EVALUATION.read_bytes()),
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
