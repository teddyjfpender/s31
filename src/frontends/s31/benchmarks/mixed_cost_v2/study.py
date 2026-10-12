#!/usr/bin/env python3
"""Prospective mixed whole-prover baseline with a committed model handoff.

Chronology: commit this tool, prepare+commit protocol, collect/audit training,
fit+commit exact model bytes, then collect/audit heldout using model anchor.
"""

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
PROTOCOL = LANGUAGE / "mixed-cost-v2-protocol.json"
MODEL = LANGUAGE / "mixed-cost-v2-model.json"
MODEL_ANCHOR = LANGUAGE / "mixed-cost-v2-model-anchor.json"
TRAIN = LANGUAGE / "mixed-cost-v2-train.json"
HELDOUT = LANGUAGE / "mixed-cost-v2-heldout.json"
EVALUATION = LANGUAGE / "mixed-cost-v2-evaluation.json"
sys.path.insert(0, str(S31 / "benchmarks/mixed_phase_v1"))
sys.path.insert(0, str(S31 / "benchmarks/mixed_stage_cost_transfer_v1"))
from cohort import design as source_design, flat, output_words, source  # noqa: E402
from abi.binding_v2 import statement_from_assignment  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
_phase_spec = importlib.util.spec_from_file_location(
    "mixed_phase_study", S31 / "benchmarks/mixed_phase_v1/study.py")
if _phase_spec is None or _phase_spec.loader is None:
    raise RuntimeError("mixed phase helper is unavailable")
_phase = importlib.util.module_from_spec(_phase_spec)
_phase_spec.loader.exec_module(_phase)
canonical = _phase.canonical
changed_result = _phase.changed_result
current_pins = _phase.current_pins
git = _phase.git
parse = _phase.parse
phase_check = _phase.phase_check
process = _phase.process
proof_layer_rejection = _phase.proof_layer_rejection
sha = _phase.sha
tagged = _phase.tagged

SPLITS = {"train": (("control", 2), ("control", 6), ("deep32", 2), ("deep32", 6)),
          "heldout": (("feeder", 4), ("feeder", 6), ("fork", 4), ("fork", 6))}
ASSIGNMENTS = 20
SEED = 202610119503
P = (1 << 31) - 1
STAGES = ("profile_rebuild_ns", "semantic_evaluation_ns", "topology_compile_ns",
          "witness_compile_ns", "native_prove_including_setup_ns",
          "envelope_and_serialization_ns")
TOOL_PATHS = (
    "src/frontends/s31/benchmarks/mixed_cost_v2/study.py",
    "src/frontends/s31/benchmarks/mixed_phase_v1/study.py",
    "src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/cohort.py",
    "src/frontends/s31/benchmarks/paired_record_v2/design.py",
    "src/frontends/s31/python/abi/binding_v2.py",
    "src/frontends/s31/python/oracle.py",
)
PRIOR_PROTOCOLS = (
    "design/s31/measurements/language/mixed-stage-cost-v1-protocol.json",
    "design/s31/measurements/language/mixed-stage-cost-transfer-v1-protocol.json",
    "design/s31/measurements/language/mixed-phase-v1-protocol.json",
)


def prior_claim_hashes() -> set[str]:
    prior = set()
    for path in PRIOR_PROTOCOLS:
        document = parse((ROOT / path).read_bytes())
        if document["schema"] == "s31-mixed-phase-v1-protocol":
            rows = document["roster"].values()
            keys = ("assignment_sha256", "statement_sha256")
        elif document["schema"] == "s31-mixed-stage-cost-transfer-v1-protocol-candidate":
            rows = document["inventory"].values()
            keys = ("assignment_sha256", "typed_statement_sha256")
        elif document["schema"] == "s31-mixed-stage-cost-v1-protocol":
            rows = [row for split in document["inventory"].values()
                    for row in split.values()]
            keys = ("assignment_sha256", "typed_statement_sha256")
        else:
            raise ValueError("unexpected prior protocol schema")
        for row in rows:
            for key in keys:
                prior.update(row[key])
    return prior


def case(shape: str, count: int, index: int) -> tuple[bytes, bytes, bytes]:
    if (shape, count) not in SPLITS["train"] + SPLITS["heldout"] or \
            not 0 <= index < ASSIGNMENTS:
        raise ValueError("case outside frozen roster")
    raw_source = source(shape, count, source_design())
    relation = parse(raw_source)
    family = [item for split in SPLITS.values() for item in split].index((shape, count))
    seed = SEED + family * 10_000_000 + count * 100_000 + index * 37
    words = [(seed * (lane + 19) + lane * lane + 7) % P for lane in range(4)]
    output = output_words(shape, count, words)
    assignment = {"public_inputs": {relation["inputs"][0]["name"]: words},
                  "private_inputs": {},
                  "public_outputs": {relation["public_outputs"][0]: output}}
    if evaluate_relation(flat(relation), assignment) != assignment["public_outputs"]:
        raise ValueError("independent relation oracle disagrees with case output")
    typed = statement_from_assignment(relation, assignment)
    changed_result(raw_source, typed)  # both eight-word claims must decode
    return raw_source, canonical(assignment), typed


def pins() -> dict:
    return {**current_pins(),
            "study_tool_sha256": {path: sha((ROOT / path).read_bytes())
                                  for path in TOOL_PATHS},
            "prior_protocol_sha256": {path: sha((ROOT / path).read_bytes())
                                      for path in PRIOR_PROTOCOLS}}


def prepare() -> dict:
    if PROTOCOL.exists():
        raise ValueError("prospective protocol already exists")
    changed = git("diff", "--name-only", "HEAD", "--", "src").decode().splitlines()
    if any(path.endswith((".zig", ".zon")) for path in changed):
        raise ValueError("commit Zig compiler/runtime sources before protocol freeze")
    roster = {}
    for split, sources in SPLITS.items():
        group = {}
        for shape, count in sources:
            rows = [case(shape, count, index) for index in range(ASSIGNMENTS)]
            name = f"{shape}_n{count}"
            group[name] = {"shape": shape, "call_count": count,
                           "total_rounds": count * (32 if shape == "deep32" else 16),
                           "source_sha256": sha(rows[0][0]),
                           "assignment_sha256": [sha(row[1]) for row in rows],
                           "statement_sha256": [sha(row[2]) for row in rows]}
        roster[split] = group
    assignments = [h for group in roster.values() for row in group.values()
                   for h in row["assignment_sha256"]]
    statements = [h for group in roster.values() for row in group.values()
                  for h in row["statement_sha256"]]
    if len(set(assignments)) != 160 or len(set(statements)) != 160:
        raise ValueError("duplicate prospective assignments or claims")
    if (set(assignments) | set(statements)) & prior_claim_hashes():
        raise ValueError("prospective claim reused prior evidence")
    value = {"schema": "s31-mixed-cost-v2-protocol", "status": "pre-native-frozen",
             "assignment_seed": SEED, "assignments_per_source": ASSIGNMENTS,
             "split": roster, "build_mode": "ReleaseFast",
             "lowering": "direct-mixed-general", "timed_native_phases": True,
             "proof_negative_error": "InvalidMixedInteractionNonce",
             "first_verified_wall": "fresh prover process plus fresh native verifier process",
             "model": {"first_verified_process_wall_ns": "median-of-four-training-program-medians",
                       "proof_bytes": "ordinary-least-squares-linear-in-call-count-on-four-training-program-medians",
                       "proof_constant_baseline": "median-of-four-training-program-medians",
                       "ratio_band": "training-trial-5th-and-95th-percentiles-clamped-to-include-one"},
             "gates": {"wall_program_p90_median_relative_error_max": 0.30,
                       "proof_program_p90_median_relative_error_max": 0.10,
                       "wall_trial_interval_coverage_min": 0.70,
                       "proof_trial_interval_coverage_min": 0.80},
             "speedup_claim_enabled": False, "automatic_lowering_enabled": False,
             **pins()}
    PROTOCOL.write_bytes(canonical(value))
    return {"protocol_sha256": sha(PROTOCOL.read_bytes()),
            "train_sources": len(roster["train"]), "heldout_sources": len(roster["heldout"])}


def frozen() -> tuple[dict, str]:
    raw = PROTOCOL.read_bytes()
    protocol = parse(raw)
    if (raw != canonical(protocol) or protocol.get("schema") != "s31-mixed-cost-v2-protocol" or
            protocol.get("status") != "pre-native-frozen" or
            protocol.get("assignment_seed") != SEED or
            protocol.get("assignments_per_source") != ASSIGNMENTS or
            protocol.get("model") != {
                "first_verified_process_wall_ns": "median-of-four-training-program-medians",
                "proof_bytes": "ordinary-least-squares-linear-in-call-count-on-four-training-program-medians",
                "proof_constant_baseline": "median-of-four-training-program-medians",
                "ratio_band": "training-trial-5th-and-95th-percentiles-clamped-to-include-one"} or
            protocol.get("gates") != {"wall_program_p90_median_relative_error_max": .30,
                                      "proof_program_p90_median_relative_error_max": .10,
                                      "wall_trial_interval_coverage_min": .70,
                                      "proof_trial_interval_coverage_min": .80} or
            protocol.get("speedup_claim_enabled") is not False or
            protocol.get("automatic_lowering_enabled") is not False or
            git("show", f"HEAD:{PROTOCOL.relative_to(ROOT).as_posix()}") != raw):
        raise ValueError("prospective protocol not committed unchanged")
    for key, value in pins().items():
        if protocol[key] != value:
            raise ValueError(f"prospective stack pin changed: {key}")
    for split, sources in SPLITS.items():
        if list(protocol["split"][split]) != [f"{shape}_n{count}" for shape, count in sources]:
            raise ValueError("source split changed")
        for shape, count in sources:
            name = f"{shape}_n{count}"
            rows = [case(shape, count, index) for index in range(ASSIGNMENTS)]
            expected = protocol["split"][split][name]
            if (expected["source_sha256"] != sha(rows[0][0]) or
                    expected["assignment_sha256"] != [sha(row[1]) for row in rows] or
                    expected["statement_sha256"] != [sha(row[2]) for row in rows]):
                raise ValueError("prospective source or claim changed")
    return protocol, sha(raw)


def binary_paths(directory: Path, name: str) -> dict[str, Path]:
    base = f"s31-mixed_cost_v2_{name}-mixed-general-"
    return {"prover": directory / "package/bin" / (base + "prover"),
            "verifier": directory / "package/bin" / (base + "native-verifier")}


def timed_process(command: list[str], env: dict[str, str]) -> tuple[subprocess.CompletedProcess[bytes], dict]:
    start = time.perf_counter_ns()
    result = subprocess.run(command, env=env, capture_output=True, check=False)
    end = time.perf_counter_ns()
    return result, {"start": start, "end": end, "duration": end - start}


def run_split(split: str, out: Path, model_sha256: str | None = None,
              model_anchor_commit: str | None = None) -> dict:
    if split not in SPLITS:
        raise ValueError("invalid split")
    protocol, protocol_sha = frozen()
    if split == "heldout":
        require_model_anchor(protocol_sha, model_sha256, model_anchor_commit)
    target = out / split
    target.mkdir(parents=True, exist_ok=False)
    records = []
    env = os.environ.copy()
    env.pop("STWO_ZIG_POW_WORKERS", None)
    env["S31_MIXED_NATIVE_PHASES"] = "1"
    for shape, count in SPLITS[split]:
        name = f"{shape}_n{count}"
        expected = protocol["split"][split][name]
        directory = target / name
        directory.mkdir()
        raw_source = case(shape, count, 0)[0]
        source_path = directory / "source.s31.json"
        source_path.write_bytes(raw_source)
        command = ["zig", "build", "--build-file", str(S31 / "build.zig"), "install",
                   "-Doptimize=ReleaseFast", "-Ds31-version=2",
                   "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
                   f"-Ds31-name=mixed_cost_v2_{name}", "-j1", "--prefix",
                   str(directory / "package")]
        built, build_wall = process(command)
        (directory / "build.stdout").write_bytes(built.stdout)
        (directory / "build.stderr").write_bytes(built.stderr)
        if built.returncode:
            raise RuntimeError(f"{name} package build failed: {built.stderr.decode(errors='replace')[-1500:]}")
        bins = binary_paths(directory, name)
        binaries = {role: sha(path.read_bytes()) for role, path in bins.items()}
        trials = []
        for index in range(ASSIGNMENTS):
            _, assignment, statement = case(shape, count, index)
            prefix = f"a{index:02d}"
            assignment_path = directory / f"{prefix}.assignment.json"
            statement_path = directory / f"{prefix}.statement.json"
            changed_path = directory / f"{prefix}.changed.json"
            proof_path = directory / f"{prefix}.proof"
            emitted_path = directory / f"{prefix}.emitted.json"
            assignment_path.write_bytes(assignment)
            statement_path.write_bytes(statement)
            changed_path.write_bytes(changed_result(raw_source, statement))
            if {role: sha(path.read_bytes()) for role, path in bins.items()} != binaries:
                raise ValueError("binary changed during study")
            proved, prove_time = timed_process([str(bins["prover"]), str(assignment_path),
                                                str(proof_path), str(emitted_path),
                                                str(statement_path)], env)
            (directory / f"{prefix}.stderr").write_bytes(proved.stderr)
            if proved.returncode or not proof_path.exists() or \
                    emitted_path.read_bytes() != statement:
                raise RuntimeError(f"{name}/{prefix} prover or statement failed")
            verified, verify_time = timed_process([str(bins["verifier"]), str(proof_path),
                                                   str(statement_path)], env)
            changed, _ = process([str(bins["verifier"]), str(proof_path),
                                  str(changed_path)], env)
            (directory / f"{prefix}.verified.stderr").write_bytes(verified.stderr)
            (directory / f"{prefix}.changed.stderr").write_bytes(changed.stderr)
            if verified.returncode or b"verified" not in verified.stderr or \
                    not proof_layer_rejection(changed):
                raise RuntimeError(f"{name}/{prefix} native proof controls failed")
            stage = tagged(proved.stderr, b"S31_MIXED_STAGE_V1")
            phase = tagged(proved.stderr, b"S31_MIXED_NATIVE_PHASE_V1")
            timing = phase_check(stage, phase, prove_time["duration"])
            if stage["source_sha256"] != expected["source_sha256"] or \
                    stage["proof_bytes"] != proof_path.stat().st_size:
                raise ValueError("source or proof size differs from stage report")
            package = stage["stages_ns"]
            trials.append({"assignment_sha256": sha(assignment),
                           "statement_sha256": sha(statement),
                           "proof_sha256": sha(proof_path.read_bytes()),
                           "proof_bytes": proof_path.stat().st_size,
                           "package_stages_ns": package,
                           "native_phases_ns": timing,
                           "prover_process_monotonic_ns": prove_time,
                           "external_verifier_process_monotonic_ns": verify_time,
                           "prover_process_wall_ns": prove_time["duration"],
                           "external_verifier_process_wall_ns": verify_time["duration"],
                           "first_verified_process_wall_ns":
                               prove_time["duration"] + verify_time["duration"],
                           "changed_result_rejected_at_interaction_nonce": True})
        records.append({"name": name, "shape": shape, "call_count": count,
                        "total_rounds": expected["total_rounds"],
                        "source_sha256": expected["source_sha256"],
                        "binary_sha256": binaries, "build_wall_ns": build_wall,
                        "trials": trials})
    if {key: protocol[key] for key in pins()} != pins():
        raise ValueError("stack changed during native split")
    corpus = {"schema": f"s31-mixed-cost-v2-{split}-corpus",
              "protocol_sha256": protocol_sha, "split": split,
              "host": protocol["host"], "engine_gitlink_commit":
                  protocol["engine_gitlink_commit"], "records": records,
              "native_verified_proofs": len(records) * ASSIGNMENTS,
              "changed_result_rejections": len(records) * ASSIGNMENTS}
    (out / f"{split}.json").write_bytes(canonical(corpus))
    (TRAIN if split == "train" else HELDOUT).write_bytes(canonical(corpus))
    return {"split": split, "corpus_sha256": sha(canonical(corpus)),
            "verified_proofs": corpus["native_verified_proofs"]}


def quantile(values: list[float], fraction: float) -> float:
    ordered = sorted(values)
    rank = fraction * (len(ordered) - 1)
    low = int(rank)
    return ordered[low] + (ordered[min(low + 1, len(ordered) - 1)] - ordered[low]) * (rank - low)


def prediction(model: dict, count: int) -> dict:
    wall = model["wall_constant_ns"]
    proof = model["proof_intercept_bytes"] + count * model["proof_slope_bytes_per_call"]
    if wall <= 0 or proof <= 0:
        raise ValueError("invalid fitted prediction")
    return {"first_verified_process_wall_ns": wall, "proof_bytes": proof}


def fit(out: Path) -> dict:
    protocol, protocol_sha = frozen()
    if MODEL.exists() or MODEL_ANCHOR.exists() or (out / "heldout").exists():
        raise ValueError("model exists or heldout work started")
    raw = (out / "train.json").read_bytes()
    if raw != TRAIN.read_bytes():
        raise ValueError("training raw and tracked corpus differ")
    corpus = parse(raw)
    check_corpus(corpus, protocol, "train")
    audit_split(out, "train", protocol)
    programs = corpus["records"]
    xs = [record["call_count"] for record in programs]
    wall_medians = [statistics.median(t["first_verified_process_wall_ns"] for t in record["trials"])
                    for record in programs]
    proof_medians = [statistics.median(t["proof_bytes"] for t in record["trials"])
                     for record in programs]
    wall = statistics.median(wall_medians)
    mx, my = statistics.mean(xs), statistics.mean(proof_medians)
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, proof_medians)) / \
            sum((x - mx) ** 2 for x in xs)
    intercept = my - slope * mx
    if slope <= 0 or intercept <= 0:
        raise ValueError("predeclared positive proof size fit failed")
    model = {"schema": "s31-mixed-cost-v2-model",
             "protocol_sha256": protocol_sha, "train_corpus_sha256": sha(raw),
             "training_source_sha256": [r["source_sha256"] for r in programs],
             "training_assignment_sha256": [t["assignment_sha256"] for r in programs for t in r["trials"]],
             "training_statement_sha256": [t["statement_sha256"] for r in programs for t in r["trials"]],
             "wall_constant_ns": wall, "proof_intercept_bytes": intercept,
             "proof_slope_bytes_per_call": slope,
             "proof_constant_baseline_bytes": statistics.median(proof_medians),
             "speedup_claim_enabled": False, "automatic_lowering_enabled": False}
    ratios = {target: [] for target in ("first_verified_process_wall_ns", "proof_bytes")}
    for record in programs:
        predicted = prediction(model, record["call_count"])
        for trial in record["trials"]:
            for target in ratios:
                ratios[target].append(trial[target] / predicted[target])
    model["training_empirical_ratio_band"] = {
        target: {"lower": min(1.0, quantile(values, .05)),
                 "upper": max(1.0, quantile(values, .95))}
        for target, values in ratios.items()}
    MODEL.write_bytes(canonical(model))
    anchor = {"schema": "s31-mixed-cost-v2-model-anchor",
              "protocol_sha256": protocol_sha,
              "train_corpus_sha256": sha(raw), "model_sha256": sha(MODEL.read_bytes()),
              "status": "commit-model-and-anchor-before-heldout-build"}
    MODEL_ANCHOR.write_bytes(canonical(anchor))
    return {"model_sha256": anchor["model_sha256"],
            "train_corpus_sha256": anchor["train_corpus_sha256"]}


def require_model_anchor(protocol_sha: str, model_sha: str | None,
                         anchor_commit: str | None) -> dict:
    if model_sha is None or anchor_commit is None or len(anchor_commit) != 40:
        raise ValueError("full committed model hash and anchor commit required")
    model_raw, anchor_raw = MODEL.read_bytes(), MODEL_ANCHOR.read_bytes()
    model, anchor = parse(model_raw), parse(anchor_raw)
    if (sha(model_raw) != model_sha or anchor.get("model_sha256") != model_sha or
            anchor.get("protocol_sha256") != protocol_sha or
            model.get("protocol_sha256") != protocol_sha or
            model.get("train_corpus_sha256") != anchor.get("train_corpus_sha256") or
            sha(TRAIN.read_bytes()) != anchor.get("train_corpus_sha256") or
            git("show", f"{anchor_commit}:{MODEL.relative_to(ROOT).as_posix()}") != model_raw or
            git("show", f"{anchor_commit}:{MODEL_ANCHOR.relative_to(ROOT).as_posix()}") != anchor_raw or
            git("show", f"{anchor_commit}:{TRAIN.relative_to(ROOT).as_posix()}") != TRAIN.read_bytes() or
            subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                            anchor_commit, "HEAD"], check=False).returncode):
        raise ValueError("model artifact is not the committed training-only anchor")
    return model


def check_corpus(corpus: dict, protocol: dict, split: str) -> None:
    expected = protocol["split"][split]
    if (corpus.get("schema") != f"s31-mixed-cost-v2-{split}-corpus" or
            corpus.get("protocol_sha256") != sha(PROTOCOL.read_bytes()) or
            corpus.get("split") != split or corpus.get("host") != protocol["host"] or
            corpus.get("engine_gitlink_commit") != protocol["engine_gitlink_commit"] or
            corpus.get("native_verified_proofs") != len(expected) * ASSIGNMENTS or
            corpus.get("changed_result_rejections") != len(expected) * ASSIGNMENTS or
            len(corpus.get("records", [])) != len(expected)):
        raise ValueError("corpus identity or count differs from prospective protocol")
    for record, (name, roster) in zip(corpus["records"], expected.items()):
        if (record.get("name") != name or record.get("shape") != roster["shape"] or
                record.get("call_count") != roster["call_count"] or
                record.get("source_sha256") != roster["source_sha256"] or
                len(record.get("trials", [])) != ASSIGNMENTS):
            raise ValueError("corpus source differs from split roster")
        for index, trial in enumerate(record["trials"]):
            if (trial.get("assignment_sha256") != roster["assignment_sha256"][index] or
                    trial.get("statement_sha256") != roster["statement_sha256"][index] or
                    trial.get("changed_result_rejected_at_interaction_nonce") is not True or
                    any(type(trial.get(key)) is not int or trial[key] <= 0 for key in
                        ("first_verified_process_wall_ns", "proof_bytes",
                         "prover_process_wall_ns", "external_verifier_process_wall_ns")) or
                    trial["first_verified_process_wall_ns"] !=
                        trial["prover_process_wall_ns"] +
                        trial["external_verifier_process_wall_ns"]):
                raise ValueError("corpus trial differs from frozen claim or target")
            for role, key in (("prover", "prover_process_wall_ns"),
                              ("external_verifier", "external_verifier_process_wall_ns")):
                elapsed = trial.get(f"{role}_process_monotonic_ns")
                if (type(elapsed) is not dict or set(elapsed) != {"start", "end", "duration"} or
                        any(type(value) is not int or value <= 0 for value in elapsed.values()) or
                        elapsed["end"] - elapsed["start"] != elapsed["duration"] or
                        elapsed["duration"] != trial[key]):
                    raise ValueError("monotonic process wall endpoints differ")
            stages = trial.get("package_stages_ns")
            phases = trial.get("native_phases_ns")
            if (type(stages) is not dict or set(stages) != {*STAGES, "package_total_ns"} or
                    any(type(value) is not int or value < 0 for value in stages.values()) or
                    stages["package_total_ns"] != sum(stages[key] for key in STAGES) or
                    stages["package_total_ns"] > trial["prover_process_wall_ns"] or
                    type(phases) is not dict or
                    phases.get("native_prove_including_setup_ns") !=
                        stages["native_prove_including_setup_ns"]):
                raise ValueError("corpus package stage accounting differs")


def audit_split(out: Path, split: str, protocol: dict) -> dict:
    """Read-only raw evidence replay, including both native verifier outcomes."""
    raw = (out / f"{split}.json").read_bytes()
    tracked = TRAIN if split == "train" else HELDOUT
    if raw != tracked.read_bytes():
        raise ValueError("raw and tracked corpus differ")
    corpus = parse(raw)
    check_corpus(corpus, protocol, split)
    checks = 0
    for record in corpus["records"]:
        name, shape, count = record["name"], record["shape"], record["call_count"]
        directory = out / split / name
        source_bytes = case(shape, count, 0)[0]
        if (directory / "source.s31.json").read_bytes() != source_bytes:
            raise ValueError("raw source changed")
        bins = binary_paths(directory, name)
        if {role: sha(path.read_bytes()) for role, path in bins.items()} != record["binary_sha256"]:
            raise ValueError("raw package binary changed")
        for index, trial in enumerate(record["trials"]):
            _, assignment, statement = case(shape, count, index)
            prefix = f"a{index:02d}"
            proof_path = directory / f"{prefix}.proof"
            proof_bytes = proof_path.read_bytes()
            statement_path = directory / f"{prefix}.statement.json"
            changed_path = directory / f"{prefix}.changed.json"
            if ((directory / f"{prefix}.assignment.json").read_bytes() != assignment or
                    statement_path.read_bytes() != statement or
                    changed_path.read_bytes() != changed_result(source_bytes, statement) or
                    (directory / f"{prefix}.emitted.json").read_bytes() != statement or
                    sha(proof_bytes) != trial["proof_sha256"] or
                    len(proof_bytes) != trial["proof_bytes"]):
                raise ValueError("raw trial source, claim or proof changed")
            stderr = (directory / f"{prefix}.stderr").read_bytes()
            stage = tagged(stderr, b"S31_MIXED_STAGE_V1")
            phase = tagged(stderr, b"S31_MIXED_NATIVE_PHASE_V1")
            if (stage["source_sha256"] != record["source_sha256"] or
                    stage["proof_bytes"] != len(proof_bytes) or
                    stage["stages_ns"] != trial["package_stages_ns"] or
                    phase_check(stage, phase, trial["prover_process_wall_ns"]) !=
                        trial["native_phases_ns"]):
                raise ValueError("raw stage or phase accounting changed")
            accepted, _ = process([str(bins["verifier"]), str(proof_path),
                                   str(statement_path)])
            rejected, _ = process([str(bins["verifier"]), str(proof_path),
                                   str(changed_path)])
            if (accepted.stderr != (directory / f"{prefix}.verified.stderr").read_bytes() or
                    rejected.stderr != (directory / f"{prefix}.changed.stderr").read_bytes() or
                    accepted.returncode or b"verified" not in accepted.stderr or
                    not proof_layer_rejection(rejected)):
                raise ValueError("native verifier replay failed")
            checks += 1
    return {"schema": "s31-mixed-cost-v2-native-audit", "split": split,
            "corpus_sha256": sha(raw), "proofs_verified_and_changed_claims_rejected": checks}


def evaluate(out: Path, model_sha: str, anchor_commit: str) -> dict:
    protocol, protocol_sha = frozen()
    model = require_model_anchor(protocol_sha, model_sha, anchor_commit)
    if EVALUATION.exists():
        raise ValueError("heldout evaluation already exists")
    train_raw, heldout_raw = TRAIN.read_bytes(), HELDOUT.read_bytes()
    train, heldout = parse(train_raw), parse(heldout_raw)
    check_corpus(train, protocol, "train")
    check_corpus(heldout, protocol, "heldout")
    audit_split(out, "heldout", protocol)
    if (sha(train_raw) != model["train_corpus_sha256"] or
            (out / "train.json").read_bytes() != train_raw or
            (out / "heldout.json").read_bytes() != heldout_raw):
        raise ValueError("train/heldout corpus differs from frozen model and raw work")
    train_sources = set(model["training_source_sha256"])
    train_assignments = set(model["training_assignment_sha256"])
    train_statements = set(model["training_statement_sha256"])
    if (train_sources & {r["source_sha256"] for r in heldout["records"]} or
            train_assignments & {t["assignment_sha256"] for r in heldout["records"] for t in r["trials"]} or
            train_statements & {t["statement_sha256"] for r in heldout["records"] for t in r["trials"]}):
        raise ValueError("heldout leakage into training model")
    rows = []
    proof_baseline_errors = []
    for record in heldout["records"]:
        predicted = prediction(model, record["call_count"])
        targets = {}
        for target in predicted:
            actual = [t[target] for t in record["trials"]]
            middle = statistics.median(actual)
            center = predicted[target]
            band = model["training_empirical_ratio_band"][target]
            lower, upper = center * band["lower"], center * band["upper"]
            targets[target] = {"observed_median": middle, "predicted_center": center,
                               "median_relative_error": abs(center - middle) / middle,
                               "covered_trials": sum(lower <= x <= upper for x in actual),
                               "trial_count": len(actual), "lower": lower, "upper": upper}
        rows.append({"name": record["name"], "shape": record["shape"],
                     "call_count": record["call_count"], "targets": targets,
                     "build_wall_ns": record["build_wall_ns"]})
        proof_baseline_errors.append(abs(model["proof_constant_baseline_bytes"] -
            targets["proof_bytes"]["observed_median"]) /
            targets["proof_bytes"]["observed_median"])
    gate = protocol["gates"]
    wall = "first_verified_process_wall_ns"
    metrics = {"wall_program_p90_median_relative_error": quantile(
                   [r["targets"][wall]["median_relative_error"] for r in rows], .9),
               "proof_program_p90_median_relative_error": quantile(
                   [r["targets"]["proof_bytes"]["median_relative_error"] for r in rows], .9),
               "wall_trial_interval_coverage": sum(r["targets"][wall]["covered_trials"] for r in rows) / 80,
               "proof_trial_interval_coverage": sum(r["targets"]["proof_bytes"]["covered_trials"] for r in rows) / 80,
               "wall_mean_program_median_relative_error": statistics.mean(
                   r["targets"][wall]["median_relative_error"] for r in rows),
               "proof_mean_program_median_relative_error": statistics.mean(
                   r["targets"]["proof_bytes"]["median_relative_error"] for r in rows),
               "proof_constant_baseline_p90_median_relative_error": quantile(proof_baseline_errors, .9)}
    metrics["wall_program_median_absolute_percentage_error"] = statistics.median(
        r["targets"][wall]["median_relative_error"] for r in rows)
    metrics["proof_program_median_absolute_percentage_error"] = statistics.median(
        r["targets"]["proof_bytes"]["median_relative_error"] for r in rows)
    passes = {"wall_error": metrics["wall_program_p90_median_relative_error"] <=
              gate["wall_program_p90_median_relative_error_max"],
              "proof_error": metrics["proof_program_p90_median_relative_error"] <=
              gate["proof_program_p90_median_relative_error_max"],
              "wall_coverage": metrics["wall_trial_interval_coverage"] >=
              gate["wall_trial_interval_coverage_min"],
              "proof_coverage": metrics["proof_trial_interval_coverage"] >=
              gate["proof_trial_interval_coverage_min"]}
    result = {"schema": "s31-mixed-cost-v2-heldout-evaluation",
              "protocol_sha256": protocol_sha, "model_sha256": model_sha,
              "model_anchor_commit": anchor_commit, "train_corpus_sha256": sha(train_raw),
              "heldout_corpus_sha256": sha(heldout_raw),
              "rows": rows, "metrics": metrics, "gate_pass": passes,
              "all_gates_pass": all(passes.values()),
              "speedup_claim_enabled": False, "automatic_lowering_enabled": False}
    EVALUATION.write_bytes(canonical(result))
    return {"evaluation_sha256": sha(EVALUATION.read_bytes()),
            "all_gates_pass": result["all_gates_pass"], "metrics": metrics}


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
        value = prepare()
    elif args.action == "train":
        value = run_split("train", args.out.resolve())
    elif args.action in ("audit-train", "audit-heldout"):
        value = audit_split(args.out.resolve(), args.action.split("-", 1)[1], frozen()[0])
    elif args.action == "fit":
        value = fit(args.out.resolve())
    elif args.action == "heldout":
        value = run_split("heldout", args.out.resolve(), args.model_sha256,
                          args.model_anchor_commit)
    else:
        value = evaluate(args.out.resolve(), args.model_sha256,
                         args.model_anchor_commit)
    print(json.dumps(value, sort_keys=True))


if __name__ == "__main__":
    main()
