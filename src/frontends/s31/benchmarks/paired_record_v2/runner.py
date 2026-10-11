"""Frozen paired v2 native build, verified trials, and replay.

This is a separate study from V8. Native work requires a committed protocol,
committed timestamp anchor, externally recorded hashes, pinned host/stack,
and a clean evidence directory. Do not run alongside another timed study.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import random
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/acceptance/mixed_boundary"))

import s31
from abi.binding_v2 import statement_from_assignment
from oracle import evaluate_relation
from package.context import parse_source_json
from registry_manifest_digest import digest as registry_digest
from design import canonical, case, design, flat, sha
from integrity import (BUILD_EVENT_SCHEMA, EVENT_SCHEMA, GENESIS, append_event,
                       build_root, check_phase_anchor, check_report_anchor, durable_write,
                       fsync_existing, observed_invoke, phase_root,
                       read_ledger, replay_process)
from protocol import check

P = (1 << 31) - 1
PCS_FIELDS = {"fri_config", "trace_lifting_log_size", "preprocessed_lifting_log_size"}
FRI_FIELDS = {"pow_bits", "log_blowup_factor", "log_last_layer_degree_bound",
              "n_queries", "fold_step"}


def saved_json(path: Path, value: object) -> None:
    path.write_bytes(canonical(value))


def check_disk_space(out: Path, minimum: int) -> None:
    """Check each filesystem used for packages, global Zig cache, and temp files."""
    global_cache = os.environ.get("ZIG_GLOBAL_CACHE_DIR") or str(Path.home() / ".cache/zig")
    locations = (out.parent, S31 / ".zig-cache", Path(global_cache),
                 Path(tempfile.gettempdir()))
    devices = set()
    for location in locations:
        path = location.resolve()
        while not path.exists():
            path = path.parent
        device = path.stat().st_dev
        if device in devices:
            continue
        devices.add(device)
        if shutil.disk_usage(path).free < minimum:
            raise ValueError(f"paired native unit requires at least 8 GiB free on {path}")


def require_static_case(directory: Path, count: int, index: int, cfg: dict, expected: dict) -> None:
    source_bytes, assignment_bytes, typed = case(count, index, cfg)
    if (sha(source_bytes) != expected["source_sha256"] or
            sha(assignment_bytes) != expected["assignment_sha256"][index] or
            sha(typed) != expected["statement_sha256"][index] or
            (directory / "source.s31.json").read_bytes() != source_bytes or
            (directory / f"assignments/{index:02d}.json").read_bytes() != assignment_bytes or
            (directory / f"statements/{index:02d}.json").read_bytes() != typed):
        raise ValueError(f"N={count}, assignment={index}: frozen source/assignment/statement changed")


def materialize(directory: Path, count: int, cfg: dict, expected: dict) -> None:
    directory.mkdir(parents=True, exist_ok=False)
    (directory / "assignments").mkdir()
    (directory / "statements").mkdir()
    for index in range(cfg["assignments_per_call_count"]):
        source_bytes, assignment, statement = case(count, index, cfg)
        if index == 0:
            (directory / "source.s31.json").write_bytes(source_bytes)
        elif source_bytes != (directory / "source.s31.json").read_bytes():
            raise ValueError("source changed inside one paired case")
        (directory / f"assignments/{index:02d}.json").write_bytes(assignment)
        (directory / f"statements/{index:02d}.json").write_bytes(statement)
        require_static_case(directory, count, index, cfg, expected)


def mixed_bins(directory: Path, name: str) -> tuple[Path, Path, Path]:
    root = directory / "mixed" / "bin"
    return (root / f"s31-{name}-mixed-general-prover",
            root / f"s31-{name}-mixed-general-native-verifier",
            root / f"s31-{name}-mixed-general-manifest")


def generic_bins(directory: Path, name: str) -> tuple[Path, Path, Path]:
    root = directory / "generic" / "bin"
    return (root / f"s31-{name}-prover",
            root / f"s31-{name}-native-verifier",
            directory / "generic" / "verification-key.json")


def package_identity(directory: Path, count: int, expected: dict, compiler: str) -> dict:
    source_path = directory / "source.s31.json"
    name = json.loads(source_path.read_bytes())["name"]
    generic = s31.verify_package(directory / "generic")
    cost = json.loads((directory / "generic/cost-report.json").read_bytes())
    gp, gv, gk = generic_bins(directory, name)
    mp, mv, mm = mixed_bins(directory, name)
    report = json.loads(subprocess.check_output([str(mm)], text=True))
    report_bytes = canonical(report)
    inspection_path = directory / "mixed-inspection.json"
    if inspection_path.read_bytes() != report_bytes:
        raise ValueError("source-embedded mixed inspection differs from saved audit artifact")
    generic_pcs = cost.get("pcs")
    mixed_pcs = report.get("pcs")
    if (not isinstance(generic_pcs, dict) or not isinstance(mixed_pcs, dict) or
            set(generic_pcs) != PCS_FIELDS or set(mixed_pcs) != PCS_FIELDS or
            not isinstance(generic_pcs.get("fri_config"), dict) or
            not isinstance(mixed_pcs.get("fri_config"), dict) or
            any(set(pcs["fri_config"]) != FRI_FIELDS or
                any(type(value) is not int or value < 0 for value in pcs["fri_config"].values())
                for pcs in (generic_pcs, mixed_pcs)) or
            generic_pcs["fri_config"] != mixed_pcs["fri_config"] or
            any(type(pcs.get(field)) is not int or pcs[field] < 0
                for pcs in (generic_pcs, mixed_pcs)
                for field in ("trace_lifting_log_size", "preprocessed_lifting_log_size")) or
            type(cost.get("interaction_pow_bits")) is not int or
            type(report.get("interaction_pow_bits")) is not int or
            cost["interaction_pow_bits"] <= 0 or
            cost["interaction_pow_bits"] != report["interaction_pow_bits"]):
        raise ValueError("live generic/mixed PCS, FRI, or interaction PoW profile is absent or incompatible")
    live_fri = generic_pcs["fri_config"]
    sealed_fri = cost.get("fri", {})
    last_layer = sealed_fri.get("last_layer_degree_bound")
    if (type(last_layer) is not int or last_layer <= 0 or last_layer & (last_layer - 1) or
            live_fri.get("pow_bits") != sealed_fri.get("pow_bits") or
            live_fri.get("log_blowup_factor") != sealed_fri.get("log_blowup_factor") or
            live_fri.get("n_queries") != sealed_fri.get("queries") or
            live_fri.get("log_last_layer_degree_bound") != last_layer.bit_length() - 1 or
            live_fri.get("fold_step") != sealed_fri.get("fold_step")):
        raise ValueError("live direct-gate FRI configuration differs from sealed package report")
    if (generic["name"] != name or generic["lowering"] != "direct-gate" or
            generic["optimize"] != "ReleaseFast" or
            generic["compiler_sha256"] != compiler or
            generic["program_sha256"] != expected["source_sha256"] or
            (directory / "generic/source.s31.json").read_bytes() != source_path.read_bytes() or
            cost["profile"] != "direct-m31-v4" or
            cost["public_abi_sha256"] != expected["public_record_abi_sha256"] or
            report.get("schema") != "s31-mixed-component-inspection-general-v3" or
            report.get("profile") != "experimental-direct-mixed-general" or
            report.get("source_sha256") != expected["source_sha256"] or
            report.get("canonical_ir_sha256") != cost["canonical_ir_sha256"] or
            report.get("call_count") != count or
            report.get("slot_count") != 1 + 2 * count or
            report.get("registry_manifest_sha256") != registry_digest(report) or
            report.get("circuit_identity_sha256") is None):
        raise ValueError(f"N={count}: generic/mixed package identities differ from frozen source")
    if cost.get("fri") != {"pow_bits": 26, "log_blowup_factor": 1,
                            "last_layer_degree_bound": 1, "queries": 70,
                            "fold_step": 1}:
        raise ValueError("generic FRI settings differ from required paired profile")
    files = [gp, gv, gk, mp, mv, mm, inspection_path,
             directory / "generic/manifest.json", directory / "generic/component-manifest.json"]
    return {
        "schema": "s31-paired-record-v2-build-attestation-v1",
        "count": count,
        "source_sha256": expected["source_sha256"],
        "semantic_relation_sha256": expected["semantic_relation_sha256"],
        "public_record_abi_sha256": expected["public_record_abi_sha256"],
        "compiler_sha256": compiler,
        "generic_profile": cost["profile"],
        "generic_component_manifest_sha256": sha((directory / "generic/component-manifest.json").read_bytes()),
        "mixed_registry_manifest_sha256": report["registry_manifest_sha256"],
        "mixed_circuit_identity_sha256": report["circuit_identity_sha256"],
        "generic_live_pcs": generic_pcs,
        "mixed_live_pcs": mixed_pcs,
        "generic_interaction_pow_bits": cost["interaction_pow_bits"],
        "mixed_interaction_pow_bits": report["interaction_pow_bits"],
        "mixed_inspection_sha256": sha(report_bytes),
        "artifact_sha256": {str(path.relative_to(directory)): sha(path.read_bytes()) for path in files},
    }


def require_package_identity(directory: Path, count: int, expected: dict, compiler: str) -> dict:
    path = directory / "package-attestation.json"
    saved = json.loads(path.read_bytes())
    actual = package_identity(directory, count, expected, compiler)
    if saved != actual:
        raise ValueError(f"N={count}: native package differs from build attestation")
    return actual


def build_case(directory: Path, count: int, cfg: dict, expected: dict,
               protocol: dict, split: str) -> list[dict]:
    materialize(directory, count, cfg, expected)
    source_path = directory / "source.s31.json"
    name = json.loads(source_path.read_bytes())["name"]
    check_disk_space(directory, protocol["minimum_available_disk_bytes_before_native_phase"])
    generic_start_ns = time.perf_counter_ns()
    s31.build(source_path, directory / "generic", "direct-gate")
    generic_end_ns = time.perf_counter_ns()
    mixed_command = [
        "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=2",
        "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
        f"-Ds31-name={name}", "-j1", "--prefix", str(directory / "mixed"),
    ]
    check_disk_space(directory, protocol["minimum_available_disk_bytes_before_native_phase"])
    mixed_start_ns = time.perf_counter_ns()
    subprocess.run(mixed_command, cwd=ROOT, check=True)
    mixed_end_ns = time.perf_counter_ns()
    mixed_manifest = mixed_bins(directory, name)[2]
    saved_json(directory / "mixed-inspection.json",
               json.loads(subprocess.check_output([str(mixed_manifest)], text=True)))
    attestation = package_identity(directory, count, expected, protocol["compiler_sha256"])
    saved_json(directory / "package-attestation.json", attestation)
    package_digest = sha((directory / "package-attestation.json").read_bytes())
    common = {
        "schema": BUILD_EVENT_SCHEMA, "split": split, "count": count,
        "source_sha256": expected["source_sha256"],
        "compiler_sha256": protocol["compiler_sha256"],
        "engine_gitlink_commit": protocol["engine_gitlink_commit"],
        "package_attestation_sha256": package_digest,
        "outcome": "success",
    }
    events = [
        {**common, "arm": "generic", "operation": {
            "api": "s31.build", "source": str(source_path),
            "output": str(directory / "generic"), "lowering": "direct-gate"},
         "start_monotonic_ns": generic_start_ns, "end_monotonic_ns": generic_end_ns},
        {**common, "arm": "mixed", "operation": {"argv": mixed_command,
                                                    "cwd": str(ROOT)},
         "start_monotonic_ns": mixed_start_ns, "end_monotonic_ns": mixed_end_ns},
    ]
    build_times = {
        "schema": "s31-paired-record-v2-build-times-v1",
        "generic_seconds": build_event_seconds(events[0], directory, split,
                                                count, "generic", expected, protocol),
        "mixed_seconds": build_event_seconds(events[1], directory, split,
                                              count, "mixed", expected, protocol),
    }
    durable_write(directory / "build-times.json", canonical(build_times))
    return events


def build_event_seconds(event: dict, directory: Path, split: str, count: int,
                        arm: str, expected: dict, protocol: dict) -> float:
    """Derive build duration only from a source/package-bound raw event."""
    source_path = directory / "source.s31.json"
    name = json.loads(source_path.read_bytes())["name"]
    mixed_command = [
        "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
        "-Doptimize=ReleaseFast", "-Ds31-version=2",
        "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
        f"-Ds31-name={name}", "-j1", "--prefix", str(directory / "mixed"),
    ]
    operation = ({"api": "s31.build", "source": str(source_path),
                  "output": str(directory / "generic"), "lowering": "direct-gate"}
                 if arm == "generic" else {"argv": mixed_command, "cwd": str(ROOT)})
    if (set(event) != {"schema", "split", "count", "arm", "source_sha256",
                       "compiler_sha256", "engine_gitlink_commit",
                       "package_attestation_sha256", "outcome", "operation",
                       "start_monotonic_ns", "end_monotonic_ns"} or
            event["schema"] != BUILD_EVENT_SCHEMA or event["split"] != split or
            event["count"] != count or event["arm"] != arm or
            event["source_sha256"] != expected["source_sha256"] or
            event["compiler_sha256"] != protocol["compiler_sha256"] or
            event["engine_gitlink_commit"] != protocol["engine_gitlink_commit"] or
            event["package_attestation_sha256"] !=
                sha((directory / "package-attestation.json").read_bytes()) or
            event["outcome"] != "success" or event["operation"] != operation or
            type(event["start_monotonic_ns"]) is not int or
            type(event["end_monotonic_ns"]) is not int or
            event["start_monotonic_ns"] < 0 or
            event["end_monotonic_ns"] <= event["start_monotonic_ns"]):
        raise ValueError(f"N={count}/{arm}: raw build event identity or clock changed")
    return (event["end_monotonic_ns"] - event["start_monotonic_ns"]) / 1e9


def replay_build_evidence(out: Path, split: str, entries: dict,
                          protocol: dict, protocol_sha256: str,
                          protocol_anchor_commit: str) -> dict:
    saved = json.loads((out / "build-root.json").read_bytes())
    actual = build_root(out, split, protocol_sha256,
                        protocol_anchor_commit, list(entries))
    if (out / "build-root.json").read_bytes() != canonical(saved) or saved != actual:
        raise ValueError("paired build root differs from raw build ledger or package artifacts")
    events, _ = read_ledger(out / "build-ledger.ndjson",
                            event_schema=BUILD_EVENT_SCHEMA)
    at = 0
    previous_end_ns = None
    derived_costs = {}
    for key, expected in entries.items():
        directory = out / f"n{key}"
        times = {"schema": "s31-paired-record-v2-build-times-v1"}
        for arm in ("generic", "mixed"):
            event = events[at]
            at += 1
            if previous_end_ns is not None and \
                    event["start_monotonic_ns"] < previous_end_ns:
                raise ValueError("raw build event order differs from frozen generic/mixed roster")
            seconds = build_event_seconds(event, directory, split, int(key),
                                          arm, expected, protocol)
            previous_end_ns = event["end_monotonic_ns"]
            times[f"{arm}_seconds"] = seconds
        if (directory / "build-times.json").read_bytes() != canonical(times):
            raise ValueError(f"N={key}: saved build times differ from raw monotonic build events")
        derived_costs[key] = times
    if at != len(events):
        raise ValueError("paired build ledger has extra or omitted arm events")
    return derived_costs


def changed_claim(original: bytes, leaf_index: int) -> bytes:
    value = json.loads(original)
    value["leaves"][leaf_index]["words"][0] = (value["leaves"][leaf_index]["words"][0] + 1) % P
    return canonical(value)


def altered_valid_assignment(original: bytes, count: int,
                             relation: dict) -> tuple[bytes, bytes]:
    """Change a public input and recompute a valid output independently."""
    assignment = json.loads(original)
    input_wire = relation["inputs"][0]["name"]
    output_wire = relation["public_outputs"][0]
    if (set(assignment["public_inputs"]) != {input_wire} or
            set(assignment["public_outputs"]) != {output_wire} or
            assignment["private_inputs"] != {}):
        raise ValueError("altered control requires the admitted public-only source")
    words = assignment["public_inputs"][input_wire][:]
    if len(words) != 4:
        raise ValueError("altered control requires four public input lanes")
    words[0] = (words[0] + 1) % P
    state = words[:]
    for call in range(count):
        for _ in range(16):
            state = [(value * value + 13 + call) % P for value in state]
    result = [(value + start) % P for value, start in zip(state, words)]
    assignment["public_inputs"][input_wire] = words
    assignment["public_outputs"][output_wire] = result
    if evaluate_relation(flat(relation), assignment) != assignment["public_outputs"]:
        raise ValueError("altered valid public assignment disagrees with independent relation oracle")
    typed = statement_from_assignment(relation, assignment)
    return canonical(assignment), typed


def rejected(command: list[str]) -> bool:
    return subprocess.run(command, cwd=ROOT, capture_output=True, check=False).returncode != 0


def paired_summary(corpus: dict, cfg: dict) -> dict:
    """Estimate assignment-paired ratios only after the native replay gate."""
    result = {}
    metrics = ("first_verified_wall_seconds", "prove_wall_seconds",
               "verify_wall_seconds", "proof_bytes", "prover_peak_rss_bytes")
    for key, rows in corpus["cases"].items():
        if len(rows) != cfg["assignments_per_call_count"]:
            raise ValueError("paired summary requires complete frozen case")
        estimates = {}
        for metric in metrics:
            pairs = [(row["generic"][metric], row["mixed"][metric]) for row in rows]
            if any(left is None or right is None for left, right in pairs):
                estimates[metric] = {"status": "unavailable"}
                continue
            if any(not math.isfinite(left) or not math.isfinite(right) or
                   left <= 0 or right <= 0 for left, right in pairs):
                raise ValueError("paired ratio inputs must be positive finite numbers")
            logs = [math.log(left / right) for left, right in pairs]
            center = statistics.median(logs)
            seed = int(sha(f"{cfg['bootstrap_seed']}:{key}:{metric}".encode()), 16)
            rng = random.Random(seed)
            sampled = sorted(statistics.median(rng.choices(logs, k=len(logs)))
                             for _ in range(cfg["bootstrap_resamples"]))
            def percentile(p: float) -> float:
                offset = p * (len(sampled) - 1)
                lo = int(offset)
                return sampled[lo] + (sampled[min(lo + 1, len(sampled) - 1)] -
                                      sampled[lo]) * (offset - lo)
            estimates[metric] = {
                "status": "estimated",
                "paired_observations": len(logs),
                "median_log_generic_over_mixed": center,
                "median_ratio_generic_over_mixed": math.exp(center),
                "bootstrap_95_ratio_interval": [math.exp(percentile(0.025)),
                                                math.exp(percentile(0.975))],
                "generic_median_absolute": statistics.median(left for left, _ in pairs),
                "mixed_median_absolute": statistics.median(right for _, right in pairs),
            }
        result[key] = estimates
    return {
        "schema": "s31-paired-record-v2-analysis-v1",
        "split": corpus["split"],
        "estimand": "fresh-process first native-verified proof; generic and mixed each have one external native verification; package build excluded",
        "workflow_note": "mixed prover evaluates the relation twice; ratios describe shipped workflows, not pure AIR arithmetic speed",
        "measurement_trust": "anchored raw evidence detects later mutation; pinned collector, monotonic clock, and OS RSS accounting remain trusted",
        "ratio_direction": "generic divided by mixed; above one favors mixed",
        "bootstrap": "assignment-paired percentile bootstrap of median log ratio, 10000 resamples",
        "automatic_lowering_selection_enabled": False,
        "per_call_count": result,
    }


def analysis_from_corpus(corpus: dict, cfg: dict, entries: dict,
                         build_costs: dict, out: Path,
                         phase_root_sha256: str, phase_anchor_commit: str) -> dict:
    analysis = paired_summary(corpus, cfg)
    analysis["phase_root_sha256"] = phase_root_sha256
    analysis["phase_anchor_commit"] = phase_anchor_commit
    analysis["build_cost_scope"] = (
        "observed warm-cache workflows: generic full s31.build package; "
        "mixed direct Zig install; not a symmetric or cold compiler benchmark"
    )
    analysis["build_costs"] = build_costs
    analysis["live_security_profiles"] = {}
    for key in entries:
        package = json.loads((out / f"n{key}/package-attestation.json").read_bytes())
        generic_pcs = package["generic_live_pcs"]
        mixed_pcs = package["mixed_live_pcs"]
        analysis["live_security_profiles"][key] = {
            "generic_pcs": generic_pcs,
            "mixed_pcs": mixed_pcs,
            "generic_interaction_pow_bits": package["generic_interaction_pow_bits"],
            "mixed_interaction_pow_bits": package["mixed_interaction_pow_bits"],
            "matching_fri_config": generic_pcs["fri_config"] == mixed_pcs["fri_config"],
            "matching_interaction_pow_bits": package["generic_interaction_pow_bits"] ==
                                             package["mixed_interaction_pow_bits"],
            "different_pcs_lifting_or_geometry": generic_pcs != mixed_pcs,
        }
    analysis["soundness_note"] = (
        "Matched visible FRI/PoW parameters do not prove equal soundness. "
        "Each AIR/component profile needs its own soundness analysis."
    )
    return analysis


def arm_commands(directory: Path, index: int, arm: str) -> tuple[list[str], list[str], Path | None]:
    source_path = directory / "source.s31.json"
    name = json.loads(source_path.read_bytes())["name"]
    assignment = directory / f"assignments/{index:02d}.json"
    typed = directory / f"statements/{index:02d}.json"
    target = directory / f"trials/{index:02d}/{arm}"
    proof = target / "proof.bin"
    if arm == "generic":
        prover, verifier, key = generic_bins(directory, name)
        prove_cmd = [str(prover), "prove-for-external-verification", str(assignment), str(proof)]
        verify_cmd = [str(verifier), str(proof), str(typed), str(key)]
        output_statement = None
    elif arm == "mixed":
        prover, verifier, _ = mixed_bins(directory, name)
        output_statement = target / "statement.json"
        prove_cmd = [str(prover), str(assignment), str(proof), str(output_statement), str(typed)]
        verify_cmd = [str(verifier), str(proof), str(typed)]
    else:
        raise ValueError("unknown paired arm")
    return prove_cmd, verify_cmd, output_statement


def arm_trial(directory: Path, split: str, count: int, index: int, order: str,
              arm: str, expected: dict) -> dict:
    target = directory / f"trials/{index:02d}/{arm}"
    target.mkdir(parents=True, exist_ok=False)
    prove_cmd, verify_cmd, output_statement = arm_commands(directory, index, arm)
    typed = directory / f"statements/{index:02d}.json"
    proof = target / "proof.bin"
    prove = observed_invoke(prove_cmd, target, "prover")
    generic_native_total = None
    if arm == "generic":
        log = (target / "prover.log").read_text()
        match = re.search(r"total before external verification=([\d.]+)s", log)
        if match is None or "total through verification=" in log:
            raise ValueError("generic timed prover did not expose its unchecked phase boundary")
        generic_native_total = float(match.group(1))
        if not 0 <= generic_native_total <= \
                (prove["end_monotonic_ns"] - prove["start_monotonic_ns"]) / 1e9 + 0.003:
            raise ValueError("generic native phase total exceeds measured prover process wall")
    # No trial exists unless this source-embedded native verifier accepts the
    # saved bytes against the exact independently generated typed statement.
    verify = observed_invoke(verify_cmd, target, "verifier")
    fsync_existing(proof)
    if output_statement is not None:
        fsync_existing(output_statement)
    if output_statement is not None and output_statement.read_bytes() != typed.read_bytes():
        raise ValueError("mixed prover emitted a different typed public statement")
    changed_input = target / "changed-input.json"
    changed_result = target / "changed-result.json"
    durable_write(changed_input, changed_claim(typed.read_bytes(), 0))
    durable_write(changed_result, changed_claim(typed.read_bytes(), 1))
    for altered in (changed_input, changed_result):
        changed = verify_cmd[:]
        changed[2] = str(altered)
        if not rejected(changed):
            raise ValueError(f"{arm}: native verifier accepted changed public claim")
    return {
        "schema": EVENT_SCHEMA,
        "split": split,
        "count": count,
        "index": index,
        "order": order,
        "arm": arm,
        "timing_boundary": "unchecked-prover-then-one-external-native-verifier-v1",
        "source_sha256": expected["source_sha256"],
        "assignment_sha256": expected["assignment_sha256"][index],
        "statement_sha256": expected["statement_sha256"][index],
        "package_attestation_sha256": sha((directory / "package-attestation.json").read_bytes()),
        "prover_binary_sha256": sha(Path(prove_cmd[0]).read_bytes()),
        "verifier_binary_sha256": sha(Path(verify_cmd[0]).read_bytes()),
        "verifier_key_sha256": sha(Path(verify_cmd[3]).read_bytes()) if arm == "generic" else None,
        "proof_sha256": sha(proof.read_bytes()),
        "proof_bytes": proof.stat().st_size,
        "mixed_output_statement_sha256": sha(output_statement.read_bytes()) if output_statement else None,
        "changed_input_sha256": sha(changed_input.read_bytes()),
        "changed_result_sha256": sha(changed_result.read_bytes()),
        "prover": prove,
        "verifier": verify,
    }


def event_record(event: dict, directory: Path, split: str, count: int,
                 index: int, order: str, arm: str, expected: dict) -> dict:
    """Reconstruct every reported metric and identity from raw anchored bytes."""
    prove_cmd, verify_cmd, output_statement = arm_commands(directory, index, arm)
    target = directory / f"trials/{index:02d}/{arm}"
    typed = directory / f"statements/{index:02d}.json"
    proof = target / "proof.bin"
    if (set(event) != {"schema", "split", "count", "index", "order", "arm",
                       "timing_boundary", "source_sha256", "assignment_sha256",
                       "statement_sha256", "package_attestation_sha256",
                       "prover_binary_sha256", "verifier_binary_sha256",
                       "verifier_key_sha256", "proof_sha256", "proof_bytes",
                       "mixed_output_statement_sha256", "changed_input_sha256",
                       "changed_result_sha256", "prover", "verifier"} or
            event["schema"] != EVENT_SCHEMA or event["split"] != split or
            event["count"] != count or event["index"] != index or
            event["order"] != order or event["arm"] != arm or
            event["timing_boundary"] != "unchecked-prover-then-one-external-native-verifier-v1" or
            event["source_sha256"] != expected["source_sha256"] or
            event["assignment_sha256"] != expected["assignment_sha256"][index] or
            event["statement_sha256"] != expected["statement_sha256"][index] or
            event["package_attestation_sha256"] != sha((directory / "package-attestation.json").read_bytes()) or
            event["prover_binary_sha256"] != sha(Path(prove_cmd[0]).read_bytes()) or
            event["verifier_binary_sha256"] != sha(Path(verify_cmd[0]).read_bytes()) or
            event["verifier_key_sha256"] != (sha(Path(verify_cmd[3]).read_bytes()) if arm == "generic" else None) or
            event["proof_sha256"] != sha(proof.read_bytes()) or
            type(event["proof_bytes"]) is not int or event["proof_bytes"] <= 0 or
            event["proof_bytes"] != proof.stat().st_size or
            event["mixed_output_statement_sha256"] !=
                (sha(output_statement.read_bytes()) if output_statement else None) or
            (output_statement is not None and output_statement.read_bytes() != typed.read_bytes())):
        raise ValueError(f"N={count}/{index}/{arm}: raw arm source, claim, artifact, or phase identity changed")
    changed_input = target / "changed-input.json"
    changed_result = target / "changed-result.json"
    if (changed_input.read_bytes() != changed_claim(typed.read_bytes(), 0) or
            changed_result.read_bytes() != changed_claim(typed.read_bytes(), 1) or
            event["changed_input_sha256"] != sha(changed_input.read_bytes()) or
            event["changed_result_sha256"] != sha(changed_result.read_bytes())):
        raise ValueError("raw changed-claim control differs from typed public statement")
    prove_wall, prove_rss, prover_log = replay_process(event["prover"], target,
                                                        "prover", prove_cmd)
    verify_wall, verify_rss, _ = replay_process(event["verifier"], target,
                                                "verifier", verify_cmd)
    if event["prover"]["end_monotonic_ns"] > event["verifier"]["start_monotonic_ns"]:
        raise ValueError("external native verifier began before prover process ended")
    native_total = None
    stages = None
    if arm == "generic":
        match = re.search(r"total before external verification=([\d.]+)s", prover_log)
        if match is None or "total through verification=" in prover_log:
            raise ValueError("generic proof lacks unchecked phase marker")
        native_total = float(match.group(1))
        if not 0 <= native_total <= prove_wall + 0.003:
            raise ValueError("generic native total exceeds measured process wall")
        stages = s31.prover_stages(prover_log)
        if stages is None:
            raise ValueError("generic native stage timers are absent")
    return {
        "arm": arm,
        "source_sha256": event["source_sha256"],
        "assignment_sha256": event["assignment_sha256"],
        "statement_sha256": event["statement_sha256"],
        "raw_event_sha256": sha(canonical(event)),
        "proof_sha256": event["proof_sha256"],
        "proof_bytes": proof.stat().st_size,
        "prover_log_sha256": event["prover"]["log_sha256"],
        "verifier_log_sha256": event["verifier"]["log_sha256"],
        "native_prover_stages": stages,
        "generic_native_total_before_external_verification_seconds": native_total,
        "prove_wall_seconds": prove_wall,
        "verify_wall_seconds": verify_wall,
        "first_verified_wall_seconds": prove_wall + verify_wall,
        "prover_peak_rss_bytes": prove_rss,
        "prover_peak_rss_method": event["prover"]["rss_method"],
        "verifier_peak_rss_bytes": verify_rss,
        "verifier_peak_rss_method": event["verifier"]["rss_method"],
        "external_native_verifier_accepted": True,
        "changed_public_input_rejected": True,
        "changed_public_result_rejected": True,
    }


def checked_report(out: Path, split: str, protocol: dict, cfg: dict,
                   protocol_sha256: str, protocol_anchor_commit: str,
                   phase_root_sha256: str, phase_anchor_commit: str,
                   report_anchor_commit: str) -> dict:
    entries = protocol["inventory"][split]
    events = check_phase_anchor(out, split, protocol_sha256, protocol_anchor_commit,
                                2 * sum(len(item["order"]) for item in entries.values()),
                                list(entries), phase_root_sha256, phase_anchor_commit)
    audit, analysis = check_report_anchor(out, split, protocol_sha256,
                                          phase_root_sha256, phase_anchor_commit,
                                          report_anchor_commit)
    for field in ("raw_ledger_replayed_before_summary", "all_saved_proofs_native_replayed",
                  "all_changed_public_claims_rejected",
                  "same_geometry_alternate_source_controls_passed",
                  "proof_header_manifest_digest_control_rejected",
                  "altered_valid_public_assignment_controls_passed"):
        if audit.get(field) is not True:
            raise ValueError(f"{split}: anchored audit control did not pass: {field}")
    first = out / f"n{next(iter(entries))}"
    first_name = json.loads((first / "source.s31.json").read_bytes())["name"]
    alternate_name = f"{first_name}_same_geometry_alternate"
    controls = out / "audit-controls"
    control_files = {
        "alternate_source_sha256": controls / "same-count-alternate.s31.json",
        "alternate_generic_verifier_sha256": controls / "alternate-generic/bin" /
            f"s31-{alternate_name}-native-verifier",
        "alternate_mixed_verifier_sha256": controls / "alternate-mixed/bin" /
            f"s31-{alternate_name}-mixed-general-native-verifier",
        "altered_assignment_sha256": controls / "altered-valid-assignment.json",
        "altered_statement_sha256": controls / "altered-valid-statement.json",
        "altered_generic_proof_sha256": controls / "altered-generic.proof",
        "altered_mixed_proof_sha256": controls / "altered-mixed.proof",
        "modified_manifest_header_proof_sha256": controls / "wrong-manifest-header.proof",
    }
    for field, path in control_files.items():
        if audit.get(field) != sha(path.read_bytes()):
            raise ValueError(f"{split}: anchored audit control artifact changed: {field}")
    corpus = json.loads((out / "corpus.json").read_bytes())
    replay_corpus(out, split, entries, protocol_sha256, protocol_anchor_commit,
                  events, corpus, native=False)
    for key, expected in entries.items():
        directory = out / f"n{key}"
        for index in range(cfg["assignments_per_call_count"]):
            require_static_case(directory, int(key), index, cfg, expected)
        require_package_identity(directory, int(key), expected, protocol["compiler_sha256"])
    build_costs = replay_build_evidence(out, split, entries, protocol,
                                        protocol_sha256, protocol_anchor_commit)
    expected_analysis = analysis_from_corpus(corpus, cfg, entries, build_costs,
                                             out, phase_root_sha256, phase_anchor_commit)
    if analysis != expected_analysis:
        raise ValueError(f"{split}: anchored analysis differs from deterministic replay")
    return {"split": split, "phase_root_sha256": phase_root_sha256,
            "phase_anchor_commit": phase_anchor_commit,
            "report_anchor_commit": report_anchor_commit,
            "audit_sha256": sha((out / "audit.json").read_bytes()),
            "analysis_sha256": sha((out / "analysis.json").read_bytes())}


def replay_corpus(out: Path, split: str, entries: dict, protocol_sha256: str,
                  protocol_anchor_commit: str, events: list[dict], corpus: dict,
                  *, native: bool) -> dict:
    """Reconstruct the sealed corpus from raw events; optionally rerun verifiers."""
    if (corpus.get("schema") != "s31-paired-record-v2-corpus-v1" or
            corpus.get("split") != split or
            corpus.get("protocol_sha256") != protocol_sha256 or
            corpus.get("anchor_commit") != protocol_anchor_commit or
            corpus.get("cases", {}).keys() != entries.keys()):
        raise ValueError("paired corpus differs from frozen roster")
    derived = {"schema": "s31-paired-record-v2-corpus-v1", "split": split,
               "protocol_sha256": protocol_sha256,
               "anchor_commit": protocol_anchor_commit, "cases": {}}
    event_at = 0
    previous_arm_end_ns = None
    for key, expected in entries.items():
        directory = out / f"n{key}"
        name = json.loads((directory / "source.s31.json").read_bytes())["name"]
        derived_rows = []
        for index, row in enumerate(corpus["cases"][key]):
            if row.get("index") != index or row.get("order") != expected["order"][index]:
                raise ValueError("paired trial order differs from freeze")
            typed = directory / f"statements/{index:02d}.json"
            order = expected["order"][index]
            arms = ("generic", "mixed") if order == "generic-first" else ("mixed", "generic")
            reconstructed = {"index": index, "order": order}
            for arm in arms:
                event = events[event_at]
                event_at += 1
                if previous_arm_end_ns is not None and \
                        event["prover"]["start_monotonic_ns"] < previous_arm_end_ns:
                    raise ValueError("raw arm timing order differs from sequential frozen trial order")
                reconstructed[arm] = event_record(event, directory, split,
                                                   int(key), index, order, arm, expected)
                previous_arm_end_ns = event["verifier"]["end_monotonic_ns"]
                if native:
                    proof = directory / f"trials/{index:02d}/{arm}/proof.bin"
                    verifier = (generic_bins(directory, name)[1] if arm == "generic"
                                else mixed_bins(directory, name)[1])
                    command = [str(verifier), str(proof), str(typed)]
                    if arm == "generic":
                        command.append(str(generic_bins(directory, name)[2]))
                    subprocess.run(command, cwd=ROOT, check=True, capture_output=True)
                    for leaf in (0, 1):
                        changed = directory / f"trials/{index:02d}/{arm}/changed-{'input' if leaf == 0 else 'result'}.json"
                        if changed.read_bytes() != changed_claim(typed.read_bytes(), leaf):
                            raise ValueError("changed-claim control bytes differ from expectation")
                        altered = command[:]
                        altered[2] = str(changed)
                        if not rejected(altered):
                            raise ValueError("saved verifier accepted a changed typed claim")
            derived_rows.append(reconstructed)
        derived["cases"][key] = derived_rows
    if event_at != len(events) or corpus != derived:
        raise ValueError("corpus timing, RSS, bytes, arm, source, or order differs from raw phase ledger")
    return derived


def heldout_train_admission(args: argparse.Namespace, out: Path,
                            protocol: dict, cfg: dict) -> dict:
    if not all((args.train_out, args.expected_train_phase_root_sha256,
                args.train_phase_anchor_commit, args.train_report_anchor_commit)):
        raise ValueError("held-out phase requires anchored and reviewed train phase/report")
    train_out = args.train_out.resolve()
    if train_out == out or not train_out.is_dir():
        raise ValueError("held-out phase requires a distinct existing train evidence path")
    return checked_report(train_out, "train", protocol, cfg,
                          args.expected_protocol_sha256, args.anchor_commit,
                          args.expected_train_phase_root_sha256,
                          args.train_phase_anchor_commit,
                          args.train_report_anchor_commit)


def run(args: argparse.Namespace) -> None:
    protocol = check(args.expected_protocol_sha256, args.anchor_commit)
    cfg = design()
    split = args.split
    entries = protocol["inventory"][split]
    out = args.out.resolve()
    train_admission = heldout_train_admission(args, out, protocol, cfg) if split == "heldout" else None
    if args.phase == "report-check":
        if not all((args.expected_phase_root_sha256, args.phase_anchor_commit,
                    args.report_anchor_commit)):
            raise ValueError("report-check requires full phase and report anchors")
        print(json.dumps(checked_report(out, split, protocol, cfg,
                                        args.expected_protocol_sha256, args.anchor_commit,
                                        args.expected_phase_root_sha256,
                                        args.phase_anchor_commit, args.report_anchor_commit),
                         sort_keys=True))
        return
    out.parent.mkdir(parents=True, exist_ok=True)
    check_disk_space(out, protocol["minimum_available_disk_bytes_before_native_phase"])
    if args.phase == "build":
        out.mkdir(parents=True, exist_ok=False)
        if train_admission is not None:
            durable_write(out / "train-admission.json", canonical(train_admission))
        build_ledger = out / "build-ledger.ndjson"
        previous = GENESIS
        sequence = 0
        for key, expected in entries.items():
            check_disk_space(out, protocol["minimum_available_disk_bytes_before_native_phase"])
            events = build_case(out / f"n{key}", int(key), cfg, expected,
                                protocol, split)
            for event in events:
                previous = append_event(build_ledger, event, sequence, previous,
                                        event_schema=BUILD_EVENT_SCHEMA)
                sequence += 1
        durable_write(out / "build-root.json", canonical(build_root(
            out, split, args.expected_protocol_sha256,
            args.anchor_commit, list(entries))))
        replay_build_evidence(out, split, entries, protocol,
                              args.expected_protocol_sha256, args.anchor_commit)
        return
    if not out.is_dir():
        raise ValueError("paired build evidence is absent")
    if train_admission is not None and (out / "train-admission.json").read_bytes() != canonical(train_admission):
        raise ValueError("held-out train admission changed after package build")
    for key, expected in entries.items():
        directory = out / f"n{key}"
        count = int(key)
        for index in range(cfg["assignments_per_call_count"]):
            require_static_case(directory, count, index, cfg, expected)
        require_package_identity(directory, count, expected, protocol["compiler_sha256"])
    build_costs = replay_build_evidence(out, split, entries, protocol,
                                        args.expected_protocol_sha256, args.anchor_commit)
    if args.phase == "prove":
        if any((out / name).exists() for name in (
                "phase-ledger.ndjson", "phase-root.json", "corpus.partial.json", "corpus.json")):
            raise ValueError("paired proof evidence already exists; do not resume a partial timed phase")
        corpus = {"schema": "s31-paired-record-v2-corpus-v1", "split": split,
                  "protocol_sha256": args.expected_protocol_sha256,
                  "anchor_commit": args.anchor_commit, "cases": {}}
        ledger = out / "phase-ledger.ndjson"
        previous = GENESIS
        sequence = 0
        for key, expected in entries.items():
            directory = out / f"n{key}"
            (directory / "trials").mkdir(exist_ok=False)
            results = []
            for index, order in enumerate(expected["order"]):
                check_disk_space(out, protocol["minimum_available_disk_bytes_before_native_phase"])
                first, second = (("generic", "mixed") if order == "generic-first"
                                 else ("mixed", "generic"))
                arms = {}
                for arm in (first, second):
                    check_disk_space(out, protocol["minimum_available_disk_bytes_before_native_phase"])
                    event = arm_trial(directory, split, int(key), index, order, arm, expected)
                    arms[arm] = event_record(event, directory, split, int(key),
                                             index, order, arm, expected)
                    previous = append_event(ledger, event, sequence, previous)
                    sequence += 1
                results.append({"index": index, "order": order, **arms})
            corpus["cases"][key] = results
            saved_json(out / "corpus.partial.json", corpus)
        durable_write(out / "corpus.json", canonical(corpus))
        (out / "corpus.partial.json").unlink()
        root = phase_root(out, split, args.expected_protocol_sha256,
                          args.anchor_commit, 2 * sum(len(item["order"]) for item in entries.values()),
                          list(entries))
        durable_write(out / "phase-root.json", canonical(root))
        print(sha((out / "phase-root.json").read_bytes()))
        return
    if args.phase == "audit":
        if (out / "corpus.partial.json").exists() or (out / "audit.json").exists() or \
                (out / "analysis.json").exists():
            raise ValueError("partial proof phase or prior audit makes this audit inadmissible")
        events = check_phase_anchor(
            out, split, args.expected_protocol_sha256, args.anchor_commit,
            2 * sum(len(item["order"]) for item in entries.values()),
            list(entries), args.expected_phase_root_sha256, args.phase_anchor_commit)
        corpus = json.loads((out / "corpus.json").read_bytes())
        check_disk_space(out, protocol["minimum_available_disk_bytes_before_native_phase"])
        derived = replay_corpus(out, split, entries, args.expected_protocol_sha256,
                                args.anchor_commit, events, corpus, native=True)
        # Independent, untimed controls exercise source identity at identical
        # geometry, proof-header binding, and a *valid* altered public claim.
        first_key = next(iter(entries))
        first = out / f"n{first_key}"
        first_source_bytes = (first / "source.s31.json").read_bytes()
        first_source = parse_source_json(first_source_bytes)
        first_name = first_source["name"]
        controls = out / "audit-controls"
        check_disk_space(out, protocol["minimum_available_disk_bytes_before_native_phase"])
        controls.mkdir(exist_ok=False)
        first_statement = first / "statements/00.json"
        generic_proof = first / "trials/00/generic/proof.bin"
        mixed_proof = first / "trials/00/mixed/proof.bin"
        alternate_name = f"{first_name}_same_geometry_alternate"
        alternate_source = {**first_source, "name": alternate_name}
        if ({key: value for key, value in alternate_source.items() if key != "name"} !=
                {key: value for key, value in first_source.items() if key != "name"}):
            raise ValueError("alternate source changed more than the top-level name")
        alternate_source_path = controls / "same-count-alternate.s31.json"
        durable_write(alternate_source_path, canonical(alternate_source))
        alternate_generic = s31.build(alternate_source_path,
                                      controls / "alternate-generic", "direct-gate")
        alternate_generic_manifest = s31.verify_package(alternate_generic)
        if (alternate_generic_manifest["program_sha256"] !=
                sha(alternate_source_path.read_bytes()) or
                alternate_generic_manifest["lowering"] != "direct-gate"):
            raise ValueError("alternate generic verifier is not bound to altered source")
        alternate_mixed = controls / "alternate-mixed"
        check_disk_space(out, protocol["minimum_available_disk_bytes_before_native_phase"])
        subprocess.run([
            "zig", "build", "--build-file", str(S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=2",
            "-Ds31-lowering=direct-mixed-general",
            f"-Ds31-source={alternate_source_path}",
            f"-Ds31-name={alternate_name}", "-j1", "--prefix", str(alternate_mixed),
        ], cwd=ROOT, check=True)
        alternate_manifest_bin = (alternate_mixed / "bin" /
                                  f"s31-{alternate_name}-mixed-general-manifest")
        alternate_mixed_report = json.loads(subprocess.check_output(
            [str(alternate_manifest_bin)], text=True))
        original_mixed_report = json.loads((first / "mixed-inspection.json").read_bytes())
        original_generic_report = json.loads((first / "generic/cost-report.json").read_bytes())
        alternate_generic_report = json.loads(
            (alternate_generic / "cost-report.json").read_bytes())
        generic_geometry = ("raw", "padded", "trace_log_size", "pcs")
        mixed_geometry = ("call_count", "slot_count", "tree_columns",
                          "max_column_log_size", "composition_log_size",
                          "composition_split", "pcs")
        if (any(original_generic_report[key] != alternate_generic_report[key]
                for key in generic_geometry) or
                any(original_mixed_report[key] != alternate_mixed_report[key]
                    for key in mixed_geometry) or
                alternate_generic_report["public_abi_sha256"] !=
                    original_generic_report["public_abi_sha256"] or
                alternate_mixed_report["source_sha256"] !=
                    sha(alternate_source_path.read_bytes()) or
                alternate_mixed_report["registry_manifest_sha256"] !=
                    registry_digest(alternate_mixed_report)):
            raise ValueError("same-count alternate source changed native geometry or ABI")
        alternate_generic_verifier = (alternate_generic / "bin" /
                                      f"s31-{alternate_name}-native-verifier")
        alternate_generic_key = alternate_generic / "verification-key.json"
        alternate_mixed_verifier = (alternate_mixed / "bin" /
                                    f"s31-{alternate_name}-mixed-general-native-verifier")
        if not rejected([str(alternate_generic_verifier), str(generic_proof),
                         str(first_statement), str(alternate_generic_key)]):
            raise ValueError("same-geometry alternate generic verifier accepted old-source proof")
        if not rejected([str(alternate_mixed_verifier), str(mixed_proof),
                         str(first_statement)]):
            raise ValueError("same-geometry alternate mixed verifier accepted old-source proof")
        first_assignment = first / "assignments/00.json"
        alternate_generic_proof = controls / "alternate-generic.proof"
        alternate_generic_prover = (alternate_generic / "bin" /
                                    f"s31-{alternate_name}-prover")
        subprocess.run([str(alternate_generic_prover),
                        "prove-for-external-verification", str(first_assignment),
                        str(alternate_generic_proof)], cwd=ROOT, check=True,
                       capture_output=True)
        subprocess.run([str(alternate_generic_verifier), str(alternate_generic_proof),
                        str(first_statement), str(alternate_generic_key)],
                       cwd=ROOT, check=True, capture_output=True)
        alternate_mixed_prover = (alternate_mixed / "bin" /
                                  f"s31-{alternate_name}-mixed-general-prover")
        alternate_mixed_proof = controls / "alternate-mixed.proof"
        alternate_mixed_statement = controls / "alternate-mixed.statement.json"
        subprocess.run([str(alternate_mixed_prover), str(first_assignment),
                        str(alternate_mixed_proof), str(alternate_mixed_statement),
                        str(first_statement)], cwd=ROOT, check=True, capture_output=True)
        if alternate_mixed_statement.read_bytes() != first_statement.read_bytes():
            raise ValueError("alternate mixed prover changed the same typed claim")
        subprocess.run([str(alternate_mixed_verifier), str(alternate_mixed_proof),
                        str(first_statement)], cwd=ROOT, check=True, capture_output=True)
        corrupted = bytearray(mixed_proof.read_bytes())
        if not corrupted.startswith(b"S31MIX07") or len(corrupted) < 76:
            raise ValueError("mixed proof envelope lacks expected component identity")
        corrupted[44] ^= 1  # first byte of bound registry manifest digest
        wrong_manifest_header = controls / "wrong-manifest-header.proof"
        durable_write(wrong_manifest_header, corrupted)
        first_mixed_verifier = mixed_bins(first, first_name)[1]
        if not rejected([str(first_mixed_verifier), str(wrong_manifest_header),
                         str(first_statement)]):
            raise ValueError("mixed verifier accepted altered proof-header manifest digest")
        altered_assignment_bytes, altered_statement_bytes = altered_valid_assignment(
            first_assignment.read_bytes(), int(first_key), first_source)
        if altered_statement_bytes == first_statement.read_bytes():
            raise ValueError("altered valid input unexpectedly has original typed claim")
        altered_assignment = controls / "altered-valid-assignment.json"
        altered_statement = controls / "altered-valid-statement.json"
        durable_write(altered_assignment, altered_assignment_bytes)
        durable_write(altered_statement, altered_statement_bytes)
        generic_prover = generic_bins(first, first_name)[0]
        check_disk_space(out, protocol["minimum_available_disk_bytes_before_native_phase"])
        altered_generic_proof = controls / "altered-generic.proof"
        subprocess.run([
            str(generic_prover), "prove-for-external-verification",
            str(altered_assignment), str(altered_generic_proof),
        ], cwd=ROOT, capture_output=True, check=True)
        _, first_generic_verifier, first_generic_key = generic_bins(first, first_name)
        subprocess.run([str(first_generic_verifier), str(altered_generic_proof),
                        str(altered_statement), str(first_generic_key)],
                       cwd=ROOT, capture_output=True, check=True)
        if not rejected([str(first_generic_verifier), str(altered_generic_proof),
                         str(first_statement), str(first_generic_key)]):
            raise ValueError("generic native verifier accepted original claim for altered valid proof")
        mixed_prover = mixed_bins(first, first_name)[0]
        check_disk_space(out, protocol["minimum_available_disk_bytes_before_native_phase"])
        altered_mixed_proof = controls / "altered-mixed.proof"
        altered_mixed_output = controls / "altered-mixed.statement.json"
        subprocess.run([str(mixed_prover), str(altered_assignment),
                        str(altered_mixed_proof), str(altered_mixed_output),
                        str(altered_statement)], cwd=ROOT, capture_output=True, check=True)
        if altered_mixed_output.read_bytes() != altered_statement_bytes:
            raise ValueError("mixed prover did not emit the valid altered typed claim")
        subprocess.run([str(first_mixed_verifier), str(altered_mixed_proof),
                        str(altered_statement)], cwd=ROOT, capture_output=True, check=True)
        if not rejected([str(first_mixed_verifier), str(altered_mixed_proof),
                         str(first_statement)]):
            raise ValueError("mixed verifier accepted original claim for altered valid proof")
        mixed_old_claim = subprocess.run([
            str(mixed_prover), str(altered_assignment),
            str(controls / "altered-old-claim.proof"),
            str(controls / "altered-old-claim.statement.json"),
            str(first_statement),
        ], cwd=ROOT, capture_output=True, check=False)
        if mixed_old_claim.returncode == 0 or \
                b"InvalidMixedPublicStatement" not in mixed_old_claim.stderr:
            raise ValueError("mixed prover failed to reject old typed claim at public-statement check")
        saved_json(out / "audit.json", {"schema": "s31-paired-record-v2-audit-v1",
                                            "protocol_sha256": args.expected_protocol_sha256,
                                            "phase_root_sha256": args.expected_phase_root_sha256,
                                            "phase_anchor_commit": args.phase_anchor_commit,
                                            "corpus_sha256": sha((out / "corpus.json").read_bytes()),
                                            "raw_ledger_replayed_before_summary": True,
                                            "all_saved_proofs_native_replayed": True,
                                            "all_changed_public_claims_rejected": True,
                                            "same_geometry_alternate_source_controls_passed": True,
                                            "proof_header_manifest_digest_control_rejected": True,
                                            "altered_valid_public_assignment_controls_passed": True,
                                            "alternate_source_sha256": sha(alternate_source_path.read_bytes()),
                                            "alternate_generic_verifier_sha256": sha(alternate_generic_verifier.read_bytes()),
                                            "alternate_mixed_verifier_sha256": sha(alternate_mixed_verifier.read_bytes()),
                                            "altered_assignment_sha256": sha(altered_assignment_bytes),
                                            "altered_statement_sha256": sha(altered_statement_bytes),
                                            "altered_generic_proof_sha256": sha(altered_generic_proof.read_bytes()),
                                            "altered_mixed_proof_sha256": sha(altered_mixed_proof.read_bytes()),
                                            "modified_manifest_header_proof_sha256": sha(wrong_manifest_header.read_bytes())})
        saved_json(out / "analysis.json", analysis_from_corpus(
            derived, cfg, entries, build_costs, out,
            args.expected_phase_root_sha256, args.phase_anchor_commit))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--split", choices=("train", "heldout"), required=True)
    parser.add_argument("--phase", choices=("build", "prove", "audit", "report-check"), required=True)
    parser.add_argument("--expected-protocol-sha256", required=True)
    parser.add_argument("--anchor-commit", required=True)
    parser.add_argument("--expected-phase-root-sha256",
                        help="full externally recorded phase-root SHA-256; required by audit")
    parser.add_argument("--phase-anchor-commit",
                        help="committed split-specific UTC phase anchor; required by audit")
    parser.add_argument("--report-anchor-commit",
                        help="committed split-specific report anchor; required by report-check")
    parser.add_argument("--train-out", type=Path,
                        help="sealed train evidence path; required by every held-out phase")
    parser.add_argument("--expected-train-phase-root-sha256",
                        help="externally recorded train phase root; required by every held-out phase")
    parser.add_argument("--train-phase-anchor-commit",
                        help="committed train phase anchor; required by every held-out phase")
    parser.add_argument("--train-report-anchor-commit",
                        help="externally recorded train report anchor; required by every held-out phase")
    parser.add_argument("--out", type=Path, required=True)
    run(parser.parse_args())
