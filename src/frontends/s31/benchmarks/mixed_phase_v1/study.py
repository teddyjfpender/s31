#!/usr/bin/env python3
"""Pinned paired diagnostic of optional mixed native phase timing.

This is an instrumentation and accounting check, not a cost-model fit.
Prepare and commit the protocol before `run` starts its first native build.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import statistics
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
ROOT = S31.parents[2]
LANGUAGE = ROOT / "design/s31/measurements/language"
PROTOCOL = LANGUAGE / "mixed-phase-v1-protocol.json"
RESULT = LANGUAGE / "mixed-phase-v1-result.json"
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks/mixed_stage_cost_transfer_v1"))
from abi.binding_v2 import decode_public_statement, statement_from_assignment  # noqa: E402
from package.context import compiler_fingerprint  # noqa: E402
from cohort import design, output_words, source  # noqa: E402

COUNTS = (2, 6)
ASSIGNMENTS = 30
SEED = 202610119301
P = (1 << 31) - 1
TOOL_PATHS = (
    "src/frontends/s31/benchmarks/mixed_phase_v1/study.py",
    "src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/cohort.py",
    "src/frontends/s31/benchmarks/paired_record_v2/design.py",
    "src/frontends/s31/python/oracle.py",
    "src/frontends/s31/python/abi/binding_v2.py",
    "src/frontends/s31/python/package/context.py",
    "src/frontends/s31/runtime/mixed_boundary/general_package.zig",
    "src/frontends/s31/runtime/mixed_boundary/general_prover_main.zig",
    "src/frontends/s31/build.zig",
)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n").encode()


def unique(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key}")
        result[key] = value
    return result


def parse(raw: bytes) -> dict:
    value = json.loads(raw, object_pairs_hook=unique)
    if type(value) is not dict:
        raise ValueError("JSON object required")
    return value


def git(*args: str) -> bytes:
    return subprocess.check_output(("git", "-C", str(ROOT), *args))


def case(count: int, index: int) -> tuple[bytes, bytes, bytes]:
    if count not in COUNTS or not 0 <= index < ASSIGNMENTS:
        raise ValueError("case outside pinned N2/N6 roster")
    raw_source = source("control", count, design())
    relation = parse(raw_source)
    seed = SEED + count * 100_000 + index * 37
    words = [(seed * (lane + 17) + lane * lane + 11) % P for lane in range(4)]
    output = output_words("control", count, words)
    assignment = {"public_inputs": {relation["inputs"][0]["name"]: words},
                  "private_inputs": {},
                  "public_outputs": {relation["public_outputs"][0]: output}}
    statement = statement_from_assignment(relation, assignment)
    return raw_source, canonical(assignment), statement


def current_pins() -> dict:
    zig = shutil.which("zig")
    if zig is None:
        raise ValueError("zig executable unavailable")
    engine = git("rev-parse", "HEAD:deps/stwo-zig").decode().strip()
    if git("-C", str(ROOT / "deps/stwo-zig"), "rev-parse", "HEAD").decode().strip() != engine:
        raise ValueError("engine checkout differs from gitlink")
    return {"engine_gitlink_commit": engine,
            "compiler_sha256": compiler_fingerprint(),
            "zig_executable_sha256": sha(Path(zig).resolve().read_bytes()),
            "tool_sha256": {path: sha((ROOT / path).read_bytes()) for path in TOOL_PATHS},
            "source_template_sha256": sha((ROOT / design()["source_template"]).read_bytes())}


def prepare() -> dict:
    if PROTOCOL.exists():
        raise ValueError("mixed phase protocol already exists")
    if git("status", "--porcelain", "--", "deps/stwo-zig",
           "src/frontends/s31/runtime/mixed_boundary").strip():
        raise ValueError("runtime or engine gitlink must be committed before protocol freeze")
    roster = {}
    prior = json.loads((LANGUAGE / "mixed-stage-cost-transfer-v1-protocol.json").read_bytes())
    prior_hashes = {h for row in prior["inventory"].values()
                    for h in row["assignment_sha256"] + row["typed_statement_sha256"]}
    for count in COUNTS:
        cases = [case(count, index) for index in range(ASSIGNMENTS)]
        source_hashes = {sha(row[0]) for row in cases}
        assignments = [sha(row[1]) for row in cases]
        statements = [sha(row[2]) for row in cases]
        for source_bytes, _, statement in cases:
            changed_result(source_bytes, statement)
        if (len(source_hashes) != 1 or len(set(assignments)) != ASSIGNMENTS or
                len(set(statements)) != ASSIGNMENTS or
                (set(assignments) | set(statements)) & prior_hashes):
            raise ValueError("case roster is duplicate or reuses prior claims")
        roster[str(count)] = {"source_sha256": source_hashes.pop(),
                              "assignment_sha256": assignments,
                              "statement_sha256": statements}
    value = {"schema": "s31-mixed-phase-v1-protocol",
             "status": "frozen-before-native-build-local-diagnostic",
             "counts": list(COUNTS), "assignments_per_count": ASSIGNMENTS,
             "seed": SEED, "build_mode": "ReleaseFast",
             "order": "untimed-first-for-even-index-timed-first-for-odd-index",
             "worker_setting": "default-unset", "lowering": "direct-mixed-general",
             "timed_environment": "S31_MIXED_NATIVE_PHASES=1",
             "same_binary_per_pair": True, "proof_byte_identity_required": True,
             "native_verification_required": True,
             "changed_public_result_rejection_required": True,
             "speedup_claim_enabled": False, "predictive_model_enabled": False,
             "roster": roster, **current_pins()}
    PROTOCOL.write_bytes(canonical(value))
    return {"protocol_sha256": sha(PROTOCOL.read_bytes()),
            "cases": sum(len(row["assignment_sha256"]) for row in roster.values())}


def frozen() -> tuple[dict, str]:
    raw = PROTOCOL.read_bytes()
    value = parse(raw)
    if raw != canonical(value) or value.get("schema") != "s31-mixed-phase-v1-protocol" or \
            value.get("status") != "frozen-before-native-build-local-diagnostic" or \
            value.get("counts") != list(COUNTS) or \
            value.get("assignments_per_count") != ASSIGNMENTS or \
            value.get("seed") != SEED or value.get("same_binary_per_pair") is not True or \
            value.get("proof_byte_identity_required") is not True or \
            value.get("native_verification_required") is not True or \
            value.get("changed_public_result_rejection_required") is not True or \
            value.get("speedup_claim_enabled") is not False or \
            value.get("predictive_model_enabled") is not False:
        raise ValueError("mixed phase protocol shape changed")
    saved = git("show", f"HEAD:{PROTOCOL.relative_to(ROOT).as_posix()}")
    if saved != raw:
        raise ValueError("mixed phase protocol must be committed unchanged before native build")
    if {key: value[key] for key in ("engine_gitlink_commit", "compiler_sha256",
                                  "zig_executable_sha256", "tool_sha256",
                                  "source_template_sha256")} != current_pins():
        raise ValueError("compiler, engine, tools or template changed after protocol freeze")
    for count in COUNTS:
        cases = [case(count, index) for index in range(ASSIGNMENTS)]
        expected = value["roster"][str(count)]
        if (len({sha(row[0]) for row in cases}) != 1 or
                sha(cases[0][0]) != expected["source_sha256"] or
                [sha(row[1]) for row in cases] != expected["assignment_sha256"] or
                [sha(row[2]) for row in cases] != expected["statement_sha256"]):
            raise ValueError("generated claims differ from frozen protocol")
    return value, sha(raw)


def process(command: list[str], env: dict[str, str] | None = None) -> tuple[subprocess.CompletedProcess[bytes], int]:
    start = time.perf_counter_ns()
    result = subprocess.run(command, env=env, capture_output=True, check=False)
    return result, time.perf_counter_ns() - start


def tagged(stderr: bytes, tag: bytes) -> dict:
    lines = [line[len(tag) + 1:] for line in stderr.splitlines()
             if line.startswith(tag + b" ")]
    if len(lines) != 1:
        raise ValueError(f"expected one {tag.decode()} line, saw {len(lines)}")
    return parse(lines[0])


def statement_words(source_bytes: bytes, statement: bytes) -> list[int]:
    relation = parse(source_bytes)
    if relation.get("version") != 2:
        raise ValueError("expected version 2 source")
    binding = relation.pop("public_abi")
    relation["version"] = 1
    words = decode_public_statement(relation, binding, statement)
    if len(words) != 8:
        raise ValueError("expected eight canonical public words")
    return words


def changed_result(source_bytes: bytes, statement: bytes) -> bytes:
    value = parse(statement)
    words = value["leaves"][-1]["words"]
    if len(words) != 4 or type(words[0]) is not int or not 0 <= words[0] < P:
        raise ValueError("expected record ABI v2 result leaf")
    words[0] = (words[0] + 1) % P
    changed = canonical(value)
    original_words = statement_words(source_bytes, statement)
    changed_words = statement_words(source_bytes, changed)
    if (original_words[:4] != changed_words[:4] or
            original_words[4] == changed_words[4] or
            original_words[5:] != changed_words[5:]):
        raise ValueError("changed result is not an ABI-valid one-word mutation")
    return changed


def proof_layer_rejection(result: subprocess.CompletedProcess[bytes]) -> bool:
    return (result.returncode > 0 and result.stderr.strip() in
            (b"error: InvalidMixedInteractionNonce",
             b"error: InvalidMixedPublicStatement"))


def stage_check(stage: dict, wall_ns: int) -> int:
    parts = stage["stages_ns"]
    native = parts["native_prove_including_setup_ns"]
    keys = ("profile_rebuild_ns", "semantic_evaluation_ns", "topology_compile_ns",
            "witness_compile_ns", "native_prove_including_setup_ns",
            "envelope_and_serialization_ns")
    if (stage["schema"] != "s31-mixed-general-prover-stages-v1" or
            set(parts) != {*keys, "package_total_ns"} or
            any(type(parts[key]) is not int or parts[key] < 0 for key in parts) or
            parts["package_total_ns"] != sum(parts[key] for key in keys) or
            not 0 < native <= wall_ns):
        raise ValueError("invalid package stage accounting")
    return native


def phase_check(stage: dict, phase: dict, wall_ns: int) -> dict:
    native = stage_check(stage, wall_ns)
    if phase["schema"] != "s31-mixed-native-phase-v1" or \
            phase["source_sha256"] != stage["source_sha256"] or \
            phase["circuit_identity_sha256"] != stage["circuit_identity_sha256"] or \
            phase["native_prove_including_setup_ns"] != native:
        raise ValueError("native phase identity differs from package stage")
    interaction, fri, pcs = (phase[key] for key in
                             ("interaction_pow_ns", "fri_pow_ns", "pcs_prove_ns"))
    if (any(type(value) is not int for value in
            (interaction, fri, pcs, phase["prove_body_ns"])) or
            not 0 < interaction < native or not 0 < fri <= pcs <= native or
            not 0 < phase["prove_body_ns"] <= native or
            interaction + fri > native or
            phase["pcs_without_fri_pow_ns"] != pcs - fri or
            phase["native_without_reported_pow_ns"] != native - interaction - fri):
        raise ValueError("native phase accounting inconsistent")
    return {"native_prove_including_setup_ns": native,
            "interaction_pow_ns": interaction, "fri_pow_ns": fri,
            "pcs_prove_ns": pcs, "native_without_reported_pow_ns":
                phase["native_without_reported_pow_ns"]}


def summarise(rows: list[dict]) -> dict:
    summary = {}
    for count in COUNTS:
        selected = [row for row in rows if row["count"] == count]
        if len(selected) != ASSIGNMENTS:
            raise ValueError("incomplete count cohort")
        summary[str(count)] = {
            "distinct_statements": len(selected),
            "timed_native_p50_ns": statistics.median(row["timed"]["native_prove_including_setup_ns"] for row in selected),
            "untimed_native_p50_ns": statistics.median(row["untimed"]["native_prove_including_setup_ns"] for row in selected),
            "interaction_pow_p50_ns": statistics.median(row["timed"]["interaction_pow_ns"] for row in selected),
            "fri_pow_p50_ns": statistics.median(row["timed"]["fri_pow_ns"] for row in selected),
            "first_verified_timed_p50_ns": statistics.median(row["timed"]["first_verified_wall_ns"] for row in selected),
            "first_verified_untimed_p50_ns": statistics.median(row["untimed"]["first_verified_wall_ns"] for row in selected),
        }
    return summary


def run(out: Path) -> dict:
    protocol, protocol_hash = frozen()
    if RESULT.exists():
        raise ValueError("mixed phase result already exists; do not overwrite")
    out.mkdir(parents=True, exist_ok=False)
    manifest = {"schema": "s31-mixed-phase-v1-raw-manifest",
                "protocol_sha256": protocol_hash, "binary_sha256": {}, "build_wall_ns": {}}
    for count in COUNTS:
        directory = out / f"n{count}"
        directory.mkdir()
        source_bytes = case(count, 0)[0]
        source_path = directory / "source.s31.json"
        source_path.write_bytes(source_bytes)
        name = f"mixed_phase_v1_n{count}"
        prefix = directory / "package"
        command = ["zig", "build", "--build-file", str(S31 / "build.zig"), "install",
                   "-Doptimize=ReleaseFast", "-Ds31-version=2",
                   "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
                   f"-Ds31-name={name}", "-j1", "--prefix", str(prefix)]
        built, build_ns = process(command)
        (directory / "build.stdout").write_bytes(built.stdout)
        (directory / "build.stderr").write_bytes(built.stderr)
        if built.returncode:
            raise RuntimeError(f"N{count} build failed: {built.stderr.decode(errors='replace')[-1500:]}")
        binary_root = prefix / "bin"
        base = f"s31-{name}-mixed-general-"
        binaries = {role: binary_root / (base + suffix) for role, suffix in
                    (("prover", "prover"), ("verifier", "native-verifier"))}
        manifest["binary_sha256"][str(count)] = {role: sha(path.read_bytes())
                                                   for role, path in binaries.items()}
        manifest["build_wall_ns"][str(count)] = build_ns
        manifest[str(count)] = str(directory)
    (out / "build-manifest.json").write_bytes(canonical(manifest))

    rows = []
    env = os.environ.copy()
    env.pop("STWO_ZIG_POW_WORKERS", None)
    for count in COUNTS:
        directory = out / f"n{count}"
        base = f"s31-mixed_phase_v1_n{count}-mixed-general-"
        prover = directory / "package/bin" / (base + "prover")
        verifier = directory / "package/bin" / (base + "native-verifier")
        for index in range(ASSIGNMENTS):
            source_bytes, assignment, statement = case(count, index)
            statement_hash = sha(statement)
            assignment_path = directory / f"a{index:02d}.assignment.json"
            statement_path = directory / f"a{index:02d}.statement.json"
            assignment_path.write_bytes(assignment)
            statement_path.write_bytes(statement)
            changed_path = directory / f"a{index:02d}.changed-result.json"
            changed_path.write_bytes(changed_result(source_bytes, statement))
            modes = ("untimed", "timed") if index % 2 == 0 else ("timed", "untimed")
            pair = {"count": count, "assignment_index": index,
                    "order": list(modes), "source_sha256": protocol["roster"][str(count)]["source_sha256"],
                    "assignment_sha256": sha(assignment), "statement_sha256": statement_hash}
            proof_bytes = []
            for mode in modes:
                if {role: sha(path.read_bytes()) for role, path in
                    (("prover", prover), ("verifier", verifier))} != \
                        manifest["binary_sha256"][str(count)]:
                    raise RuntimeError("package binary changed during paired study")
                trial_env = env.copy()
                trial_env.pop("S31_MIXED_NATIVE_PHASES", None)
                if mode == "timed":
                    trial_env["S31_MIXED_NATIVE_PHASES"] = "1"
                proof_path = directory / f"a{index:02d}.{mode}.proof"
                emitted_path = directory / f"a{index:02d}.{mode}.emitted.json"
                produced, prove_wall = process([str(prover), str(assignment_path),
                                                str(proof_path), str(emitted_path),
                                                str(statement_path)], trial_env)
                (directory / f"a{index:02d}.{mode}.stderr").write_bytes(produced.stderr)
                if produced.returncode or emitted_path.read_bytes() != statement or not proof_path.is_file():
                    raise RuntimeError(f"N{count}/a{index}/{mode} prover or statement failed")
                verified, verify_wall = process([str(verifier), str(proof_path),
                                                 str(statement_path)], trial_env)
                if verified.returncode or b"verified" not in verified.stderr:
                    raise RuntimeError(f"N{count}/a{index}/{mode} native verifier rejected")
                rejected, _ = process([str(verifier), str(proof_path), str(changed_path)], trial_env)
                if not proof_layer_rejection(rejected):
                    raise RuntimeError(f"N{count}/a{index}/{mode} changed result did not reach proof binding: {rejected.stderr.decode(errors='replace')}")
                stage = tagged(produced.stderr, b"S31_MIXED_STAGE_V1")
                if stage["source_sha256"] != pair["source_sha256"] or \
                        stage["proof_bytes"] != proof_path.stat().st_size:
                    raise RuntimeError("stage source or proof size differs")
                phase_lines = [line for line in produced.stderr.splitlines()
                               if line.startswith(b"S31_MIXED_NATIVE_PHASE_V1 ")]
                if mode == "timed":
                    if len(phase_lines) != 1:
                        raise RuntimeError("timed proof has no unique phase record")
                    phase = tagged(produced.stderr, b"S31_MIXED_NATIVE_PHASE_V1")
                    intervals = phase_check(stage, phase, prove_wall)
                else:
                    if phase_lines:
                        raise RuntimeError("untimed proof emitted phase record")
                    intervals = {"native_prove_including_setup_ns": stage_check(stage, prove_wall)}
                payload = proof_path.read_bytes()
                proof_bytes.append(payload)
                pair[mode] = {"proof_sha256": sha(payload), "proof_bytes": len(payload),
                              "prover_process_wall_ns": prove_wall,
                              "external_verifier_process_wall_ns": verify_wall,
                              "first_verified_wall_ns": prove_wall + verify_wall,
                              "changed_result_rejected": True,
                              "binary_sha256": manifest["binary_sha256"][str(count)],
                              **intervals}
            if proof_bytes[0] != proof_bytes[1]:
                raise RuntimeError(f"N{count}/a{index} timed proof changed proof bytes")
            rows.append(pair)
    if {key: protocol[key] for key in ("engine_gitlink_commit", "compiler_sha256",
                                      "zig_executable_sha256", "tool_sha256",
                                      "source_template_sha256")} != current_pins():
        raise RuntimeError("compiler, engine, tools or template changed during native study")
    result = {"schema": "s31-mixed-phase-v1-result",
              "status": "local-diagnostic-host-contention-not-controlled",
              "protocol_sha256": protocol_hash,
              "engine_gitlink_commit": protocol["engine_gitlink_commit"],
              "compiler_sha256": protocol["compiler_sha256"],
              "binary_sha256": manifest["binary_sha256"],
              "build_wall_ns": manifest["build_wall_ns"],
              "proof_pairs": len(rows), "native_accepted_proofs": 2 * len(rows),
              "changed_result_rejections": 2 * len(rows),
              "exact_proof_byte_pairs": len(rows), "rows": rows,
              "summary": summarise(rows),
              "speedup_claim_enabled": False, "predictive_model_enabled": False}
    (out / "result.json").write_bytes(canonical(result))
    RESULT.write_bytes(canonical(result))
    return {"result_sha256": sha(canonical(result)),
            "proof_pairs": len(rows), "native_accepted_proofs": 2 * len(rows)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="action", required=True)
    sub.add_parser("prepare")
    runner = sub.add_parser("run")
    runner.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    result = prepare() if args.action == "prepare" else run(args.out.resolve())
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
