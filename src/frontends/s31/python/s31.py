#!/usr/bin/env python3
"""S31 v0.1 command-line frontend and stable Python API."""

import sys
from pathlib import Path
S31_SOURCE_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))

import argparse
import copy
import json
import platform
import re
import statistics
import subprocess
import tempfile
import time

from package.build import build, build_json, build_text, package_for
from package.context import (
    AIR_BUNDLE_SHA256, BUILD_FILE, ENGINE_ROOT, LIBRARY_SOURCE_FILES,
    PINNED_ASSETS, PROJECTION_SHA256, ROOT, S31_DIR, TEXT_FRONTEND_SOURCES,
    abi, compiler_fingerprint, file_hash, invoke, load_source, lower_text,
    sha256, standard_library_lock, text_interface, write_json,
)
from package.verify import verify_package


def explain(package: Path) -> dict:
    from inspection.reports import explain as inspect_explain

    return inspect_explain(package, verify_package)


def equations(package: Path) -> dict:
    from inspection.reports import equations as inspect_equations

    return inspect_equations(package, verify_package)


def independent_value_check(relation: dict, assignment: dict) -> dict:
    """Check supported relation values without calling the Zig runtime or circuit."""
    from oracle import UnsupportedOperation, evaluate_relation

    try:
        computed = evaluate_relation(relation, assignment)
    except UnsupportedOperation as exc:
        return {"status": "unsupported", "reason": str(exc)}
    return {"status": "passed", "computed_public_outputs": computed}


def prover_stages(log: str) -> dict | None:
    """Parse the runtime's stage timers without inventing unavailable PoW data."""
    stages = re.search(r"witness=([\d.]+)s, setup=([\d.]+)s, prove=([\d.]+)s", log)
    if stages is None:
        return None
    result = {
        "witness_seconds": float(stages.group(1)),
        "setup_seconds": float(stages.group(2)),
        "prove_seconds": float(stages.group(3)),
    }
    pow_stages = re.search(r"interaction_pow=([\d.]+)s fri_pow=([\d.]+)s", log)
    if pow_stages is not None:
        interaction, fri = float(pow_stages.group(1)), float(pow_stages.group(2))
        result["interaction_pow_seconds"] = interaction
        result["fri_pow_seconds"] = fri
        result["prove_excluding_pow_seconds"] = max(0.0, result["prove_seconds"] - interaction - fri)
    return result


def assignment_digest(path: Path) -> str:
    """Hash assignment values, independent of JSON whitespace and key order."""
    canonical = json.dumps(json.loads(path.read_text()), sort_keys=True,
                           separators=(",", ":"), ensure_ascii=True).encode()
    return sha256(canonical)


def oracle_provenance() -> dict:
    """Pin the independent oracle code and constants used by this run."""
    sources = (
        S31_DIR / "python/oracle.py",
        S31_DIR / "python/poseidon2_oracle.py",
        ENGINE_ROOT / "src/frontends/riscv/air/memory_commitment/poseidon2_constants.zig",
    )
    return {
        "python_version": platform.python_version(),
        "source_sha256": {str(path.relative_to(ROOT)): file_hash(path) for path in sources},
    }


def trial(source_or_package: Path, assignment_path: Path, output: Path,
          lowering: str | None = None, fri_fold_step: int | None = None) -> dict:
    """Build, prove, verify, and record one reproducible agent-facing trial."""
    source_or_package = source_or_package.resolve()
    assignment_path = assignment_path.resolve()
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / "trial-report.json").unlink(missing_ok=True)
    started = time.perf_counter()
    if source_or_package.is_dir():
        package = source_or_package
        manifest = verify_package(package)
        if lowering is not None and lowering != manifest["lowering"]:
            raise ValueError("requested lowering differs from the supplied package")
        if fri_fold_step is not None and fri_fold_step != manifest.get("fri_fold_step", 1):
            raise ValueError("requested FRI fold step differs from the supplied package")
    else:
        package = build(source_or_package, output / "package", lowering or "gate",
                        1 if fri_fold_step is None else fri_fold_step)
        manifest = verify_package(package)
    build_seconds = time.perf_counter() - started
    assignment = json.loads(assignment_path.read_text())
    relation = json.loads((package / "source.s31.json").read_text())
    value_check = independent_value_check(relation, assignment)
    statement = {
        "public_inputs": assignment["public_inputs"],
        "public_outputs": assignment["public_outputs"],
    }
    abi_data = json.loads((package / "public-abi.json").read_text())
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    key = package / "verification-key.json"
    with tempfile.TemporaryDirectory(prefix=".trial-", dir=output) as directory:
        staging = Path(directory)
        proof = staging / "proof.bin"
        statement_path = staging / "statement.json"
        wrong_path = staging / "changed-statement.json"
        write_json(statement_path, statement)
        started = time.perf_counter()
        prover_log = invoke(str(prover), "prove", str(assignment_path), str(proof))
        prove_seconds = time.perf_counter() - started
        started = time.perf_counter()
        invoke(str(verifier), str(proof), str(statement_path), str(key))
        verify_seconds = time.perf_counter() - started
        changed = copy.deepcopy(statement)
        changed_field = None
        for category in ("public_outputs", "public_inputs"):
            for field in abi_data[category]:
                values = changed[category][field["name"]]
                if values:
                    bound = 65536 if field["kind"] == "u16" else (1 << 31) - 1
                    values[0] = (values[0] + 1) % bound
                    changed_field = f"{category}.{field['name']}[0]"
                    break
            if changed_field is not None:
                break
        if changed_field is None:
            raise ValueError("trial needs at least one public word to test statement binding")
        write_json(wrong_path, changed)
        try:
            invoke(str(verifier), str(proof), str(wrong_path), str(key))
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"native verifier accepted changed {changed_field}")
        proof_data = proof.read_bytes()
        (output / "proof.bin").write_bytes(proof_data)
        write_json(output / "statement.json", statement)
        write_json(output / "changed-statement.json", changed)
    source_equations = equations(package)
    write_json(output / "equations.json", source_equations)
    write_json(output / "explain.json", explain(package))
    cost = json.loads((package / "cost-report.json").read_text())
    result = {
        "schema": "s31-trial-v1",
        "program": manifest["name"],
        "package": str(package),
        "assignment": str(assignment_path),
        "lowering": manifest["lowering"],
        "fri_fold_step": manifest.get("fri_fold_step", 1),
        "profile": cost["profile"],
        "visible_fri": visible_fri(cost, manifest["lowering"]),
        "canonical_ir_sha256": cost["canonical_ir_sha256"],
        "program_sha256": manifest["program_sha256"],
        "raw": cost["raw"],
        "padded": cost["padded"],
        "preprocessed_cells": cost["preprocessed_cells"],
        "proof_sha256": sha256(proof_data),
        "proof_bytes": len(proof_data),
        "native_verifier_accepted": True,
        "changed_public_statement_rejected": changed_field,
        "text_source_relowered": "source_text_sha256" in manifest,
        "independent_value_oracle": value_check,
        "independent_value_oracle_provenance": oracle_provenance(),
        "build_or_load_seconds": build_seconds,
        "prove_seconds": prove_seconds,
        "prover_stages": prover_stages(prover_log),
        "verify_seconds": verify_seconds,
        "timing_note": "Single local observations; proof-of-work and cache state affect timings.",
        "artifacts": {
            "proof": "proof.bin", "statement": "statement.json",
            "changed_statement": "changed-statement.json",
            "equations": "equations.json", "explain": "explain.json",
        },
    }
    write_json(output / "trial-report.json", result)
    return result


def visible_fri(cost: dict, lowering: str) -> dict:
    """Give every lowering the same units for the visible FRI settings.

    The SHA shift/fused cost reports store log2(last-layer degree bound),
    whereas the older package reports store the degree bound itself.
    """
    raw = cost["fri"]
    last_layer = raw["last_layer_degree_bound"]
    if lowering in {"sha-shift", "sha-fused"}:
        last_layer = 1 << last_layer
    return {
        "pow_bits": raw["pow_bits"],
        "blowup_factor": 1 << raw["log_blowup_factor"],
        "last_layer_degree_bound": last_layer,
        "queries": raw["queries"],
        "fold_step": raw["fold_step"],
    }


def tune(source: Path, assignments: list[Path], output: Path,
         lowerings: list[str], warmup: Path | None = None) -> dict:
    """Compare proof profiles on the same source and assignment corpus."""
    if source.is_dir():
        raise ValueError("tune expects a source file so every profile compiles the same relation")
    if len(lowerings) < 2 or len(set(lowerings)) != len(lowerings):
        raise ValueError("tune requires at least two distinct --lowering values")
    if not assignments:
        raise ValueError("tune requires at least one assignment")
    source = source.resolve()
    assignments = [path.resolve() for path in assignments]
    warmup = warmup.resolve() if warmup is not None else None
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    (output / "tune-report.json").unlink(missing_ok=True)
    assignment_hashes = [assignment_digest(path) for path in assignments]
    packages = {}
    build_seconds = {}
    for lowering in lowerings:
        started = time.perf_counter()
        packages[lowering] = build(source, output / "packages" / lowering, lowering)
        build_seconds[lowering] = time.perf_counter() - started
    per_profile = {}
    canonical_digests = set()
    program_digests = set()
    for lowering, package in packages.items():
        manifest = verify_package(package)
        canonical_digests.add(manifest["canonical_ir_sha256"])
        program_digests.add(manifest["program_sha256"])
        if warmup is not None:
            trial(package, warmup, output / "warmup" / lowering)
        trials = [trial(package, assignment, output / "runs" / lowering / f"{index:03d}")
                  for index, assignment in enumerate(assignments)]
        proof_sizes = [item["proof_bytes"] for item in trials]
        wall_times = [item["prove_seconds"] for item in trials]
        verify_times = [item["verify_seconds"] for item in trials]
        non_pow_times = [item["prover_stages"]["prove_excluding_pow_seconds"]
                         for item in trials if item["prover_stages"] is not None and
                         "prove_excluding_pow_seconds" in item["prover_stages"]]
        cost = json.loads((package / "cost-report.json").read_text())
        per_profile[lowering] = {
            "package": str(package),
            "build_or_load_seconds": build_seconds[lowering],
            "profile": cost["profile"],
            "visible_fri": visible_fri(cost, lowering),
            "public_abi": json.loads((package / "public-abi.json").read_text()),
            "raw": cost["raw"],
            "padded": cost["padded"],
            "preprocessed_cells": cost["preprocessed_cells"],
            "proof_bytes_per_assignment": proof_sizes,
            "median_proof_bytes": statistics.median(proof_sizes),
            "wall_prove_seconds_per_assignment": wall_times,
            "median_wall_prove_seconds": statistics.median(wall_times),
            "native_verify_seconds_per_assignment": verify_times,
            "median_native_verify_seconds": statistics.median(verify_times),
            "prove_excluding_pow_seconds_per_assignment": non_pow_times,
            "median_prove_excluding_pow_seconds": (
                statistics.median(non_pow_times) if len(non_pow_times) == len(trials) else None),
            "native_verifier_accepted_all": all(item["native_verifier_accepted"] for item in trials),
            "changed_public_statement_rejected_all": all(
                item["changed_public_statement_rejected"] for item in trials),
            "independent_value_oracle_statuses": [
                item["independent_value_oracle"]["status"] for item in trials],
        }
    if len(program_digests) != 1 or len(canonical_digests) != 1:
        raise ValueError("tune profiles compiled different source or canonical relations")
    fri_settings = {json.dumps(item["visible_fri"], sort_keys=True)
                    for item in per_profile.values()}
    report = {
        "schema": "s31-tune-v1",
        "source": str(source),
        "program_sha256": next(iter(program_digests)),
        "canonical_ir_sha256": next(iter(canonical_digests)),
        "host": {"platform": platform.platform(), "machine": platform.machine(),
                 "python": platform.python_version(), "zig": invoke("zig", "version").strip()},
        "assignment_sha256": assignment_hashes,
        "independent_value_oracle_provenance": oracle_provenance(),
        "warmup_assignment_sha256": assignment_digest(warmup) if warmup is not None else None,
        "distinct_assignments": len(set(assignment_hashes)) == len(assignment_hashes),
        "same_visible_fri_settings": len(fri_settings) == 1,
        "profiles": per_profile,
        "timing_note": ("Use --warmup for one unmeasured proof per profile. Transcript-dependent "
                        "proof-of-work varies with the assignment; compare repeated distinct witnesses. "
                        "Visible FRI settings alone do not establish equal soundness across AIRs. "
                        "No profile is selected automatically."),
    }
    write_json(output / "tune-report.json", report)
    return report


def replay_state_step(previous: list[int], body: list[dict]) -> list[int]:
    """Independent scalar M31 replay of a sealed four-lane fold transition."""
    p = (1 << 31) - 1
    if len(previous) != 4 or any(type(word) is not int or not 0 <= word < p for word in previous):
        raise ValueError("invalid state-fold checkpoint state")
    values = previous.copy()
    for operation in body:
        op = operation.get("op")
        constant = operation.get("constant")
        if op == "square" and constant is None:
            values = [(value * value) % p for value in values]
        elif op in {"add_const", "mul_const"} and type(constant) is int and 0 <= constant < p:
            values = [((value + constant) if op == "add_const" else (value * constant)) % p
                      for value in values]
        elif op == "mix4" and constant is None:
            total = sum(values) % p
            values = [(value + total) % p for value in values]
        else:
            raise ValueError("unsupported sealed state-fold step operation")
    return values


def audit_fold_chain(package: Path, manifest: dict, proofs: list[Path], state: bool,
                     max_step: int | None) -> dict:
    """Verify every checkpoint and replay its public claim continuity."""
    if not proofs:
        raise ValueError("a fold chain needs at least one proof")
    if max_step is not None and not (0 <= max_step <= 0xffffffff):
        raise ValueError("--max-step must fit u32")
    if len(proofs) - 1 > 0xffffffff or (max_step is not None and len(proofs) - 1 > max_step):
        raise ValueError("fold chain exceeds the locally trusted depth")
    wide = manifest["lowering"] == "sparse-wide-gate"
    if state and (manifest["lowering"] != "gate" or
                  "state-fold-verification-key.json" not in manifest["artifacts"]):
        raise ValueError("state-fold chain requires a supported gate recurrence package")
    if not state and manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
        raise ValueError("fixed-fold chain requires a gate or sparse-wide package")
    expected_schema = ("s31-state-fold-statement-v2" if state else
                       "s31-fixed-fold-statement-v4" if wide else "s31-fixed-fold-statement-v3")
    key_field = "state_fold_key_sha256" if state else "fold_key_sha256"
    native_command = "state-fold-verify" if state else "fold-verify"
    verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
    body = None
    if state:
        key = json.loads((package / "state-fold-verification-key.json").read_text())
        body = key["step_body"]
    previous = None
    for index, raw_proof in enumerate(proofs):
        proof = raw_proof.resolve()
        statement_path = Path(str(proof) + ".statement.json")
        item = json.loads(statement_path.read_text())
        if item.get("schema") != expected_schema or type(item.get("step")) is not int or item["step"] != index:
            raise ValueError(f"fold checkpoint must have contiguous step {index}: {proof}")
        if previous is not None:
            for field in (key_field, "fold_preprocessed_root", "fold_circuit_hash",
                          "leaf_public_words", "base_public_words"):
                if item[field] != previous[field]:
                    raise ValueError(f"fold checkpoint changed {field} at step {index}")
        if state:
            if item["initial_state"] != item["leaf_public_words"][4:8]:
                raise ValueError("state-fold initial state differs from leaf output")
            if index == 0:
                if item["current_state"] != item["initial_state"]:
                    raise ValueError("state-fold base current state differs from initial state")
            elif (item["initial_state"] != previous["initial_state"] or
                  item["current_state"] != replay_state_step(previous["current_state"], body)):
                raise ValueError(f"state-fold transition mismatch at step {index}")
        invoke(str(verifier), native_command, str(proof), str(statement_path),
               *(("--max-step", str(max_step)) if max_step is not None else ()))
        previous = item
    result = {
        "schema": "s31-fold-chain-audit-v1",
        "kind": "state" if state else "fixed",
        "proofs_verified": len(proofs),
        "top_step": len(proofs) - 1,
        "leaf_public_words": previous["leaf_public_words"],
        "base_public_words": previous["base_public_words"],
        "fold_preprocessed_root": previous["fold_preprocessed_root"],
    }
    if state:
        result["initial_state"] = previous["initial_state"]
        result["current_state"] = previous["current_state"]
    return result


def main() -> None:
    parser = argparse.ArgumentParser(prog="s31", description="S31 circuit relation compiler")
    commands = parser.add_subparsers(dest="command", required=True)
    for command in ("check", "inspect", "explain", "equations", "run"):
        help_text = {
            "explain": "show canonical nodes, source positions, and builder gate counts",
            "equations": "show source-level field equations (not expanded AIR terms)",
        }.get(command)
        sub = commands.add_parser(command, help=help_text)
        sub.add_argument("source_or_package", type=Path)
        if command == "run":
            sub.add_argument("assignment", type=Path)
    sub = commands.add_parser("build")
    sub.add_argument("source", type=Path)
    sub.add_argument("--out", type=Path, required=True)
    sub.add_argument("--lowering", choices=("gate", "chip", "sparse-gate", "sparse-chip", "sparse-wide-gate", "direct-gate", "direct-chip", "sha-joint", "sha-shift", "sha-fused"), default="gate")
    sub.add_argument("--fri-fold-step", type=int, choices=(1, 4), default=1,
                     help="FRI folds per commitment for gate or sparse-wide-gate proofs; 4 can shrink recursive verifier circuits")
    sub = commands.add_parser("trial", help="build, prove, verify, and record one trial")
    sub.add_argument("source_or_package", type=Path)
    sub.add_argument("assignment", type=Path)
    sub.add_argument("--out", type=Path, required=True)
    sub.add_argument("--lowering", choices=("gate", "chip", "sparse-gate", "sparse-chip", "sparse-wide-gate", "direct-gate", "direct-chip", "sha-joint", "sha-shift", "sha-fused"))
    sub.add_argument("--fri-fold-step", type=int, choices=(1, 4),
                     help="select a gate or sparse-wide-gate package's FRI schedule, or check a supplied package")
    sub = commands.add_parser("tune", help="compare verified proof profiles on one source and assignment corpus")
    sub.add_argument("source", type=Path)
    sub.add_argument("assignments", type=Path, nargs="+")
    sub.add_argument("--warmup", type=Path, help="valid assignment proved once per profile before measurement")
    sub.add_argument("--out", type=Path, required=True)
    sub.add_argument("--lowering", action="append", required=True,
                     choices=("gate", "chip", "sparse-gate", "sparse-chip", "sparse-wide-gate", "direct-gate", "direct-chip", "sha-joint", "sha-shift", "sha-fused"))
    sub = commands.add_parser("oracle", help="check normalized relation values without building a proof")
    sub.add_argument("source_or_package", type=Path)
    sub.add_argument("assignment", type=Path)
    sub = commands.add_parser("lower", help="lower .s31 text to normalized relation JSON")
    sub.add_argument("source", type=Path)
    sub.add_argument("--out", type=Path)
    sub = commands.add_parser("prove")
    sub.add_argument("package", type=Path)
    sub.add_argument("assignment", type=Path)
    sub.add_argument("proof", type=Path)
    sub = commands.add_parser("wrap", help="prove verification of a saved gate or sparse-wide S31 proof")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("outer_proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--low-memory", action="store_true",
                     help="retain committed evaluations only; lower peak RAM with some extra proving time")
    sub = commands.add_parser("wrap-next", help="prove verification of an already recursive S31 proof")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("outer_proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--low-memory", action="store_true")
    for command, description in (
        ("fold-base", "start a fixed-key fold from a first-level recursive proof"),
        ("fold-next", "extend a fixed-key fold under the same verification key"),
        ("state-fold-base", "start a state-transition fold from a first-level recursive proof"),
        ("state-fold-next", "prove one more source recurrence step under the same key"),
    ):
        sub = commands.add_parser(command, help=description)
        sub.add_argument("package", type=Path)
        sub.add_argument("child_proof", type=Path)
        sub.add_argument("outer_proof", type=Path)
        sub.add_argument("--statement", type=Path)
        sub.add_argument("--low-memory", action="store_true")
    sub = commands.add_parser("fold-advance", help="prove several fixed-key folds while reusing the sealed AIR")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("outer_proof", type=Path)
    sub.add_argument("--steps", type=int, required=True)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--checkpoint-dir", type=Path, help="keep intermediate proofs for resume")
    sub.add_argument("--low-memory", action="store_true")
    sub = commands.add_parser("state-fold-advance", help="prove several source steps, with optional resumable checkpoints")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("outer_proof", type=Path)
    sub.add_argument("--steps", type=int, required=True,
                     help="number of new fold proofs; the first starts at step zero for a recursive base proof")
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--checkpoint-dir", type=Path,
                     help="keep each intermediate proof and statement for resume")
    sub.add_argument("--low-memory", action="store_true")
    sub = commands.add_parser("audit-recursive", help="audit a saved child proof's in-circuit verifier inputs")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("audit-recursive-next", help="audit the in-circuit verifier for a recursive child proof")
    sub.add_argument("package", type=Path)
    sub.add_argument("child_proof", type=Path)
    sub.add_argument("--statement", type=Path)
    for command, description in (
        ("audit-fold-base", "challenge a fixed-key fold's base circuit inputs"),
        ("audit-fold-next", "challenge a fixed-key fold's recursive circuit inputs"),
        ("audit-state-fold-base", "challenge a state fold's base circuit and counter"),
        ("audit-state-fold-next", "challenge a state fold's transition and recursive verifier"),
    ):
        sub = commands.add_parser(command, help=description)
        sub.add_argument("package", type=Path)
        sub.add_argument("child_proof", type=Path)
        sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("verify")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("verify-recursive", help="verify an outer proof against its embedded child key")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("verify-recursive-next", help="verify a two-level recursive chain")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub = commands.add_parser("verify-fold", help="verify a fixed-key fold using only its top proof and statement")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--max-step", type=int, help="reject a top fold statement above this locally trusted recursion depth")
    sub = commands.add_parser("verify-state-fold", help="verify a recursive state-transition proof from its top proof")
    sub.add_argument("package", type=Path)
    sub.add_argument("proof", type=Path)
    sub.add_argument("--statement", type=Path)
    sub.add_argument("--max-step", type=int, help="reject a top fold statement above this locally trusted recursion depth")
    for command, description in (
        ("audit-fold-chain", "verify every fixed-fold checkpoint and its public claim continuity"),
        ("audit-state-fold-chain", "verify every state-fold checkpoint and replay its source transition"),
    ):
        sub = commands.add_parser(command, help=description)
        sub.add_argument("package", type=Path)
        sub.add_argument("proofs", type=Path, nargs="+", help="fold proofs from step zero through the top step")
        sub.add_argument("--max-step", type=int)
    sub = commands.add_parser("inspect-fold", help="rebuild and report a sealed fold AIR's raw rows and padding headroom")
    sub.add_argument("package", type=Path)
    sub.add_argument("--step", type=int, default=0, help="rebuild the witness-free AIR at this u32 counter value")
    sub = commands.add_parser("inspect-state-fold", help="rebuild and report a state-fold AIR's raw rows and padding headroom")
    sub.add_argument("package", type=Path)
    sub.add_argument("--step", type=int, default=0, help="rebuild the witness-free AIR at this u32 counter value")
    args = parser.parse_args()

    if args.command == "lower":
        if args.source.suffix != ".s31":
            raise ValueError("lower expects a .s31 text file")
        _, normalized, _ = lower_text(args.source)
        if args.out:
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_bytes(normalized)
            print(args.out)
        else:
            sys.stdout.buffer.write(normalized)
        return
    if args.command == "build":
        print(build(args.source, args.out, args.lowering, args.fri_fold_step))
        return
    if args.command == "trial":
        print(json.dumps(trial(args.source_or_package, args.assignment, args.out,
                               args.lowering, args.fri_fold_step),
                         indent=2, sort_keys=True))
        return
    if args.command == "tune":
        print(json.dumps(tune(args.source, args.assignments, args.out, args.lowering,
                              args.warmup),
                         indent=2, sort_keys=True))
        return
    if args.command == "oracle":
        if args.source_or_package.is_dir():
            package = args.source_or_package.resolve()
            verify_package(package)
            relation = json.loads((package / "source.s31.json").read_text())
        elif args.source_or_package.suffix == ".s31":
            relation, _, _ = lower_text(args.source_or_package.resolve())
        else:
            relation, _ = load_source(args.source_or_package.resolve())
        result = independent_value_check(relation, json.loads(args.assignment.read_text()))
        if result["status"] != "passed":
            raise ValueError(result["reason"])
        print(json.dumps({"schema": "s31-oracle-v1", "program": relation["name"], **result},
                         indent=2, sort_keys=True))
        return
    if args.command == "explain":
        print(json.dumps(explain(package_for(args.source_or_package)), indent=2, sort_keys=True))
        return
    if args.command == "equations":
        print(json.dumps(equations(package_for(args.source_or_package)), indent=2, sort_keys=True))
        return
    if args.command in ("check", "inspect", "run"):
        package = package_for(args.source_or_package)
        manifest = verify_package(package)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        extra = (str(args.assignment.resolve()),) if args.command == "run" else ()
        print(invoke(str(executable), args.command, *extra), end="")
        return

    package = args.package.resolve()
    manifest = verify_package(package)
    if args.command == "prove":
        assignment = json.loads(args.assignment.read_text())
        statement = {
            "public_inputs": assignment["public_inputs"],
            "public_outputs": assignment["public_outputs"],
        }
        proof = args.proof.resolve()
        proof.parent.mkdir(parents=True, exist_ok=True)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "prove", str(args.assignment.resolve()), str(proof)), end="")
        statement_path = Path(str(proof) + ".statement.json")
        write_json(statement_path, statement)
        print(f"public statement: {statement_path}")
    elif args.command == "wrap":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("wrap requires a gate or sparse-wide package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        outer.parent.mkdir(parents=True, exist_ok=True)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        command = "recurse-wide-wrap" if manifest["lowering"] == "sparse-wide-gate" else "recurse-wrap"
        print(invoke(str(executable), command, str(child), str(statement),
                     str(outer), str(package / "verification-key.json"),
                     *(("--low-memory",) if args.low_memory else ())), end="")
        print(f"recursive statement: {outer}.statement.json")
    elif args.command == "wrap-next":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("wrap-next requires a gate or sparse-wide package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        outer.parent.mkdir(parents=True, exist_ok=True)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "recurse-wrap-next", str(child), str(statement),
                     str(outer), str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     str(package / "recursive-verification-key-level2.json"),
                     *(("--low-memory",) if args.low_memory else ())), end="")
        print(f"recursive chain statement: {outer}.statement.json")
    elif args.command in ("fold-base", "fold-next", "state-fold-base", "state-fold-next"):
        wide_fold = manifest["lowering"] == "sparse-wide-gate" and args.command in ("fold-base", "fold-next")
        if manifest["lowering"] != "gate" and not wide_fold:
            raise ValueError(f"{args.command} requires a gate or supported sparse-wide package")
        if args.command.startswith("state-fold-") and "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("source does not expose a supported typed recurrence step")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        outer.parent.mkdir(parents=True, exist_ok=True)
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        command = {
            "fold-base": "fold-wrap-base",
            "fold-next": "fold-wrap-next",
            "state-fold-base": "state-fold-wrap-base",
            "state-fold-next": "state-fold-wrap-next",
        }[args.command]
        if wide_fold:
            command = "wide-" + command
        key_name = ("state-fold-verification-key.json" if args.command.startswith("state-fold-")
                    else "fixed-fold-verification-key.json")
        print(invoke(str(executable), command, str(child), str(statement), str(outer),
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     *((str(package / "recursive-verification-key-level2.json"),) if wide_fold else ()),
                     str(package / key_name),
                     *(("--low-memory",) if args.low_memory else ())), end="")
        print(f"fold statement: {outer}.statement.json")
    elif args.command == "fold-advance":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"} or "s31-fixed-fold-batch-v1" not in manifest.get("capabilities", []):
            raise ValueError("fold-advance requires a package with the fixed-fold batch capability")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        if child == outer or args.steps < 1 or args.steps > 65536:
            raise ValueError("fold-advance needs a distinct output and 1..65536 steps")
        wide_fold = manifest["lowering"] == "sparse-wide-gate"
        initial = json.loads(statement.read_text())
        base_schema = "s31-recursive-chain-statement-v1" if wide_fold else "s31-recursive-gate-statement-v2"
        fold_schema = "s31-fixed-fold-statement-v4" if wide_fold else "s31-fixed-fold-statement-v3"
        if initial.get("schema") == base_schema:
            first_step = 0
            base_case = True
        elif initial.get("schema") == fold_schema:
            prior_step = initial.get("step")
            if type(prior_step) is not int or prior_step < 0 or prior_step > 0xffffffff:
                raise ValueError("input fixed-fold statement has an invalid step counter")
            first_step = prior_step + 1
            base_case = False
        else:
            raise ValueError("input must be a recursive base or fixed-fold proof")
        if first_step + args.steps - 1 > 0xffffffff:
            raise ValueError("fixed-fold step counter would overflow")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        outer.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="s31-fixed-fold-advance-") as temporary:
            checkpoints = args.checkpoint_dir.resolve() if args.checkpoint_dir else Path(temporary)
            checkpoints.mkdir(parents=True, exist_ok=True)
            planned_paths: set[Path] = set()
            for index in range(args.steps):
                step = first_step + index
                target = outer if index == args.steps - 1 else checkpoints / f"fold-{step:05d}.proof"
                target_statement = Path(str(target) + ".statement.json")
                if target in planned_paths or target_statement in planned_paths or target in {child, statement} or target_statement in {child, statement}:
                    raise ValueError(f"fold batch paths collide: {target}")
                planned_paths.update((target, target_statement))
                if target.exists() or target_statement.exists():
                    raise ValueError(f"refusing to overwrite fold proof or statement: {target}")
            print(invoke(str(executable), "wide-fold-wrap-batch" if wide_fold else "fold-wrap-batch",
                         str(child), str(statement), str(outer),
                         str(package / "verification-key.json"),
                         str(package / "recursive-verification-key.json"),
                         *((str(package / "recursive-verification-key-level2.json"),) if wide_fold else ()),
                         str(package / "fixed-fold-verification-key.json"),
                         str(args.steps), str(checkpoints), str(first_step),
                         "base" if base_case else "next",
                         *(("--low-memory",) if args.low_memory else ())), end="")
        print(f"fold statement: {outer}.statement.json")
    elif args.command == "state-fold-advance":
        if manifest["lowering"] != "gate" or "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("state-fold-advance requires a supported gate-profile recurrence package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        outer = args.outer_proof.resolve()
        if child == outer or args.steps < 1:
            raise ValueError("state-fold-advance needs a distinct output and at least one step")
        if args.steps > 65536:
            raise ValueError("state-fold-advance accepts at most 65536 proofs per batch; resume from a checkpoint")
        state_key = json.loads((package / "state-fold-verification-key.json").read_text())
        new_counter = state_key["schema"] == "s31-state-fold-verification-key-v3"
        expected_statement = "s31-state-fold-statement-v2" if new_counter else "s31-state-fold-statement-v1"
        counter_max = (1 << 32) - 1 if new_counter else 65535
        initial = json.loads(statement.read_text())
        if initial.get("schema") == "s31-recursive-gate-statement-v2":
            first_step = 0
            base_case = True
        elif initial.get("schema") == expected_statement:
            prior_step = initial.get("step")
            if type(prior_step) is not int or prior_step < 0 or prior_step > counter_max:
                raise ValueError("input state-fold statement has an invalid step counter")
            first_step = initial["step"] + 1
            base_case = False
        else:
            raise ValueError("input must be a first-level recursive or state-fold proof")
        if first_step + args.steps - 1 > counter_max:
            raise ValueError("state-fold step counter would overflow")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        outer.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix="s31-state-fold-advance-") as temporary:
            checkpoints = args.checkpoint_dir.resolve() if args.checkpoint_dir else Path(temporary)
            checkpoints.mkdir(parents=True, exist_ok=True)
            planned_paths = set()
            for index in range(args.steps):
                step = first_step + index
                target = (outer if index == args.steps - 1 else
                          checkpoints / f"state-{step:05d}.proof")
                target_statement = Path(str(target) + ".statement.json")
                if target in planned_paths or target_statement in planned_paths:
                    raise ValueError(f"state-fold batch outputs collide: {target}")
                planned_paths.update((target, target_statement))
                if target.exists() or target_statement.exists():
                    raise ValueError(f"refusing to overwrite fold proof or statement: {target}")
            batch_capability = ("s31-state-fold-batch-v2" if new_counter else "s31-state-fold-batch-v1")
            if batch_capability in manifest.get("capabilities", []):
                print(invoke(str(executable), "state-fold-wrap-batch", str(child), str(statement),
                             str(outer), str(package / "verification-key.json"),
                             str(package / "recursive-verification-key.json"),
                             str(package / "state-fold-verification-key.json"),
                             str(args.steps), str(checkpoints), str(first_step),
                             "base" if base_case else "next",
                             *(("--low-memory",) if args.low_memory else ())), end="")
                statement = Path(str(outer) + ".statement.json")
            else:
                # Old packages carry their own v1 binary, which only has the
                # one-step command. Preserve their installed proof format.
                for index in range(args.steps):
                    step = first_step + index
                    target = (outer if index == args.steps - 1 else
                              checkpoints / f"state-{step:05d}.proof")
                    target_statement = Path(str(target) + ".statement.json")
                    command = "state-fold-wrap-base" if base_case and index == 0 else "state-fold-wrap-next"
                    print(invoke(str(executable), command, str(child), str(statement), str(target),
                                 str(package / "verification-key.json"),
                                 str(package / "recursive-verification-key.json"),
                                 str(package / "state-fold-verification-key.json"),
                                 *(("--low-memory",) if args.low_memory else ())), end="")
                    child, statement = target, target_statement
            print(invoke(str(verifier), "state-fold-verify", str(outer), str(statement)), end="")
        print(f"state-fold top proof: {outer}")
    elif args.command == "audit-recursive":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("audit-recursive requires a gate or sparse-wide package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        command = "recurse-wide-audit" if manifest["lowering"] == "sparse-wide-gate" else "recurse-audit"
        print(invoke(str(executable), command, str(child), str(statement),
                     str(package / "verification-key.json")), end="")
    elif args.command == "audit-recursive-next":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("audit-recursive-next requires a gate or sparse-wide package")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "recurse-audit-next", str(child), str(statement),
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json")), end="")
    elif args.command in ("audit-fold-base", "audit-fold-next", "audit-state-fold-base", "audit-state-fold-next"):
        wide_fold = manifest["lowering"] == "sparse-wide-gate" and args.command in ("audit-fold-base", "audit-fold-next")
        if manifest["lowering"] != "gate" and not wide_fold:
            raise ValueError(f"{args.command} requires a gate or supported sparse-wide package")
        if args.command.startswith("audit-state-fold-") and "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("source does not expose a supported typed recurrence step")
        child = args.child_proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(child) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        command = {
            "audit-fold-base": "fold-audit",
            "audit-fold-next": "fold-audit-next",
            "audit-state-fold-base": "state-fold-audit-base",
            "audit-state-fold-next": "state-fold-audit-next",
        }[args.command]
        if wide_fold:
            command = "wide-fold-audit-base" if args.command == "audit-fold-base" else "wide-fold-audit-next"
        key_name = ("state-fold-verification-key.json" if args.command.startswith("audit-state-fold-")
                    else "fixed-fold-verification-key.json")
        print(invoke(str(executable), command, str(child), str(statement),
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     *((str(package / "recursive-verification-key-level2.json"),) if wide_fold else ()),
                     str(package / key_name)), end="")
    elif args.command == "verify":
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        print(invoke(str(executable), str(proof), str(statement), str(package / "verification-key.json")), end="")
    elif args.command == "verify-recursive":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("verify-recursive requires a gate or sparse-wide package")
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        print(invoke(str(executable), "recurse-verify", str(proof), str(statement)), end="")
    elif args.command == "verify-recursive-next":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("verify-recursive-next requires a gate or sparse-wide package")
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        print(invoke(str(executable), "recurse-verify-next", str(proof), str(statement)), end="")
    elif args.command == "verify-fold":
        if manifest["lowering"] not in {"gate", "sparse-wide-gate"}:
            raise ValueError("verify-fold requires a gate or sparse-wide package")
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        if args.max_step is not None and not (0 <= args.max_step <= 0xffffffff):
            raise ValueError("--max-step must fit u32")
        max_step = ("--max-step", str(args.max_step)) if args.max_step is not None else ()
        print(invoke(str(executable), "fold-verify", str(proof), str(statement), *max_step), end="")
    elif args.command == "verify-state-fold":
        if manifest["lowering"] != "gate" or "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("verify-state-fold requires a supported gate-profile recurrence package")
        proof = args.proof.resolve()
        statement = args.statement.resolve() if args.statement else Path(str(proof) + ".statement.json")
        executable = package / "bin" / f"s31-{manifest['name']}-native-verifier"
        if args.max_step is not None and not (0 <= args.max_step <= 0xffffffff):
            raise ValueError("--max-step must fit u32")
        max_step = ("--max-step", str(args.max_step)) if args.max_step is not None else ()
        print(invoke(str(executable), "state-fold-verify", str(proof), str(statement), *max_step), end="")
    elif args.command in {"audit-fold-chain", "audit-state-fold-chain"}:
        result = audit_fold_chain(package, manifest, args.proofs,
                                  args.command == "audit-state-fold-chain", args.max_step)
        print(json.dumps(result, sort_keys=True))
    elif args.command == "inspect-fold":
        wide_fold = manifest["lowering"] == "sparse-wide-gate"
        if manifest["lowering"] != "gate" and not wide_fold:
            raise ValueError("inspect-fold requires a gate or sparse-wide package")
        if not 0 <= args.step <= 0xffffffff:
            raise ValueError("--step must fit u32")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "wide-fold-inspect" if wide_fold else "fold-inspect",
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     *((str(package / "recursive-verification-key-level2.json"),) if wide_fold else ()),
                     str(package / "fixed-fold-verification-key.json"), "--step", str(args.step)), end="")
    elif args.command == "inspect-state-fold":
        if manifest["lowering"] != "gate" or "state-fold-verification-key.json" not in manifest["artifacts"]:
            raise ValueError("inspect-state-fold requires a supported gate-profile recurrence package")
        if not 0 <= args.step <= 0xffffffff:
            raise ValueError("--step must fit u32")
        executable = package / "bin" / f"s31-{manifest['name']}-prover"
        print(invoke(str(executable), "state-fold-inspect",
                     str(package / "verification-key.json"),
                     str(package / "recursive-verification-key.json"),
                     str(package / "state-fold-verification-key.json"), "--step", str(args.step)), end="")


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, UnicodeError, RuntimeError, KeyError, json.JSONDecodeError) as exc:
        print(f"s31: {exc}", file=sys.stderr)
        raise SystemExit(1)
