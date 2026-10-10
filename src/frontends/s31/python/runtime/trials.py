"""Run source-bound native proof trials and compare verified profiles."""

from __future__ import annotations

import copy
import json
import platform
import re
import statistics
import tempfile
import time
from pathlib import Path

from abi.binding_v2 import statement_from_assignment
from inspection.reports import equations as report_equations, explain as report_explain
from package.build import build
from package.context import ENGINE_ROOT, ROOT, S31_DIR, file_hash, invoke, sha256, write_json
from package.verify import verify_package
from runtime.cost_model import measured_invoke, observed_cost_model


def explain(package: Path) -> dict:
    return report_explain(package, verify_package)


def equations(package: Path) -> dict:
    return report_equations(package, verify_package)


def independent_value_check(relation: dict, assignment: dict) -> dict:
    """Check supported relation values without calling the Zig runtime or circuit."""
    from oracle import UnsupportedOperation, evaluate_relation

    try:
        semantic = {**relation, "version": 1} if relation.get("version") == 2 else relation
        if semantic is not relation:
            semantic.pop("public_abi")
        computed = evaluate_relation(semantic, assignment)
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
        residual = result["prove_seconds"] - interaction - fri
        if residual < -0.000003:
            raise ValueError("reported PoW stages exceed the native prove timer")
        result["prove_excluding_pow_seconds"] = max(0.0, residual)
    total = re.search(r"total through verification=([\d.]+)s", log)
    if total is not None:
        result["total_through_verification_seconds"] = float(total.group(1))
        other = result["total_through_verification_seconds"] - sum(
            result[name] for name in ("witness_seconds", "setup_seconds", "prove_seconds"))
        if other >= -0.000003:
            result["runtime_other_seconds"] = max(0.0, other)
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
        if relation["version"] == 2:
            statement_path.write_bytes(statement_from_assignment(relation, assignment))
        else:
            write_json(statement_path, statement)
        prove_measurement = measured_invoke(str(prover), "prove", str(assignment_path), str(proof))
        prover_log = prove_measurement["output"]
        prove_seconds = prove_measurement["wall_seconds"]
        verify_measurement = measured_invoke(str(verifier), str(proof), str(statement_path), str(key))
        verify_seconds = verify_measurement["wall_seconds"]
        changed = (json.loads(statement_path.read_text()) if relation["version"] == 2
                   else copy.deepcopy(statement))
        changed_field = None
        if relation["version"] == 2:
            leaf = changed["leaves"][0]
            leaf["words"][0] = (leaf["words"][0] + 1) % ((1 << 31) - 1)
            changed_field = "leaves[0].words[0]"
        else:
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
        if relation["version"] == 2:
            wrong_path.write_text(json.dumps(changed, sort_keys=True, separators=(",", ":"), ensure_ascii=True) + "\n")
        else:
            write_json(wrong_path, changed)
        try:
            invoke(str(verifier), str(proof), str(wrong_path), str(key))
        except RuntimeError:
            pass
        else:
            raise RuntimeError(f"native verifier accepted changed {changed_field}")
        proof_data = proof.read_bytes()
        (output / "proof.bin").write_bytes(proof_data)
        (output / "statement.json").write_bytes(statement_path.read_bytes())
        (output / "changed-statement.json").write_bytes(wrong_path.read_bytes())
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
        "prover_peak_rss_bytes": prove_measurement["peak_rss_bytes"],
        "prover_peak_rss_method": prove_measurement["peak_rss_method"],
        "verify_seconds": verify_seconds,
        "verifier_peak_rss_bytes": verify_measurement["peak_rss_bytes"],
        "verifier_peak_rss_method": verify_measurement["peak_rss_method"],
        "timing_note": "Single local observation; every prover process constructs cold native setup. Wall time includes process startup and both PoW stages when present. Peak RSS is per process and null when unavailable.",
        "artifacts": {
            "proof": "proof.bin", "statement": "statement.json",
            "changed_statement": "changed-statement.json",
            "equations": "equations.json", "explain": "explain.json",
        },
    }
    result["observed_cost_model"] = observed_cost_model([result])
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
            "observed_cost_model": observed_cost_model(trials),
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
        "distinct_assignment_count": len(set(assignment_hashes)),
        "independent_value_oracle_provenance": oracle_provenance(),
        "warmup_assignment_sha256": assignment_digest(warmup) if warmup is not None else None,
        "distinct_assignments": len(set(assignment_hashes)) == len(assignment_hashes),
        "same_visible_fri_settings": len(fri_settings) == 1,
        "profiles": per_profile,
        "timing_note": ("--warmup runs one unmeasured, separate native process per profile; it may warm OS caches "
                        "but does not reuse that process's preprocessed commitment. Each measured process constructs "
                        "cold native setup. Transcript-dependent proof-of-work varies with the assignment; "
                        "compare repeated distinct witnesses. "
                        "Visible FRI settings alone do not establish equal soundness across AIRs. "
                        "No profile is selected automatically."),
    }
    write_json(output / "tune-report.json", report)
    return report
