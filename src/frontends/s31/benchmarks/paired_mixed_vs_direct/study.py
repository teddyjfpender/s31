#!/usr/bin/env python3
"""One prospective native paired run after protocol.py is committed.

Builds are recorded separately. Every scored pair uses byte-identical source,
assignment and public statement for both lowerings, with balanced randomized
profile order. Proof acceptance is by separate source-pinned native verifiers.
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import statistics
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import design
import protocol

sys.path.insert(0, str(protocol.S31 / "python"))
from abi.binding_v2 import decode_public_statement, statement_from_assignment  # noqa: E402

RESULT = protocol.ROOT / "design/s31/measurements/language/paired-mixed-vs-direct-v1-result.json"
SUMMARY = protocol.ROOT / "design/s31/measurements/language/paired-mixed-vs-direct-v1-summary.json"


def process(args: list[str], *, measure: bool = False,
            timeout_seconds: int = 120, mixed_phase_timing: bool = False) -> tuple[subprocess.CompletedProcess[bytes], dict]:
    method = "unavailable"
    with tempfile.TemporaryDirectory(prefix="s31-paired-time-") as temp:
        resource = Path(temp) / "resource.txt"
        command = args
        if measure and Path("/usr/bin/time").is_file() and platform.system() == "Darwin":
            command = ["/usr/bin/time", "-l", "-o", str(resource), *args]
            method = "darwin-time-max-rss-bytes"
        elif measure and Path("/usr/bin/time").is_file() and platform.system() == "Linux":
            command = ["/usr/bin/time", "-f", "%M", "-o", str(resource), *args]
            method = "gnu-time-max-rss-kib"
        start = time.perf_counter_ns()
        env = {k: v for k, v in os.environ.items() if k != "STWO_ZIG_POW_WORKERS"}
        if mixed_phase_timing:
            env["S31_MIXED_NATIVE_PHASES"] = "1"
        result = subprocess.run(command, cwd=protocol.ROOT, capture_output=True,
                                timeout=timeout_seconds,
                                env=env)
        wall_ns = time.perf_counter_ns() - start
        peak = None
        if resource.exists():
            raw = resource.read_text()
            if method == "darwin-time-max-rss-bytes":
                match = re.search(r"^\s*(\d+)\s+maximum resident set size\s*$", raw, re.M)
                if match:
                    peak = int(match.group(1))
            elif method == "gnu-time-max-rss-kib" and raw.strip().isdigit():
                peak = int(raw.strip()) * 1024
        return result, {"wall_ns": wall_ns, "peak_rss_bytes": peak,
                        "peak_rss_method": method if peak is not None else "unavailable"}


def accepted(result: subprocess.CompletedProcess[bytes], scope: str) -> None:
    if result.returncode != 0:
        raise RuntimeError(f"{scope} failed: {result.returncode}: {result.stderr[-3000:]!r}")


def reported_pow(stderr: bytes, profile: str) -> dict:
    if profile == "direct":
        match = re.search(rb"S31 direct proof: interaction_pow=([0-9.]+)s fri_pow=([0-9.]+)s", stderr)
        if match is None:
            raise ValueError("direct prover omitted native PoW stage report")
        return {"interaction_pow_ns": round(float(match.group(1)) * 1e9),
                "fri_pow_ns": round(float(match.group(2)) * 1e9),
                "resolution": "rounded-to-microseconds-native-log"}
    lines = [line[len(b"S31_MIXED_NATIVE_PHASE_V1 "):]
             for line in stderr.splitlines()
             if line.startswith(b"S31_MIXED_NATIVE_PHASE_V1 ")]
    if len(lines) != 1:
        raise ValueError("mixed prover omitted native PoW phase report")
    phase = json.loads(lines[0])
    if phase.get("schema") != "s31-mixed-native-phase-v1":
        raise ValueError("unexpected mixed native phase report")
    return {"interaction_pow_ns": phase["interaction_pow_ns"],
            "fri_pow_ns": phase["fri_pow_ns"],
            "resolution": "native-nanosecond-timer"}


def changed_statement(raw_source: bytes, statement: bytes) -> bytes:
    source = json.loads(raw_source)
    value = json.loads(statement)
    result = value["leaves"][-1]["words"]
    if len(result) != 4:
        raise ValueError("expected four-word record result")
    result[0] = (result[0] + 1) % design.P
    changed = design.canonical(value)
    semantic = {**source, "version": 1}
    binding = semantic.pop("public_abi")
    original_words = decode_public_statement(semantic, binding, statement)
    altered_words = decode_public_statement(semantic, binding, changed)
    if original_words[:4] != altered_words[:4] or original_words[4] == altered_words[4] or original_words[5:] != altered_words[5:]:
        raise ValueError("mutation did not change only one valid result word")
    return changed


def binary_paths(case_dir: Path, case: str, profile: str) -> dict[str, Path]:
    name = f"s31-{design.name(case)}"
    if profile == "mixed":
        prefix = case_dir / "mixed-package/bin" / f"{name}-mixed-general-"
        return {role: Path(f"{prefix}{suffix}") for role, suffix in (
            ("prover", "prover"), ("verifier", "native-verifier"),
            ("manifest", "manifest"))}
    bin_dir = case_dir / "direct-package/bin"
    return {"prover": bin_dir / f"{name}-prover",
            "verifier": bin_dir / f"{name}-native-verifier",
            "key": case_dir / "direct-package/verification-key.json"}


def build(out: Path, frozen: dict) -> dict:
    builds = {}
    for case in protocol.CASES:
        _, calls, _ = design.spec(case)
        case_dir = out / case
        case_dir.mkdir(parents=True)
        raw_source = design.source(case)
        source_path = case_dir / "source.s31.json"
        source_path.write_bytes(raw_source)
        if design.digest(raw_source) != frozen["roster"][case]["source_sha256"]:
            raise ValueError("source differs from freeze")
        direct_package = case_dir / "direct-package"
        direct_build, direct_time = process([
            sys.executable, "-B", "-c",
            "import sys; from pathlib import Path; sys.path.insert(0, sys.argv[1]); "
            "import s31; s31.build(Path(sys.argv[2]), Path(sys.argv[3]), 'direct-gate')",
            str(protocol.S31 / "python"), str(source_path), str(direct_package)],
            timeout_seconds=600)
        (case_dir / "direct-build.stdout").write_bytes(direct_build.stdout)
        (case_dir / "direct-build.stderr").write_bytes(direct_build.stderr)
        accepted(direct_build, f"{case} direct package build")
        direct_wall_ns = direct_time["wall_ns"]
        mixed_package = case_dir / "mixed-package"
        result, timing = process([
            "zig", "build", "--build-file", str(protocol.S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=2",
            "-Ds31-lowering=direct-mixed-general", f"-Ds31-source={source_path}",
            f"-Ds31-name={design.name(case)}", "-j1", "--prefix", str(mixed_package)],
            timeout_seconds=600)
        (case_dir / "mixed-build.stdout").write_bytes(result.stdout)
        (case_dir / "mixed-build.stderr").write_bytes(result.stderr)
        accepted(result, f"{case} mixed build")
        direct = binary_paths(case_dir, case, "direct")
        mixed = binary_paths(case_dir, case, "mixed")
        for path in (*direct.values(), *mixed.values()):
            if not path.is_file():
                raise ValueError(f"missing source-pinned binary or key: {path}")
        manifest_result, _ = process([str(mixed["manifest"])])
        accepted(manifest_result, f"{case} mixed manifest")
        manifest = json.loads(manifest_result.stdout)
        direct_manifest = json.loads((direct_package / "manifest.json").read_bytes())
        direct_cost = json.loads((direct_package / "cost-report.json").read_bytes())
        if (manifest["source_sha256"] != design.digest(raw_source) or
                direct_manifest["program_sha256"] != design.digest(raw_source) or
                direct_manifest["lowering"] != "direct-gate" or
                direct_cost["profile"] != "direct-m31-v4" or
                manifest["call_count"] != calls):
            raise ValueError("lowering package is not bound to frozen source")
        builds[case] = {
            "direct_build_wall_ns": direct_wall_ns,
            "mixed_build_wall_ns": timing["wall_ns"],
            "direct_cost": {key: direct_cost[key] for key in
                            ("profile", "raw", "padded", "trace_log_size", "preprocessed_cells", "fri")},
            "mixed_geometry": {key: manifest[key] for key in
                               ("call_count", "slot_count", "tree_columns", "total_constraints")},
            "mixed_component_manifest": manifest,
            "binary_sha256": {profile: {role: design.digest(path.read_bytes())
                                        for role, path in binary_paths(case_dir, case, profile).items()}
                              for profile in ("direct", "mixed")},
            "direct_package_manifest_sha256": design.digest(
                (direct_package / "manifest.json").read_bytes()),
            "mixed_manifest_sha256": design.digest(manifest_result.stdout),
        }
    return builds


def trial(out: Path, case: str, index: int, profile: str, expected: dict,
          expected_binaries: dict[str, str]) -> dict:
    case_dir = out / case
    paths = binary_paths(case_dir, case, profile)
    if {role: design.digest(path.read_bytes()) for role, path in paths.items()} != expected_binaries:
        raise ValueError("source-pinned prover, verifier, or key changed before trial")
    source = design.source(case)
    assignment = design.assignment(case, index)
    statement = statement_from_assignment(json.loads(source), json.loads(assignment))
    if (design.digest(assignment) != expected["assignment_sha256"] or
            design.digest(statement) != expected["statement_sha256"]):
        raise ValueError("claim differs from prospective freeze")
    work = case_dir / f"a{index:03d}-{profile}"
    work.mkdir()
    assignment_path = work / "assignment.json"
    statement_path = work / "statement.json"
    changed_path = work / "changed.json"
    proof_path = work / "proof.bin"
    assignment_path.write_bytes(assignment)
    statement_path.write_bytes(statement)
    changed_path.write_bytes(changed_statement(source, statement))
    if profile == "direct":
        prove_command = [str(paths["prover"]), "prove-for-external-verification",
                         str(assignment_path), str(proof_path)]
        verify_command = [str(paths["verifier"]), str(proof_path),
                          str(statement_path), str(paths["key"])]
        wrong_command = [str(paths["verifier"]), str(proof_path),
                         str(changed_path), str(paths["key"])]
    else:
        emitted_path = work / "emitted.json"
        prove_command = [str(paths["prover"]), str(assignment_path),
                         str(proof_path), str(emitted_path), str(statement_path)]
        verify_command = [str(paths["verifier"]), str(proof_path), str(statement_path)]
        wrong_command = [str(paths["verifier"]), str(proof_path), str(changed_path)]
    proved, prove = process(prove_command, measure=True,
                            mixed_phase_timing=profile == "mixed")
    accepted(proved, f"{case}/{index} {profile} prover")
    pow_stages = reported_pow(proved.stderr, profile)
    if not proof_path.is_file() or (profile == "mixed" and emitted_path.read_bytes() != statement):
        raise ValueError("prover omitted proof or emitted different public statement")
    verified, verify = process(verify_command, measure=True)
    accepted(verified, f"{case}/{index} {profile} native verifier")
    changed, _ = process(wrong_command)
    expected_rejection = (b"error: InvalidInteractionNonce" if profile == "direct"
                          else b"error: InvalidMixedInteractionNonce")
    if changed.returncode <= 0 or changed.stderr.strip() != expected_rejection:
        raise ValueError("native verifier did not reject the changed result at the proof layer")
    total_wall = prove["wall_ns"] + verify["wall_ns"]
    pow_total = pow_stages["interaction_pow_ns"] + pow_stages["fri_pow_ns"]
    if pow_total > total_wall:
        raise ValueError("native reported PoW exceeds first-verified process wall")
    return {"case": case, "index": index, "profile": profile,
            "assignment_sha256": design.digest(assignment),
            "statement_sha256": design.digest(statement),
            "changed_statement_sha256": design.digest(changed_path.read_bytes()),
            "proof_sha256": design.digest(proof_path.read_bytes()),
            "proof_bytes": proof_path.stat().st_size,
            "prover": prove, "verifier": verify,
            "first_verified_wall_ns": total_wall,
            "reported_pow": pow_stages,
            "wall_after_reported_pow_ns": total_wall - pow_total,
            "honest_native_verifier_accepted": True,
            "changed_result_native_verifier_rejection": changed.stderr.decode(errors="replace").strip(),
            "proof_relative_path": proof_path.relative_to(out).as_posix(),
            "statement_relative_path": statement_path.relative_to(out).as_posix(),
            "changed_relative_path": changed_path.relative_to(out).as_posix()}


def summarize(rows: list[dict]) -> dict:
    results = {}
    for case in protocol.CASES:
        pairs = [row for row in rows if row["case"] == case and row["index"] > 0]
        if len(pairs) != protocol.SCORED * 2:
            raise ValueError("incomplete scored pairs")
        by_index = {index: {row["profile"]: row for row in pairs if row["index"] == index}
                    for index in range(1, protocol.SCORED + 1)}
        if any(set(pair) != {"direct", "mixed"} for pair in by_index.values()):
            raise ValueError("incomplete matched assignment")
        metrics = {}
        for key in ("first_verified_wall_ns", "wall_after_reported_pow_ns",
                    "prover_wall_ns", "verifier_wall_ns", "proof_bytes"):
            def read(row: dict) -> int:
                if key == "prover_wall_ns":
                    return row["prover"]["wall_ns"]
                if key == "verifier_wall_ns":
                    return row["verifier"]["wall_ns"]
                return row[key]
            direct = [read(pair["direct"]) for pair in by_index.values()]
            mixed = [read(pair["mixed"]) for pair in by_index.values()]
            ratios = [a / b for a, b in zip(direct, mixed, strict=True)]
            metrics[key] = {"direct_median": statistics.median(direct),
                            "mixed_median": statistics.median(mixed),
                            "median_paired_direct_over_mixed": statistics.median(ratios),
                            "pairs_direct_larger": sum(a > b for a, b in zip(direct, mixed, strict=True)),
                            "pairs_equal": sum(a == b for a, b in zip(direct, mixed, strict=True))}
        for key in ("prover", "verifier"):
            d = [pair["direct"][key]["peak_rss_bytes"] for pair in by_index.values()]
            m = [pair["mixed"][key]["peak_rss_bytes"] for pair in by_index.values()]
            metrics[f"{key}_peak_rss_bytes"] = {
                "direct_median": statistics.median(d) if all(v is not None for v in d) else None,
                "mixed_median": statistics.median(m) if all(v is not None for v in m) else None}
        results[case] = metrics
    return results


def run(out: Path) -> dict:
    frozen, protocol_sha = protocol.frozen()
    if RESULT.exists() or SUMMARY.exists() or out.exists():
        raise FileExistsError("prospective run already exists")
    out.mkdir(parents=True)
    try:
        return _run(out, frozen, protocol_sha)
    except (subprocess.TimeoutExpired, RuntimeError, ValueError, OSError) as exc:
        (out / "failure.json").write_bytes(design.canonical({
            "schema": "s31-paired-mixed-vs-direct-v1-failure",
            "protocol_sha256": protocol_sha,
            "error_type": type(exc).__name__,
            "error": str(exc)[:3000],
            "native_process_timeout_seconds": frozen["native_process_timeout_seconds"],
            "native_build_timeout_seconds": frozen["native_build_timeout_seconds"],
        }))
        raise


def _run(out: Path, frozen: dict, protocol_sha: str) -> dict:
    builds = build(out, frozen)
    rows = []
    for case in protocol.CASES:
        claim = frozen["roster"][case]["claims"][0]
        for profile in ("direct", "mixed"):
            rows.append(trial(out, case, 0, profile, claim,
                              builds[case]["binary_sha256"][profile]))
    for item in frozen["proof_order"]:
        case, index = item["case"], item["index"]
        claim = frozen["roster"][case]["claims"][index]
        for profile in item["order"]:
            rows.append(trial(out, case, index, profile, claim,
                              builds[case]["binary_sha256"][profile]))
    protocol.frozen()
    for case in protocol.CASES:
        case_dir = out / case
        for profile in ("direct", "mixed"):
            observed = {role: design.digest(path.read_bytes())
                        for role, path in binary_paths(case_dir, case, profile).items()}
            if observed != builds[case]["binary_sha256"][profile]:
                raise ValueError("source-pinned binary changed during run")
    result = {"schema": "s31-paired-mixed-vs-direct-v1-result",
              "protocol_sha256": protocol_sha, "builds": builds,
              "warmup_and_scored_rows": rows,
              "honest_verified": len(rows), "changed_claim_rejected": len(rows)}
    raw = design.canonical(result)
    (out / "result.json").write_bytes(raw)
    RESULT.write_bytes(raw)
    summary = {"schema": "s31-paired-mixed-vs-direct-v1-summary",
               "protocol_sha256": protocol_sha, "result_sha256": design.digest(raw),
               "scored_pairs_per_source": protocol.SCORED,
               "measurements": summarize(rows)}
    SUMMARY.write_bytes(design.canonical(summary))
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    print(json.dumps(run(args.out.resolve()), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
