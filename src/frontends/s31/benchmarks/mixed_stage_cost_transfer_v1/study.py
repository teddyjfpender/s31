#!/usr/bin/env python3
"""Freeze-gated cross-shape mixed cost build, proof collection, and replay.

No native command runs before the separately committed protocol and freeze
anchor. The audit replays every proof and changed public claim from saved raw
artifacts, then writes the only corpus eligible for later model scoring.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone
from pathlib import Path

from cohort import (ROOT, S31, canonical, case, design, inventory, materialize,
                    sha, trial_order)
from protocol import check, path_name

sys.path.insert(0, str(S31 / "benchmarks/paired_record_v2"))
sys.path.insert(0, str(S31 / "tests/acceptance/mixed_boundary"))
from diagnose_stages_v1 import measure, parse_prover_stage, unique_object  # noqa: E402
from registry_manifest_digest import digest as registry_digest  # noqa: E402

PHASE_ANCHOR = ROOT / "design/s31/measurements/language/mixed-stage-cost-transfer-v1-phase-anchor.json"
EXCLUDED = {"phase-root.json", "audit.json", "corpus.json", "evaluation.json"}


def load_json(path: Path) -> dict:
    value = json.loads(path.read_bytes(), object_pairs_hook=unique_object)
    if type(value) is not dict:
        raise ValueError(f"expected JSON object: {path}")
    return value


def disk_guard(out: Path, minimum: int) -> None:
    locations = (out, Path(os.environ.get("ZIG_LOCAL_CACHE_DIR") or S31 / ".zig-cache"),
                 Path(os.environ.get("ZIG_GLOBAL_CACHE_DIR") or Path.home() / ".cache/zig"),
                 Path(tempfile.gettempdir()))
    devices = set()
    for path in locations:
        if not path.is_absolute():
            path = ROOT / path
        path = path.resolve()
        while not path.exists():
            path = path.parent
        if path.stat().st_dev in devices:
            continue
        devices.add(path.stat().st_dev)
        if shutil.disk_usage(path).free < minimum:
            raise ValueError(f"transfer native unit requires {minimum} free bytes on {path}")


def bins(directory: Path, name: str) -> dict[str, Path]:
    prefix = f"s31-mixed_stage_transfer_v1_{name}-mixed-general-"
    base = directory / "mixed/bin"
    return {"prover": base / (prefix + "prover"),
            "verifier": base / (prefix + "native-verifier"),
            "inspector": base / (prefix + "manifest")}


def build_command(directory: Path, name: str) -> list[str]:
    return ["zig", "build", "--build-file", str(S31 / "build.zig"), "install",
            "-Doptimize=ReleaseFast", "-Ds31-version=2",
            "-Ds31-lowering=direct-mixed-general",
            f"-Ds31-source={directory / 'source.s31.json'}",
            f"-Ds31-name=mixed_stage_transfer_v1_{name}", "-j1", "--prefix",
            str(directory / "mixed")]


def inspect(directory: Path, name: str, expected: dict) -> tuple[dict, bytes, bytes]:
    result = subprocess.run([str(bins(directory, name)["inspector"])],
                            capture_output=True, check=False)
    if result.returncode:
        raise ValueError(f"{name}: source-embedded inspector failed")
    manifest = json.loads(result.stdout, object_pairs_hook=unique_object)
    calls = manifest.get("calls")
    if (manifest.get("schema") != "s31-mixed-component-inspection-general-v3" or
            manifest.get("profile") != "experimental-direct-mixed-general" or
            manifest.get("source_sha256") != expected["source_sha256"] or
            manifest.get("call_count") != expected["call_count"] or
            manifest.get("slot_count") != expected["chip_slots"] or
            type(calls) is not list or len(calls) != expected["call_count"] or
            [call.get("rounds") for call in calls] !=
                [expected["total_rounds"] // expected["call_count"]] * expected["call_count"] or
            [call.get("constant") for call in calls] !=
                [13 + index for index in range(expected["call_count"])] or
            manifest.get("registry_manifest_sha256") != registry_digest(manifest) or
            type(manifest.get("circuit_identity_sha256")) is not str or
            len(manifest["circuit_identity_sha256"]) != 64):
        raise ValueError(f"{name}: inspector differs from frozen source and chip schedule")
    return manifest, result.stdout, result.stderr


def materialized(directory: Path, name: str, expected: dict, cfg: dict) -> None:
    shape, count = expected["shape"], expected["call_count"]
    actual = {path.name for path in directory.glob("assignment-*.json")}
    wanted = {f"assignment-{i:02d}.json" for i in range(cfg["assignments_per_program"])}
    if actual != wanted or {path.name for path in directory.glob("statement-*.json")} != \
            {f"statement-{i:02d}.json" for i in range(cfg["assignments_per_program"])}:
        raise ValueError(f"{name}: incomplete materialized case roster")
    for index in range(cfg["assignments_per_program"]):
        source_bytes, assignment, statement = case(shape, count, index, cfg)
        if ((directory / "source.s31.json").read_bytes() != source_bytes or
                (directory / f"assignment-{index:02d}.json").read_bytes() != assignment or
                (directory / f"statement-{index:02d}.json").read_bytes() != statement or
                sha(source_bytes) != expected["source_sha256"] or
                sha(assignment) != expected["assignment_sha256"][index] or
                sha(statement) != expected["typed_statement_sha256"][index]):
            raise ValueError(f"{name}/{index}: generated bytes differ from frozen inventory")


def check_build(directory: Path, name: str, expected: dict, cfg: dict) -> dict:
    materialized(directory, name, expected, cfg)
    saved = load_json(directory / "build.json")
    manifest, stdout, stderr = inspect(directory, name, expected)
    paths = bins(directory, name)
    if (set(saved) != {"schema", "source_sha256", "registry_manifest_sha256",
                       "circuit_identity_sha256", "binary_sha256", "build_command",
                       "build_start_monotonic_ns", "build_end_monotonic_ns",
                       "build_wall_ns", "build_stdout_sha256", "build_stderr_sha256",
                       "inspector_stdout_sha256", "inspector_stderr_sha256",
                       "package_reused"} or
            saved["schema"] != "s31-mixed-stage-cost-transfer-v1-build" or
            saved["source_sha256"] != expected["source_sha256"] or
            saved["registry_manifest_sha256"] != manifest["registry_manifest_sha256"] or
            saved["circuit_identity_sha256"] != manifest["circuit_identity_sha256"] or
            saved["binary_sha256"] != {key: sha(path.read_bytes())
                                        for key, path in paths.items()} or
            saved["build_command"] != build_command(directory, name) or
            type(saved["build_start_monotonic_ns"]) is not int or
            type(saved["build_end_monotonic_ns"]) is not int or
            saved["build_start_monotonic_ns"] < 0 or
            saved["build_end_monotonic_ns"] <= saved["build_start_monotonic_ns"] or
            saved["build_wall_ns"] != saved["build_end_monotonic_ns"] -
                                      saved["build_start_monotonic_ns"] or
            saved["build_stdout_sha256"] != sha((directory / "build.stdout").read_bytes()) or
            saved["build_stderr_sha256"] != sha((directory / "build.stderr").read_bytes()) or
            saved["inspector_stdout_sha256"] != sha(stdout) or
            saved["inspector_stderr_sha256"] != sha(stderr) or
            (directory / "inspector.stdout").read_bytes() != stdout or
            (directory / "inspector.stderr").read_bytes() != stderr or
            saved["package_reused"] is not False):
        raise ValueError(f"{name}: package, build endpoints, or logs differ")
    return saved


def raw_root(out: Path, protocol_sha256: str) -> dict:
    if any(path.is_symlink() for path in out.rglob("*")):
        raise ValueError("transfer raw phase cannot contain symlinks")
    files = sorted(path for path in out.rglob("*") if path.is_file() and
                   path.relative_to(out).as_posix() not in EXCLUDED)
    if not files:
        raise ValueError("transfer raw phase has no files")
    entries = [{"path": path.relative_to(out).as_posix(), "sha256": sha(path.read_bytes())}
               for path in files]
    return {"schema": "s31-mixed-stage-cost-transfer-v1-phase-root",
            "protocol_sha256": protocol_sha256, "file_count": len(entries),
            "content_root_sha256": sha(canonical(entries))}


def build(out: Path, protocol_sha256: str, anchor_commit: str) -> dict:
    out = out.resolve()
    protocol = check(protocol_sha256, anchor_commit)
    cfg = design()
    if out.exists():
        raise ValueError("fresh transfer output path required; no resume")
    disk_guard(out, protocol["minimum_available_disk_bytes_at_phase_start"])
    materialize(out, cfg)
    (out / "protocol-ref.json").write_bytes(canonical({
        "protocol_sha256": protocol_sha256, "anchor_commit": anchor_commit}))
    for name, expected in protocol["inventory"].items():
        disk_guard(out, protocol["minimum_available_disk_bytes_before_native_unit"])
        directory = out / name
        command = build_command(directory, name)
        start = time.perf_counter_ns()
        result = subprocess.run(command, cwd=ROOT, capture_output=True, check=False)
        end = time.perf_counter_ns()
        (directory / "build.stdout").write_bytes(result.stdout)
        (directory / "build.stderr").write_bytes(result.stderr)
        if result.returncode:
            raise RuntimeError(f"{name}: mixed package build failed; discard partial phase")
        manifest, stdout, stderr = inspect(directory, name, expected)
        (directory / "inspector.stdout").write_bytes(stdout)
        (directory / "inspector.stderr").write_bytes(stderr)
        saved = {"schema": "s31-mixed-stage-cost-transfer-v1-build",
                 "source_sha256": expected["source_sha256"],
                 "registry_manifest_sha256": manifest["registry_manifest_sha256"],
                 "circuit_identity_sha256": manifest["circuit_identity_sha256"],
                 "binary_sha256": {key: sha(path.read_bytes())
                                   for key, path in bins(directory, name).items()},
                 "build_command": command,
                 "build_start_monotonic_ns": start,
                 "build_end_monotonic_ns": end,
                 "build_wall_ns": end - start,
                 "build_stdout_sha256": sha(result.stdout),
                 "build_stderr_sha256": sha(result.stderr),
                 "inspector_stdout_sha256": sha(stdout),
                 "inspector_stderr_sha256": sha(stderr),
                 "package_reused": False}
        (directory / "build.json").write_bytes(canonical(saved))
    return {"sources_built": len(protocol["inventory"])}


def prove(out: Path, protocol_sha256: str, anchor_commit: str) -> dict:
    out = out.resolve()
    protocol = check(protocol_sha256, anchor_commit)
    cfg = design()
    if (not out.is_dir() or (out / "phase-root.json").exists() or
            any((out / name / "trials").exists() for name in protocol["inventory"])):
        raise ValueError("transfer proof phase is absent or already started; no resume")
    if load_json(out / "protocol-ref.json") != {
            "protocol_sha256": protocol_sha256, "anchor_commit": anchor_commit}:
        raise ValueError("transfer protocol reference differs")
    disk_guard(out, protocol["minimum_available_disk_bytes_at_phase_start"])
    for name, expected in protocol["inventory"].items():
        directory = out / name
        check_build(directory, name, expected, cfg)
        (directory / "trials").mkdir()
    for index in range(cfg["assignments_per_program"]):
        for name in trial_order(index, cfg):
            disk_guard(out, protocol["minimum_available_disk_bytes_before_native_unit"])
            directory = out / name
            paths = bins(directory, name)
            measure(paths["prover"], paths["verifier"], paths["inspector"],
                    directory / f"assignment-{index:02d}.json",
                    directory / f"statement-{index:02d}.json",
                    directory / f"trials/{index:02d}")
    root = raw_root(out, protocol_sha256)
    (out / "phase-root.json").write_bytes(canonical(root))
    return root


def changed_claim(statement: bytes, leaf_index: int) -> bytes:
    value = json.loads(statement, object_pairs_hook=unique_object)
    if (value.get("version") != 2 or type(value.get("leaves")) is not list or
            len(value["leaves"]) != 2 or
            type(value["leaves"][leaf_index].get("words")) is not list or
            len(value["leaves"][leaf_index]["words"]) != 4):
        raise ValueError("transfer typed statement has wrong record claim shape")
    value["leaves"][leaf_index]["words"][0] = \
        (value["leaves"][leaf_index]["words"][0] + 1) % ((1 << 31) - 1)
    return canonical(value)


def phase_anchor(protocol_sha256: str, root_sha256: str, anchor_commit: str,
                 phase_commit: str) -> dict:
    if len(phase_commit) != 40 or any(char not in "0123456789abcdef" for char in phase_commit):
        raise ValueError("full externally recorded phase anchor commit required")
    if subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                       anchor_commit, phase_commit], check=False).returncode or \
            subprocess.run(["git", "-C", str(ROOT), "merge-base", "--is-ancestor",
                            phase_commit, "HEAD"], check=False).returncode:
        raise ValueError("transfer phase anchor must descend from freeze and precede audit")
    saved = subprocess.check_output(["git", "-C", str(ROOT), "show",
                                     f"{phase_commit}:{path_name(PHASE_ANCHOR)}"])
    if saved != PHASE_ANCHOR.read_bytes():
        raise ValueError("phase anchor differs from committed bytes")
    value = load_json(PHASE_ANCHOR)
    try:
        timestamp = datetime.fromisoformat(value["recorded_at_utc"].replace("Z", "+00:00"))
    except (KeyError, ValueError, TypeError) as exc:
        raise ValueError("phase anchor requires UTC timestamp") from exc
    if (set(value) != {"schema", "protocol_sha256", "phase_root_sha256",
                       "recorded_at_utc"} or
            value["schema"] != "s31-mixed-stage-cost-transfer-v1-phase-anchor" or
            value["protocol_sha256"] != protocol_sha256 or
            value["phase_root_sha256"] != root_sha256 or
            timestamp.utcoffset() is None or timestamp.utcoffset().total_seconds() != 0 or
            timestamp > datetime.now(timezone.utc)):
        raise ValueError("phase anchor differs from raw transfer phase")
    return value


def audit(out: Path, protocol_sha256: str, anchor_commit: str,
          root_sha256: str, phase_commit: str, *, write: bool = True) -> dict:
    out = out.resolve()
    protocol = check(protocol_sha256, anchor_commit)
    cfg = design()
    if write and ((out / "audit.json").exists() or (out / "corpus.json").exists()):
        raise ValueError("transfer audit already exists; never overwrite")
    if not write and (not (out / "audit.json").is_file() or
                      not (out / "corpus.json").is_file()):
        raise ValueError("transfer report check requires saved audit and corpus")
    saved_root = (out / "phase-root.json").read_bytes()
    if saved_root != canonical(raw_root(out, protocol_sha256)) or \
            sha(saved_root) != root_sha256:
        raise ValueError("raw transfer phase differs from anchored digest")
    phase_anchor(protocol_sha256, root_sha256, anchor_commit, phase_commit)
    if load_json(out / "protocol-ref.json") != {
            "protocol_sha256": protocol_sha256, "anchor_commit": anchor_commit}:
        raise ValueError("transfer protocol reference differs")
    records = []
    observed_order: list[tuple[str, int, int, int]] = []
    for name, expected in protocol["inventory"].items():
        directory = out / name
        build_record = check_build(directory, name, expected, cfg)
        trials_dir = directory / "trials"
        if {path.name for path in trials_dir.iterdir()} != {
                f"{index:02d}" for index in range(cfg["assignments_per_program"])}:
            raise ValueError(f"{name}: incomplete trial roster")
        paths = bins(directory, name)
        manifest = load_json(directory / "inspector.stdout")
        reports = []
        for index in range(cfg["assignments_per_program"]):
            disk_guard(out, protocol["minimum_available_disk_bytes_before_native_unit"])
            trial = trials_dir / f"{index:02d}"
            report = load_json(trial / "report.json")
            proof = (trial / "proof.bin").read_bytes()
            statement = (trial / "statement.json").read_bytes()
            supplied = (directory / f"statement-{index:02d}.json").read_bytes()
            if (report.get("schema") != "s31-mixed-stage-diagnostic-v1" or
                    report.get("external_native_verification_accepted") is not True or
                    report.get("source_sha256") != expected["source_sha256"] or
                    report.get("registry_manifest_sha256") !=
                        build_record["registry_manifest_sha256"] or
                    report.get("circuit_identity_sha256") !=
                        build_record["circuit_identity_sha256"] or
                    report.get("binary_sha256") != build_record["binary_sha256"] or
                    report.get("assignment_sha256") != expected["assignment_sha256"][index] or
                    report.get("typed_statement_sha256") !=
                        expected["typed_statement_sha256"][index] or
                    report.get("proof_sha256") != sha(proof) or
                    report.get("proof_bytes") != len(proof) or
                    statement != supplied or
                    report.get("raw_log_sha256") != {
                        filename: sha((trial / filename).read_bytes()) for filename in (
                            "prover.stdout", "prover.stderr", "verifier.stdout",
                            "verifier.stderr", "inspector.stdout", "inspector.stderr")}
                    or (trial / "inspector.stdout").read_bytes() !=
                        (directory / "inspector.stdout").read_bytes() or
                    (trial / "inspector.stderr").read_bytes() !=
                        (directory / "inspector.stderr").read_bytes()):
                raise ValueError(f"{name}/{index}: raw diagnostic differs from frozen evidence")
            stage = parse_prover_stage((trial / "prover.stderr").read_bytes(),
                                       manifest, proof, statement)
            if stage["stages_ns"] != report.get("prover_internal_stages_ns"):
                raise ValueError(f"{name}/{index}: stage line differs from report")
            prover_wall = report.get("prover_process_wall_ns")
            verifier_wall = report.get("external_verifier_process_wall_ns")
            times = report.get("process_monotonic_ns")
            if (type(times) is not dict or
                    set(times) != {"prover_start", "prover_end", "verifier_start",
                                   "verifier_end"} or
                    any(type(value) is not int or value < 0 for value in times.values()) or
                    not times["prover_start"] < times["prover_end"] <=
                        times["verifier_start"] < times["verifier_end"] or
                    prover_wall != times["prover_end"] - times["prover_start"] or
                    verifier_wall != times["verifier_end"] - times["verifier_start"] or
                    report.get("first_verified_process_wall_ns") !=
                        prover_wall + verifier_wall or
                    stage["stages_ns"]["package_total_ns"] > prover_wall or
                    report.get("engine_setup_preprocessing_ns", "missing") is not None or
                    report.get("engine_pow_ns", "missing") is not None):
                raise ValueError(f"{name}/{index}: process and package timing differs")
            accepted = subprocess.run([str(paths["verifier"]), str(trial / "proof.bin"),
                                       str(trial / "statement.json")],
                                      capture_output=True, check=False)
            if accepted.returncode:
                raise ValueError(f"{name}/{index}: native proof replay rejected")
            for leaf in (0, 1):
                with tempfile.TemporaryDirectory() as temporary:
                    changed = Path(temporary) / "changed.json"
                    changed.write_bytes(changed_claim(statement, leaf))
                    rejected = subprocess.run([str(paths["verifier"]),
                                               str(trial / "proof.bin"), str(changed)],
                                              capture_output=True, check=False)
                    if rejected.returncode == 0:
                        raise ValueError(f"{name}/{index}: changed public claim accepted")
            if (sha((trial / "proof.bin").read_bytes()) != report["proof_sha256"] or
                    {key: sha(path.read_bytes()) for key, path in paths.items()} !=
                        build_record["binary_sha256"]):
                raise ValueError(f"{name}/{index}: verifier changed proof or executable")
            observed_order.append((name, index, times["prover_start"],
                                   times["verifier_end"]))
            reports.append(report)
        records.append({"name": name, "shape": expected["shape"],
                        "call_count": expected["call_count"],
                        "source_sha256": expected["source_sha256"],
                        "build_wall_ns": build_record["build_wall_ns"],
                        "trials": reports})
    expected_order = [(name, index)
                      for index in range(cfg["assignments_per_program"])
                      for name in trial_order(index, cfg)]
    observed_order.sort(key=lambda item: item[2])
    if ([(name, index) for name, index, _, _ in observed_order] != expected_order or
            any(left[3] > right[2] for left, right in
                zip(observed_order, observed_order[1:]))):
        raise ValueError("transfer trial timing differs from predeclared interleaving")
    if saved_root != canonical(raw_root(out, protocol_sha256)):
        raise ValueError("raw transfer phase changed during native audit")
    corpus = {"schema": "s31-mixed-stage-cost-transfer-v1-audited-corpus",
              "protocol_sha256": protocol_sha256,
              "phase_root_sha256": root_sha256,
              "host": protocol["host"],
              "compiler_sha256": protocol["compiler_sha256"],
              "engine_gitlink_commit": protocol["engine_gitlink_commit"],
              "inventory_sha256": protocol["inventory_sha256"],
              "records": records}
    corpus_bytes = canonical(corpus)
    audit_record = {"schema": "s31-mixed-stage-cost-transfer-v1-audit",
                    "protocol_sha256": protocol_sha256,
                    "phase_root_sha256": root_sha256,
                    "corpus_sha256": sha(corpus_bytes),
                    "native_verified_proofs": len(records) * cfg["assignments_per_program"],
                    "changed_input_and_result_rejected": True,
                    "raw_build_and_process_endpoints_replayed": True,
                    "source_assignment_statement_manifest_and_binary_hashes_replayed": True}
    if write:
        (out / "corpus.json").write_bytes(corpus_bytes)
        (out / "audit.json").write_bytes(canonical(audit_record))
    elif ((out / "corpus.json").read_bytes() != corpus_bytes or
          (out / "audit.json").read_bytes() != canonical(audit_record)):
        raise ValueError("saved transfer audit or corpus differs from raw native replay")
    return audit_record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("build", "prove", "audit"))
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--expected-protocol-sha256", required=True)
    parser.add_argument("--protocol-anchor-commit", required=True)
    parser.add_argument("--expected-phase-root-sha256")
    parser.add_argument("--phase-anchor-commit")
    args = parser.parse_args()
    common = (args.out, args.expected_protocol_sha256, args.protocol_anchor_commit)
    if args.command == "audit":
        if not args.expected_phase_root_sha256 or not args.phase_anchor_commit:
            parser.error("audit requires anchored phase root SHA-256 and commit")
        result = audit(*common, args.expected_phase_root_sha256,
                       args.phase_anchor_commit)
    else:
        result = build(*common) if args.command == "build" else prove(*common)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
