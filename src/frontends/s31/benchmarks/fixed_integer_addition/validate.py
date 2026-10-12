#!/usr/bin/env python3
"""Gate paired checked-addition measurements on current source, host, and raw evidence.

This is an evidence consistency check. It does not replay a native verifier or
predict cost on another program, compiler revision, or host.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import statistics
import sys
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

import s31


LOWERINGS = {"direct-gate": "direct-m31-v4",
             "sparse-wide-gate": "sparse-wide-v5"}
PROFILE_FIELDS = (
    "profile", "visible_fri", "raw", "padded", "preprocessed_cells",
    "proof_bytes_per_assignment", "median_proof_bytes",
    "wall_prove_seconds_per_assignment", "median_wall_prove_seconds",
    "median_prove_excluding_pow_seconds", "median_native_verify_seconds",
    "native_verifier_accepted_all", "changed_public_statement_rejected_all",
    "independent_value_oracle_statuses",
)


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError(message)


def load(path: Path) -> dict:
    value = json.loads(path.read_text())
    require(isinstance(value, dict), f"{path}: expected a JSON object")
    return value


def positive(value: object) -> bool:
    return type(value) in (int, float) and math.isfinite(value) and value > 0


def host_identity() -> dict:
    """Bind local measurements to a host instance without publishing its name."""
    node = platform.node()
    require(bool(node), "host identity unavailable")
    return {"host_id_sha256": hashlib.sha256(node.encode()).hexdigest(),
            "platform": platform.platform(), "machine": platform.machine(),
            "python": platform.python_version(),
            "zig": s31.invoke("zig", "version").strip()}


def validate(output: Path) -> dict:
    output = output.resolve()
    summary = load(output / "summary.json")
    tune = load(output / "tune" / "tune-report.json")
    kind, count = summary.get("kind"), summary.get("count")
    require(summary.get("schema") == "s31-fixed-addition-paired-v2",
            "paired addition summary has an unsupported schema")
    require(kind in {f"{sign}{width}" for sign in ("u", "i")
                     for width in (8, 16, 32, 64, 128)}, "invalid integer kind")
    require(type(count) is int and 5 <= count <= 256, "invalid witness count")
    require(tune.get("schema") == "s31-tune-v1", "raw tune report missing or invalid")
    compiler = s31.compiler_fingerprint()
    require(summary.get("compiler_sha256") == compiler,
            "paired report uses a stale compiler fingerprint")
    host = host_identity()
    require(summary.get("host") == host, "paired report came from another host or toolchain")
    require(tune.get("host") == {key: value for key, value in host.items()
                                   if key != "host_id_sha256"},
            "raw tune report host/toolchain differs from paired summary")

    source = output / f"{kind}_checked_add.s31"
    require(Path(tune.get("source", "")).resolve() == source,
            "raw tune source path differs from paired source")
    source_sha = s31.file_hash(source)
    require(summary.get("source_sha256") == source_sha,
            "paired source bytes differ from report")
    for key in ("program_sha256", "canonical_ir_sha256", "assignment_sha256",
                "same_visible_fri_settings"):
        require(summary.get(key) == tune.get(key), f"paired {key} differs from raw tune")
    require(tune["same_visible_fri_settings"] is True,
            "profiles use different visible FRI settings")
    require(tune.get("distinct_assignment_count") == count and
            tune.get("distinct_assignments") is True,
            "raw tune has missing or duplicate assignments")
    assignments = [output / "assignments" / f"{index:03d}.json"
                   for index in range(count)]
    require(set((output / "assignments").glob("*.json")) == set(assignments),
            "assignment file set differs from declared corpus")
    hashes = [s31.assignment_digest(path) for path in assignments]
    require(len(set(hashes)) == count and tune.get("assignment_sha256") == hashes,
            "assignment values differ from raw tune hashes")
    require(tune.get("warmup_assignment_sha256") == hashes[0],
            "warmup assignment differs from the first measured assignment")

    profiles = tune.get("profiles")
    require(isinstance(profiles, dict) and set(profiles) == set(LOWERINGS) and
            isinstance(summary.get("profiles"), dict) and
            set(summary["profiles"]) == set(LOWERINGS),
            "paired report does not contain exactly the two requested profiles")
    fri = set()
    for lowering, expected_profile in LOWERINGS.items():
        profile = profiles[lowering]
        require(isinstance(profile, dict) and all(field in profile for field in PROFILE_FIELDS) and
                summary["profiles"][lowering] ==
                {field: profile[field] for field in PROFILE_FIELDS},
                f"{lowering}: paired metrics differ from raw tune")
        require(profile.get("profile") == expected_profile,
                f"{lowering}: unexpected native profile")
        require(profile.get("native_verifier_accepted_all") is True and
                profile.get("changed_public_statement_rejected_all") is True and
                profile.get("independent_value_oracle_statuses") == ["passed"] * count,
                f"{lowering}: native verifier or independent oracle control failed")
        sizes = profile.get("proof_bytes_per_assignment")
        walls = profile.get("wall_prove_seconds_per_assignment")
        require(isinstance(sizes, list) and len(sizes) == count and
                all(type(size) is int and size > 0 for size in sizes) and
                isinstance(walls, list) and len(walls) == count and
                all(positive(wall) for wall in walls),
                f"{lowering}: invalid per-assignment cost values")
        require(profile.get("median_proof_bytes") == statistics.median(sizes) and
                profile.get("median_wall_prove_seconds") == statistics.median(walls) and
                positive(profile.get("median_native_verify_seconds")),
                f"{lowering}: invalid median cost values")
        non_pow = profile.get("median_prove_excluding_pow_seconds")
        require(non_pow is None or positive(non_pow),
                f"{lowering}: invalid measured non-PoW median")
        require(type(profile.get("preprocessed_cells")) is int and
                profile["preprocessed_cells"] > 0,
                f"{lowering}: invalid preprocessing size")
        fri.add(json.dumps(profile["visible_fri"], sort_keys=True))

        package = output / "tune" / "packages" / lowering
        manifest = load(package / "manifest.json")
        for key, value in (("compiler_sha256", compiler),
                           ("source_text_sha256", source_sha),
                           ("program_sha256", tune["program_sha256"]),
                           ("canonical_ir_sha256", tune["canonical_ir_sha256"]),
                           ("lowering", lowering)):
            require(manifest.get(key) == value,
                    f"{lowering}: package manifest {key} differs from paired evidence")
        verify_times = []
        non_pow_times = []
        for index in range(count):
            trial_dir = output / "tune" / "runs" / lowering / f"{index:03d}"
            trial = load(trial_dir / "trial-report.json")
            proof = trial_dir / "proof.bin"
            require(trial.get("schema") == "s31-trial-v1" and
                    Path(trial.get("assignment", "")).resolve() == assignments[index] and
                    trial.get("program_sha256") == tune["program_sha256"] and
                    trial.get("canonical_ir_sha256") == tune["canonical_ir_sha256"] and
                    trial.get("lowering") == lowering and
                    trial.get("profile") == expected_profile and
                    trial.get("visible_fri") == profile["visible_fri"] and
                    trial.get("raw") == profile["raw"] and
                    trial.get("padded") == profile["padded"] and
                    trial.get("preprocessed_cells") == profile["preprocessed_cells"] and
                    Path(trial.get("package", "")).resolve() == package,
                    f"{lowering} trial {index}: identity differs from paired evidence")
            require(trial.get("proof_bytes") == sizes[index] == proof.stat().st_size and
                    trial.get("proof_sha256") == s31.file_hash(proof) and
                    trial.get("prove_seconds") == walls[index] and
                    trial.get("native_verifier_accepted") is True and
                    bool(trial.get("changed_public_statement_rejected")) and
                    trial.get("independent_value_oracle", {}).get("status") == "passed",
                    f"{lowering} trial {index}: proof, timing, or control differs")
            require(positive(trial.get("verify_seconds")),
                    f"{lowering} trial {index}: invalid native verifier time")
            verify_times.append(trial["verify_seconds"])
            stages = trial.get("prover_stages")
            if isinstance(stages, dict) and "prove_excluding_pow_seconds" in stages:
                non_pow_times.append(stages["prove_excluding_pow_seconds"])
        require(profile["median_native_verify_seconds"] == statistics.median(verify_times) and
                profile["median_prove_excluding_pow_seconds"] ==
                (statistics.median(non_pow_times) if len(non_pow_times) == count else None),
                f"{lowering}: median verifier or non-PoW time differs from raw trials")
    require(len(fri) == 1, "visible FRI settings differ between profiles")
    return {"schema": "s31-fixed-addition-evidence-gate-v1",
            "status": "current-host-and-compiler-evidence-consistent",
            "kind": kind, "count": count, "compiler_sha256": compiler,
            "host_id_sha256": host["host_id_sha256"],
            "limitations": "Archived report and artifact consistency only; native verification was recorded by the original trial and is not replayed. No unseen-program or cross-host cost prediction."}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("measurement_dir", type=Path)
    args = parser.parse_args()
    print(json.dumps(validate(args.measurement_dir), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
