#!/usr/bin/env python3
"""Post-study, source-bound mixed prover stage diagnostic for record ABI v2.

This does not amend the frozen paired corpus. It measures one complete prover
process and one separate native verifier process. The mixed engine keeps its
preprocessing, interaction work, FRI and PoW inside one opaque native call.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import time
from pathlib import Path

SCHEMA = "s31-mixed-stage-diagnostic-v1"
PROVER_SCHEMA = "s31-mixed-general-prover-stages-v1"
PREFIX = "S31_MIXED_STAGE_V1 "
STAGES = {
    "profile_rebuild_ns", "semantic_evaluation_ns", "topology_compile_ns",
    "witness_compile_ns", "native_prove_including_setup_ns",
    "envelope_and_serialization_ns", "package_total_ns",
}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs: list[tuple[str, object]]) -> dict:
    value = {}
    for key, item in pairs:
        if key in value:
            raise ValueError(f"duplicate JSON field: {key}")
        value[key] = item
    return value


def invoke(argv: list[str]) -> tuple[subprocess.CompletedProcess[bytes], int]:
    start = time.perf_counter_ns()
    result = subprocess.run(argv, capture_output=True, check=False)
    elapsed = time.perf_counter_ns() - start
    if result.returncode:
        raise RuntimeError(f"command failed ({result.returncode}): {argv!r}\n"
                           f"{result.stderr.decode(errors='replace')}")
    return result, elapsed


def parse_prover_stage(stderr: bytes, manifest: dict, proof: bytes,
                       statement: bytes) -> dict:
    lines = [line[len(PREFIX):] for line in stderr.decode("utf-8").splitlines()
             if line.startswith(PREFIX)]
    if len(lines) != 1:
        raise ValueError("expected exactly one mixed prover stage line")
    report = json.loads(lines[0], object_pairs_hook=unique_object)
    if set(report) != {"schema", "source_sha256", "registry_manifest_sha256",
                       "circuit_identity_sha256", "proof_bytes", "statement_bytes",
                       "stages_ns", "external_native_verification_ns"}:
        raise ValueError("mixed prover stage schema has missing or unknown fields")
    if (report["schema"] != PROVER_SCHEMA or
            report["external_native_verification_ns"] is not None or
            any(report[field] != manifest[field] for field in
                ("source_sha256", "registry_manifest_sha256",
                 "circuit_identity_sha256")) or
            type(report["proof_bytes"]) is not int or
            report["proof_bytes"] <= 0 or report["proof_bytes"] != len(proof) or
            type(report["statement_bytes"]) is not int or
            report["statement_bytes"] != len(statement)):
        raise ValueError("mixed prover stages differ from source or saved artifacts")
    stages = report["stages_ns"]
    if (type(stages) is not dict or set(stages) != STAGES or
            any(type(value) is not int or value < 0 for value in stages.values()) or
            stages["package_total_ns"] <= 0 or
            stages["package_total_ns"] != sum(value for key, value in stages.items()
                                               if key != "package_total_ns")):
        raise ValueError("mixed prover stage intervals are malformed")
    return report


def measure(prover: Path, verifier: Path, inspector: Path, assignment: Path,
            typed_statement: Path, out: Path) -> dict:
    # Bare relative names are resolved through PATH by subprocess, but
    # Path.read_bytes() opens them in cwd. Use the same absolute file for both
    # execution and the evidence digest.
    prover, verifier, inspector = (path.resolve(strict=True) for path in
                                   (prover, verifier, inspector))
    binaries = {name: digest(path.read_bytes()) for name, path in
                (("prover", prover), ("verifier", verifier), ("inspector", inspector))}
    supplied = typed_statement.read_bytes()
    assignment_bytes = assignment.read_bytes()
    inspector_result, _ = invoke([str(inspector)])
    manifest = json.loads(inspector_result.stdout, object_pairs_hook=unique_object)
    if (manifest.get("schema") != "s31-mixed-component-inspection-general-v3" or
            any(type(manifest.get(field)) is not str or len(manifest[field]) != 64 or
                any(character not in "0123456789abcdef" for character in manifest[field])
                for field in ("source_sha256", "registry_manifest_sha256",
                              "circuit_identity_sha256"))):
        raise ValueError("source-embedded mixed inspector has an invalid identity")
    out.mkdir(parents=True, exist_ok=False)
    proof_path = out / "proof.bin"
    statement_path = out / "statement.json"
    prover_result, prover_wall = invoke([str(prover), str(assignment),
                                        str(proof_path), str(statement_path),
                                        str(typed_statement)])
    proof = proof_path.read_bytes()
    statement = statement_path.read_bytes()
    if statement != supplied:
        raise ValueError("mixed prover changed the canonical typed statement")
    stages = parse_prover_stage(prover_result.stderr, manifest, proof, statement)
    if stages["stages_ns"]["package_total_ns"] > prover_wall:
        raise ValueError("reported internal package time exceeds measured prover process wall")
    verifier_result, verifier_wall = invoke([str(verifier), str(proof_path),
                                            str(statement_path)])
    if (proof_path.read_bytes() != proof or statement_path.read_bytes() != statement or
            assignment.read_bytes() != assignment_bytes or
            typed_statement.read_bytes() != supplied):
        raise ValueError("mixed diagnostic input or artifact changed during verification")
    if any(digest(path.read_bytes()) != binaries[name] for name, path in
           (("prover", prover), ("verifier", verifier), ("inspector", inspector))):
        raise ValueError("a mixed executable changed during the diagnostic")
    (out / "prover.stdout").write_bytes(prover_result.stdout)
    (out / "prover.stderr").write_bytes(prover_result.stderr)
    (out / "verifier.stdout").write_bytes(verifier_result.stdout)
    (out / "verifier.stderr").write_bytes(verifier_result.stderr)
    (out / "inspector.stdout").write_bytes(inspector_result.stdout)
    (out / "inspector.stderr").write_bytes(inspector_result.stderr)
    report = {
        "schema": SCHEMA,
        "external_native_verification_accepted": True,
        "source_sha256": manifest["source_sha256"],
        "registry_manifest_sha256": manifest["registry_manifest_sha256"],
        "circuit_identity_sha256": manifest["circuit_identity_sha256"],
        "binary_sha256": binaries,
        "assignment_sha256": digest(assignment_bytes),
        "typed_statement_sha256": digest(supplied),
        "proof_sha256": digest(proof),
        "proof_bytes": len(proof),
        "prover_process_wall_ns": prover_wall,
        "external_verifier_process_wall_ns": verifier_wall,
        "first_verified_process_wall_ns": prover_wall + verifier_wall,
        "prover_internal_stages_ns": stages["stages_ns"],
        "engine_setup_preprocessing_ns": None,
        "engine_pow_ns": None,
        "raw_log_sha256": {
            path.name: digest(path.read_bytes()) for path in (
                out / "prover.stdout", out / "prover.stderr",
                out / "verifier.stdout", out / "verifier.stderr",
                out / "inspector.stdout", out / "inspector.stderr")
        },
    }
    (out / "report.json").write_text(json.dumps(report, sort_keys=True,
                                                separators=(",", ":")) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    for option in ("prover", "verifier", "inspector", "assignment",
                   "typed-statement", "out"):
        parser.add_argument("--" + option, required=True, type=Path)
    args = parser.parse_args()
    result = measure(args.prover, args.verifier, args.inspector,
                     args.assignment, args.typed_statement, args.out)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
