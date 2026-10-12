"""Balanced measurement order and exact native stage accounting."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "benchmarks" / "fixed_integer_cost"))

import evidence
import paired_tune
from runtime.cost_model import observed_cost_model


def trial_row() -> dict:
    return {
        "native_verifier_accepted": True,
        "changed_public_statement_rejected": "public_outputs.out[0]",
        "independent_value_oracle": {"status": "passed"},
        "proof_bytes": 100, "prove_seconds": .020, "verify_seconds": .004,
        "prover_stages": {
            "witness_seconds": .001, "setup_seconds": .002,
            "prove_seconds": .010, "interaction_pow_seconds": .002,
            "fri_pow_seconds": .003, "prove_excluding_pow_seconds": .005,
            "runtime_other_seconds": .001,
            "total_through_verification_seconds": .014,
        },
    }


def put(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True))


def evidence_fixture(root: Path) -> tuple[dict, dict]:
    compiler = "c" * 64
    host = {"host_id_sha256": "h" * 64, "platform": "test", "machine": "cpu",
            "python": "3.14", "zig": "0.15.2"}
    source = root / "u8_checked_add.s31"
    source.write_text("use std@1;\ncircuit u8_checked_add(private a: u8, private b: u8) "
                      "-> public u8 { std::int::add_checked(a, b) }\n")
    source_hash = evidence.s31.file_hash(source)
    assignments = []
    oracle = {"version": 1}
    for index in range(5):
        assignment = {"public_inputs": {}, "private_inputs": {"a": [index], "b": [1]},
                      "public_outputs": {"out": [index + 1]}}
        path = root / "assignments" / f"{index:03d}.json"
        put(path, assignment)
        assignments.append(evidence.s31.assignment_digest(path))
    profiles = {}
    summary_profiles = {}
    for lowering, profile_name in evidence.LOWERINGS.items():
        package = root / "tune" / "packages" / lowering
        put(package / "manifest.json", {
            "compiler_sha256": compiler, "source_text_sha256": source_hash,
            "program_sha256": "p" * 64, "canonical_ir_sha256": "r" * 64,
            "lowering": lowering,
        })
        trials = []
        for index in range(5):
            trial_dir = root / "tune" / "runs" / lowering / f"{index:03d}"
            trial_dir.mkdir(parents=True)
            proof = trial_dir / "proof.bin"
            proof.write_bytes(b"proof")
            assignment_path = root / "assignments" / f"{index:03d}.json"
            claim = json.loads(assignment_path.read_text())
            statement = {"public_inputs": {}, "public_outputs": claim["public_outputs"]}
            changed = {"public_inputs": {}, "public_outputs": {"out": [index + 2]}}
            put(trial_dir / "statement.json", statement)
            put(trial_dir / "changed-statement.json", changed)
            row = {**trial_row(), "schema": "s31-trial-v1",
                   "assignment": str(assignment_path), "package": str(package),
                   "lowering": lowering, "profile": profile_name,
                   "visible_fri": {"queries": 70},
                   "program_sha256": "p" * 64,
                   "canonical_ir_sha256": "r" * 64,
                   "raw": {"qm31_ops": 5}, "padded": {"qm31_ops": 16},
                   "preprocessed_cells": 128,
                   "proof_bytes": 5, "proof_sha256": evidence.s31.file_hash(proof),
                   "independent_value_oracle": {
                       "status": "passed", "computed_public_outputs": claim["public_outputs"]},
                   "independent_value_oracle_provenance": oracle}
            row["observed_cost_model"] = observed_cost_model([row])
            put(trial_dir / "trial-report.json", row)
            trials.append(row)
        profile = {
            "profile": profile_name, "visible_fri": {"queries": 70},
            "raw": {"qm31_ops": 5}, "padded": {"qm31_ops": 16},
            "preprocessed_cells": 128,
            "proof_bytes_per_assignment": [5] * 5, "median_proof_bytes": 5,
            "wall_prove_seconds_per_assignment": [.020] * 5,
            "median_wall_prove_seconds": .020,
            "native_verify_seconds_per_assignment": [.004] * 5,
            "median_native_verify_seconds": .004,
            "prove_excluding_pow_seconds_per_assignment": [.005] * 5,
            "median_prove_excluding_pow_seconds": .005,
            "native_verifier_accepted_all": True,
            "changed_public_statement_rejected_all": True,
            "independent_value_oracle_statuses": ["passed"] * 5,
            "observed_cost_model": observed_cost_model(trials),
        }
        profiles[lowering] = profile
        summary_profiles[lowering] = {key: value for key, value in profile.items()
                                      if key not in ("native_verify_seconds_per_assignment",
                                                     "prove_excluding_pow_seconds_per_assignment",
                                                     "observed_cost_model")}
    schedule = [{"assignment_index": index, "lowering": lowering}
                for index in range(5)
                for lowering in (("direct-gate", "sparse-wide-gate") if index % 2 == 0
                                 else ("sparse-wide-gate", "direct-gate"))]
    tune = {
        "schema": "s31-tune-v1", "source": str(source),
        "program_sha256": "p" * 64, "canonical_ir_sha256": "r" * 64,
        "assignment_sha256": assignments, "distinct_assignments": True,
        "distinct_assignment_count": 5, "warmup_assignment_sha256": assignments[0],
        "same_visible_fri_settings": True, "profiles": profiles,
        "host": {key: value for key, value in host.items() if key != "host_id_sha256"},
        "independent_value_oracle_provenance": oracle,
        "measurement_order": "alternating-by-assignment-v1", "trial_schedule": schedule,
    }
    put(root / "tune" / "tune-report.json", tune)
    put(root / "summary.json", {
        "schema": "s31-fixed-addition-paired-v2", "kind": "u8", "count": 5,
        "compiler_sha256": compiler, "host": host, "source_sha256": source_hash,
        "program_sha256": tune["program_sha256"],
        "canonical_ir_sha256": tune["canonical_ir_sha256"],
        "assignment_sha256": assignments, "same_visible_fri_settings": True,
        "profiles": summary_profiles,
    })
    return host, oracle


class CostAccountingTest(unittest.TestCase):
    def test_artifact_gate_and_tampered_timing(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            host, oracle = evidence_fixture(root)
            with (patch.object(evidence.s31, "compiler_fingerprint", return_value="c" * 64),
                  patch.object(evidence, "host_identity", return_value=host),
                  patch.object(evidence.s31, "oracle_provenance", return_value=oracle)):
                report = evidence.analyze(root)
                self.assertEqual(report["count"], 5)
                self.assertAlmostEqual(
                    report["profiles"]["direct-gate"]["median_whole_process_seconds"],
                    .024)
                self.assertAlmostEqual(
                    report["profiles"]["direct-gate"][
                        "max_absolute_accounting_residual_seconds"], 0)
                trial_path = root / "tune/runs/direct-gate/000/trial-report.json"
                row = json.loads(trial_path.read_text())
                row["prover_stages"]["fri_pow_seconds"] += .001
                put(trial_path, row)
                with self.assertRaisesRegex(ValueError, "PoW/non-PoW accounting"):
                    evidence.analyze(root)

    def test_artifact_gate_rejects_unbalanced_schedule(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp).resolve()
            host, oracle = evidence_fixture(root)
            tune_path = root / "tune/tune-report.json"
            tune = json.loads(tune_path.read_text())
            tune["trial_schedule"][2:4] = tune["trial_schedule"][0:2]
            put(tune_path, tune)
            with (patch.object(evidence.s31, "compiler_fingerprint", return_value="c" * 64),
                  patch.object(evidence, "host_identity", return_value=host),
                  patch.object(evidence.s31, "oracle_provenance", return_value=oracle)):
                with self.assertRaisesRegex(ValueError, "schedule"):
                    evidence.analyze(root)

    def test_complete_process_decomposition(self) -> None:
        parts = evidence.stage_parts(trial_row(), "test")
        self.assertAlmostEqual(parts["whole_process"], .024)
        self.assertAlmostEqual(parts["process_residual"], .006)
        self.assertAlmostEqual(sum(value for key, value in parts.items()
                                   if key != "whole_process"), .024)

    def test_rejects_inconsistent_or_missing_native_timers(self) -> None:
        row = trial_row()
        row["prover_stages"]["fri_pow_seconds"] = .004
        with self.assertRaisesRegex(ValueError, "PoW/non-PoW accounting"):
            evidence.stage_parts(row, "test")
        row = trial_row()
        del row["prover_stages"]["witness_seconds"]
        with self.assertRaisesRegex(ValueError, "incomplete native stage"):
            evidence.stage_parts(row, "test")

    def test_rejects_native_runtime_larger_than_process_wall(self) -> None:
        row = trial_row()
        row["prove_seconds"] = .010
        with self.assertRaisesRegex(ValueError, "exceeds measured prover process"):
            evidence.stage_parts(row, "test")

    def test_interleaves_lowerings_by_assignment(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            source = root / "source.s31"
            source.write_text("source")
            assignments = [root / f"{index}.json" for index in range(4)]
            for index, path in enumerate(assignments):
                path.write_text(json.dumps({"index": index}))
            calls = []

            def build(_source: Path, package: Path, lowering: str) -> Path:
                package.mkdir(parents=True)
                (package / "cost-report.json").write_text(json.dumps({
                    "profile": evidence.LOWERINGS[lowering],
                    "raw": {"qm31_ops": 5}, "padded": {"qm31_ops": 16},
                    "preprocessed_cells": 128, "fri": {"queries": 70},
                }))
                (package / "public-abi.json").write_text("{}")
                return package

            def trial(package: Path, assignment: Path, target: Path) -> dict:
                if "runs" in target.parts:
                    calls.append((int(assignment.stem), package.name))
                return trial_row()

            with (patch.object(paired_tune.s31, "build", side_effect=build),
                  patch.object(paired_tune.s31, "verify_package", return_value={
                      "program_sha256": "p", "canonical_ir_sha256": "c"}),
                  patch.object(paired_tune.s31, "trial", side_effect=trial),
                  patch.object(paired_tune.s31, "visible_fri", return_value={"queries": 70}),
                  patch.object(paired_tune.s31, "oracle_provenance", return_value={}),
                  patch.object(paired_tune.s31, "invoke", return_value="0.15.2")):
                report = paired_tune.tune_interleaved(
                    source, assignments, root / "out",
                    ("direct-gate", "sparse-wide-gate"))
            self.assertEqual(calls, [
                (0, "direct-gate"), (0, "sparse-wide-gate"),
                (1, "sparse-wide-gate"), (1, "direct-gate"),
                (2, "direct-gate"), (2, "sparse-wide-gate"),
                (3, "sparse-wide-gate"), (3, "direct-gate"),
            ])
            self.assertEqual(report["measurement_order"],
                             "alternating-by-assignment-v1")
            self.assertEqual(len(report["trial_schedule"]), 8)


if __name__ == "__main__":
    unittest.main()
