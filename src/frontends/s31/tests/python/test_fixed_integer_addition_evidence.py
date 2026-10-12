"""Archived cost reports must not silently transfer across revisions or hosts."""

from __future__ import annotations

import importlib.util
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[2] / "benchmarks/fixed_integer_addition/validate.py"
SPEC = importlib.util.spec_from_file_location("fixed_addition_evidence", SCRIPT)
assert SPEC and SPEC.loader
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)

COMPILER = "c" * 64
HOST = {"host_id_sha256": "h" * 64, "platform": "test-platform", "machine": "test-cpu",
        "python": "test-python", "zig": "test-zig"}


def put(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True))


def fixture(root: Path) -> None:
    source = root / "u8_checked_add.s31"
    source.write_text("use std@1; circuit u8_checked_add(private a: u8, private b: u8) -> public u8 { std::int::add_checked(a, b) }\n")
    assignments = []
    for index in range(5):
        path = root / "assignments" / f"{index:03d}.json"
        put(path, {"public_inputs": {}, "private_inputs": {"a": [index], "b": [1]},
                   "public_outputs": {"out": [index + 1]}})
        assignments.append(gate.s31.assignment_digest(path))
    fri = {"fold_step": 1}
    profile_map = {}
    for lowering, profile_name in gate.LOWERINGS.items():
        profile = {
            "profile": profile_name, "visible_fri": fri, "raw": {"qm31": 12},
            "padded": {"qm31": 16}, "preprocessed_cells": 128,
            "proof_bytes_per_assignment": [4] * 5, "median_proof_bytes": 4,
            "wall_prove_seconds_per_assignment": [0.1] * 5,
            "median_wall_prove_seconds": 0.1,
            "median_prove_excluding_pow_seconds": 0.05,
            "median_native_verify_seconds": 0.02,
            "native_verifier_accepted_all": True,
            "changed_public_statement_rejected_all": True,
            "independent_value_oracle_statuses": ["passed"] * 5,
        }
        profile_map[lowering] = profile
        put(root / "tune" / "packages" / lowering / "manifest.json", {
            "compiler_sha256": COMPILER,
            "source_text_sha256": gate.s31.file_hash(source),
            "program_sha256": "p" * 64,
            "canonical_ir_sha256": "r" * 64,
            "lowering": lowering,
        })
        for index in range(5):
            trial_dir = root / "tune" / "runs" / lowering / f"{index:03d}"
            trial_dir.mkdir(parents=True, exist_ok=True)
            proof = trial_dir / "proof.bin"
            proof.write_bytes(b"proof")
            put(trial_dir / "trial-report.json", {
                "schema": "s31-trial-v1", "assignment": str(root / "assignments" / f"{index:03d}.json"),
                "program_sha256": "p" * 64,
                "canonical_ir_sha256": "r" * 64,
                "lowering": lowering, "profile": profile_name,
                "visible_fri": fri, "raw": profile["raw"],
                "padded": profile["padded"],
                "preprocessed_cells": profile["preprocessed_cells"],
                "package": str(root / "tune" / "packages" / lowering),
                "proof_bytes": 5,
                "proof_sha256": gate.s31.file_hash(proof),
                "prove_seconds": 0.1, "verify_seconds": 0.02,
                "prover_stages": {"prove_excluding_pow_seconds": 0.05},
                "native_verifier_accepted": True,
                "changed_public_statement_rejected": "public_outputs.out[0]",
                "independent_value_oracle": {"status": "passed"},
            })
        profile["proof_bytes_per_assignment"] = [5] * 5
        profile["median_proof_bytes"] = 5
    tune = {
        "schema": "s31-tune-v1", "source": str(source),
        "program_sha256": "p" * 64,
        "canonical_ir_sha256": "r" * 64,
        "host": {k: v for k, v in HOST.items() if k != "host_id_sha256"},
        "assignment_sha256": assignments,
        "distinct_assignment_count": 5, "distinct_assignments": True,
        "warmup_assignment_sha256": assignments[0],
        "same_visible_fri_settings": True, "profiles": profile_map,
    }
    put(root / "tune" / "tune-report.json", tune)
    put(root / "summary.json", {
        "schema": "s31-fixed-addition-paired-v2", "kind": "u8", "count": 5,
        "compiler_sha256": COMPILER, "host": HOST,
        "source_sha256": gate.s31.file_hash(source),
        "program_sha256": tune["program_sha256"],
        "canonical_ir_sha256": tune["canonical_ir_sha256"],
        "assignment_sha256": assignments,
        "same_visible_fri_settings": True,
        "profiles": {name: {field: profile[field] for field in gate.PROFILE_FIELDS}
                     for name, profile in profile_map.items()},
    })


class FixedAdditionEvidenceTest(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name).resolve()
        fixture(self.root)
        self.compiler = patch.object(gate.s31, "compiler_fingerprint", return_value=COMPILER)
        self.host = patch.object(gate, "host_identity", return_value=HOST)
        self.compiler.start()
        self.host.start()
        self.addCleanup(self.compiler.stop)
        self.addCleanup(self.host.stop)

    def test_current_report_passes(self) -> None:
        self.assertEqual(gate.validate(self.root)["status"],
                         "current-host-and-compiler-evidence-consistent")

    def test_stale_compiler_or_host_rejected(self) -> None:
        with patch.object(gate.s31, "compiler_fingerprint", return_value="d" * 64):
            with self.assertRaisesRegex(ValueError, "stale compiler"):
                gate.validate(self.root)
        with patch.object(gate, "host_identity", return_value={**HOST, "machine": "other"}):
            with self.assertRaisesRegex(ValueError, "another host"):
                gate.validate(self.root)

    def test_proof_or_manifest_mutation_rejected(self) -> None:
        proof = self.root / "tune/runs/direct-gate/000/proof.bin"
        proof.write_bytes(b"bad!!")
        with self.assertRaisesRegex(ValueError, "proof, timing, or control"):
            gate.validate(self.root)
        proof.write_bytes(b"proof")
        manifest = self.root / "tune/packages/direct-gate/manifest.json"
        value = json.loads(manifest.read_text())
        value["compiler_sha256"] = "d" * 64
        put(manifest, value)
        with self.assertRaisesRegex(ValueError, "package manifest compiler_sha256"):
            gate.validate(self.root)

    def test_duplicate_assignment_and_false_control_rejected(self) -> None:
        duplicate = self.root / "assignments/001.json"
        duplicate.write_bytes((self.root / "assignments/000.json").read_bytes())
        with self.assertRaisesRegex(ValueError, "assignment values differ"):
            gate.validate(self.root)
        fixture(self.root)
        trial = self.root / "tune/runs/direct-gate/000/trial-report.json"
        value = json.loads(trial.read_text())
        value["native_verifier_accepted"] = False
        put(trial, value)
        with self.assertRaisesRegex(ValueError, "proof, timing, or control"):
            gate.validate(self.root)


if __name__ == "__main__":
    unittest.main()
