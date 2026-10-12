"""Mutation controls for the scoped S31 candidate evidence checker."""

from __future__ import annotations

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from scripts.release.release_candidate import (
    AUDIT_CASES, FEATURE_CASES, FORMAL_COMMANDS, validate_reports,
)

COMPILER = "a" * 64
SOURCE = "b" * 40
ENGINE = "c" * 40


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


class CandidateReports(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        for name in ("formal/s31/proof-inventory.json", "formal/s31/source-bindings.json"):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps({"file": name}))
        self.audit = {
            "schema": "s31-v01-supported-profile-audit-v1", "release_claim": "not-established",
            "selected_passed": True, "fixture_identity_consistent": True,
            "matrix_identity_consistent": True, "complete_profile_matrix_passed": True,
            "release_candidate_worktree_clean": True, "compiler_sha256_at_end": COMPILER,
            "summary": {"passed": 12, "failed": 0, "not-run": 0},
            "cases": {name: {
                "status": "passed", "compiler_sha256": COMPILER,
                "source_kind": "json-relation" if name.startswith("sha-") else "text",
                "native_verifier_accepted": True,
                "changed_public_statement_rejected": True,
                "altered_key_rejected": True, "altered_proof_rejected": True,
                "independent_value_oracle_passed": True,
                "same_relation_shape_as_handwritten": True,
                "same_canonical_ir_as_handwritten": True,
                "same_reported_air_geometry_as_handwritten": True,
            } for name in AUDIT_CASES},
            "repository": {"commit": SOURCE, "worktree_clean": True},
            "repository_at_end": {"commit": SOURCE, "worktree_clean": True},
            "engine": {"commit": ENGINE, "worktree_clean": True},
            "engine_at_end": {"commit": ENGINE, "worktree_clean": True},
        }
        self.feature = {
            "schema": "s31-scoped-feature-gate-v1", "mode": "full",
            "release_claim": "not-established", "selected_passed": True,
            "mode_complete": True, "compiler_identity_consistent": True,
            "script_identity_consistent": True,
            "compiler_sha256_start": COMPILER, "compiler_sha256_end": COMPILER,
            "selected": sorted(FEATURE_CASES),
            "cases": {name: {"status": "passed", "returncode": 0,
                             "controls": {"cases": 1},
                             **{key: "d" * 64 for key in (
                                 "command_sha256", "result_sha256",
                                 "stdout_sha256", "stderr_sha256")}}
                      for name in FEATURE_CASES},
        }
        self.formal = {
            "schema": "s31-v01-formal-checks-v1", "compiler_sha256": COMPILER,
            "source_commit": SOURCE,
            "inventory_sha256": sha((self.root / "formal/s31/proof-inventory.json").read_bytes()),
            "bindings_sha256": sha((self.root / "formal/s31/source-bindings.json").read_bytes()),
            "checks": {},
        }
        for name, command in FORMAL_COMMANDS.items():
            log = self.root / f"{name}.log"
            log.write_text(f"{name}: OK\n")
            self.formal["checks"][name] = {"command": command, "returncode": 0,
                                           "log": str(log), "log_sha256": sha(log.read_bytes())}

    def check(self) -> dict:
        return validate_reports(self.audit, self.feature, self.formal,
                                compiler=COMPILER, root=self.root)

    def test_valid_finite_packet(self) -> None:
        self.assertEqual(self.check()["feature_checks"], 17)

    def test_missing_audit_profile_fails(self) -> None:
        del self.audit["cases"]["sha-fused"]
        with self.assertRaisesRegex(ValueError, "audit matrix"):
            self.check()

    def test_failed_native_control_fails(self) -> None:
        self.audit["cases"]["direct-gate"]["changed_public_statement_rejected"] = False
        with self.assertRaisesRegex(ValueError, "changed_public_statement_rejected"):
            self.check()

    def test_partial_feature_gate_fails(self) -> None:
        self.feature["mode_complete"] = False
        with self.assertRaisesRegex(ValueError, "mode_complete"):
            self.check()

    def test_feature_compiler_drift_fails(self) -> None:
        self.feature["compiler_sha256_end"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "feature compiler pin"):
            self.check()

    def test_missing_formal_log_fails(self) -> None:
        Path(self.formal["checks"]["leanchecker"]["log"]).unlink()
        with self.assertRaisesRegex(ValueError, "formal log digest mismatch"):
            self.check()

    def test_stale_formal_inventory_fails(self) -> None:
        (self.root / "formal/s31/proof-inventory.json").write_text("changed")
        with self.assertRaisesRegex(ValueError, "formal inventory_sha256"):
            self.check()

    def test_missing_formal_source_commit_fails(self) -> None:
        self.formal["source_commit"] = None
        with self.assertRaisesRegex(ValueError, "formal source commit"):
            self.check()

    def test_failed_lean_command_fails(self) -> None:
        self.formal["checks"]["lake_build"]["returncode"] = 1
        with self.assertRaisesRegex(ValueError, "formal command failed"):
            self.check()


if __name__ == "__main__":
    unittest.main()
