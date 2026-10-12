"""Mutation controls for the scoped S31 candidate evidence checker."""

from __future__ import annotations

import hashlib
import json
import tempfile
import unittest
import subprocess
from pathlib import Path

from scripts.release.release_candidate import (
    AUDIT_CASES, AUDIT_FIXTURES, FEATURE_CASES, FORMAL_COMMANDS,
    validate_reports, require_formal_tree_unchanged,
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
        script = self.root / "scripts/release/s31_v01_audit.py"
        script.parent.mkdir(parents=True, exist_ok=True)
        script.write_text("# audit fixture\n")
        gate_script = self.root / "scripts/release/s31_feature_gate.py"
        gate_script.write_text("# feature gate fixture\n")
        for source, assignment, manual in AUDIT_FIXTURES.values():
            for name in (source, assignment, manual):
                if name is not None:
                    fixture = self.root / "src/frontends/s31/examples" / name
                    fixture.parent.mkdir(parents=True, exist_ok=True)
                    fixture.write_text(name)
        feature_script = self.root / "src/frontends/s31/tests/check.py"
        feature_script.parent.mkdir(parents=True, exist_ok=True)
        feature_script.write_text("# feature fixture\n")
        for name in ("formal/s31/proof-inventory.json", "formal/s31/source-bindings.json"):
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(json.dumps({"file": name}))
        self.audit = {
            "schema": "s31-v01-supported-profile-audit-v1", "release_claim": "not-established",
            "audit_script_sha256": sha(script.read_bytes()),
            "selected_passed": True, "fixture_identity_consistent": True,
            "matrix_identity_consistent": True, "complete_profile_matrix_passed": True,
            "release_candidate_worktree_clean": True, "compiler_sha256_at_end": COMPILER,
            "summary": {"passed": 12, "failed": 0, "not-run": 0},
            "cases": {name: {
                "status": "passed", "compiler_sha256": COMPILER,
                "source": AUDIT_FIXTURES[name][0],
                "assignment": AUDIT_FIXTURES[name][1],
                "handwritten_equivalent": AUDIT_FIXTURES[name][2],
                "fri_fold_step": 4 if name in {"gate-fri4", "sparse-wide-gate-fri4"} else 1,
                "source_sha256": sha((self.root / "src/frontends/s31/examples" /
                                      AUDIT_FIXTURES[name][0]).read_bytes()),
                "assignment_sha256": sha((self.root / "src/frontends/s31/examples" /
                                          AUDIT_FIXTURES[name][1]).read_bytes()),
                "handwritten_source_sha256": (
                    sha((self.root / "src/frontends/s31/examples" /
                         AUDIT_FIXTURES[name][2]).read_bytes())
                    if AUDIT_FIXTURES[name][2] is not None else None),
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
        command = {"argv": ["python3", "-B", "src/frontends/s31/tests/check.py"],
                   "cwd": str(self.root), "script_sha256": sha(feature_script.read_bytes())}
        command_sha = sha((json.dumps(command, sort_keys=True, separators=(",", ":"),
                                       ensure_ascii=True) + "\n").encode("ascii"))
        self.feature = {
            "schema": "s31-scoped-feature-gate-v1", "mode": "full",
            "gate_script_sha256": sha(gate_script.read_bytes()),
            "release_claim": "not-established", "selected_passed": True,
            "mode_complete": True, "compiler_identity_consistent": True,
            "script_identity_consistent": True,
            "compiler_sha256_start": COMPILER, "compiler_sha256_end": COMPILER,
            "selected": sorted(FEATURE_CASES),
            "cases": {name: {"status": "passed", "returncode": 0,
                             "controls": {"cases": 1},
                             "command": command, "command_sha256": command_sha,
                             "stdout_sha256": "d" * 64, "stderr_sha256": "d" * 64,
                             "result_sha256": sha((json.dumps({
                                 "command_sha256": command_sha, "returncode": 0,
                                 "stdout_sha256": "d" * 64, "stderr_sha256": "d" * 64,
                             }, sort_keys=True, separators=(",", ":"), ensure_ascii=True)
                                 + "\n").encode("ascii"))}
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

    def test_changed_audit_script_fails(self) -> None:
        (self.root / "scripts/release/s31_v01_audit.py").write_text("changed")
        with self.assertRaisesRegex(ValueError, "audit script differs"):
            self.check()

    def test_changed_audit_fixture_fails(self) -> None:
        (self.root / "src/frontends/s31/examples/arithmetic/functional_square4.s31").write_text("changed")
        with self.assertRaisesRegex(ValueError, "current fixture differs"):
            self.check()

    def test_relabelled_audit_fixture_fails(self) -> None:
        self.audit["cases"]["gate"]["source"] = "different.s31"
        with self.assertRaisesRegex(ValueError, "fixture identity mismatch"):
            self.check()

    def test_relabelled_audit_schedule_fails(self) -> None:
        self.audit["cases"]["gate-fri4"]["fri_fold_step"] = 1
        with self.assertRaisesRegex(ValueError, "FRI schedule mismatch"):
            self.check()

    def test_changed_feature_script_fails(self) -> None:
        (self.root / "src/frontends/s31/tests/check.py").write_text("changed")
        with self.assertRaisesRegex(ValueError, "script differs"):
            self.check()

    def test_changed_feature_gate_runner_fails(self) -> None:
        (self.root / "scripts/release/s31_feature_gate.py").write_text("changed")
        with self.assertRaisesRegex(ValueError, "feature gate script differs"):
            self.check()

    def test_feature_result_identity_fails(self) -> None:
        self.feature["cases"]["record-u32-native"]["result_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "result identity mismatch"):
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


class FormalTreeFreshness(unittest.TestCase):
    def test_descendant_formal_source_or_binding_script_change_fails(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            def git(*args: str) -> str:
                return subprocess.check_output(["git", "-C", str(root), *args],
                                               text=True, stderr=subprocess.DEVNULL).strip()
            git("init", "-q")
            git("config", "user.name", "Test")
            git("config", "user.email", "test@example.invalid")
            lean = root / "formal/s31/S31/New.lean"
            lean.parent.mkdir(parents=True)
            lean.write_text("def x := 1\n")
            script = root / "scripts/s31_formal.py"
            script.parent.mkdir(parents=True)
            script.write_text("# first\n")
            git("add", ".")
            git("commit", "-qm", "formal checked")
            checked = git("rev-parse", "HEAD")
            (root / "README.md").write_text("release note\n")
            git("add", ".")
            git("commit", "-qm", "docs only")
            require_formal_tree_unchanged(root, checked, git("rev-parse", "HEAD"))
            for path, value in ((lean, "def x := 2\n"),
                                (script, "# changed\n")):
                path.write_text(value)
                git("add", ".")
                git("commit", "-qm", "formal changed")
                with self.assertRaisesRegex(ValueError, "formal sources or binding checker"):
                    require_formal_tree_unchanged(root, checked, git("rev-parse", "HEAD"))


if __name__ == "__main__":
    unittest.main()
