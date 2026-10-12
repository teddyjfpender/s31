"""Fast structural controls for the executable release matrix."""

from __future__ import annotations

import unittest
from unittest.mock import patch
import contextlib
import io

from scripts.release import s31_v01_audit as audit


class ReleaseAuditTests(unittest.TestCase):
    @staticmethod
    def passed_row(compiler_sha256: str) -> dict:
        return {"status": "passed", "compiler_sha256": compiler_sha256,
                "source_sha256": "a" * 64, "assignment_sha256": "b" * 64,
                "handwritten_source_sha256": "c" * 64}

    def test_inventory_matches_cli_and_fixtures(self) -> None:
        audit.check_inventory()
        self.assertEqual({case.lowering for case in audit.CASES}, audit.cli_lowerings())
        self.assertEqual(len(audit.CASES), 12)
        self.assertEqual(audit.case_ids() - audit.cli_lowerings(),
                         {"gate-fri4", "sparse-wide-gate-fri4"})

    def test_list_does_not_claim_execution(self) -> None:
        report = audit.audit(audit.case_ids(), False,
                             runner=lambda *_: self.fail("list ran native work"))
        self.assertFalse(report["selected_passed"])
        self.assertFalse(report["complete_profile_matrix_passed"])
        self.assertEqual({row["status"] for row in report["cases"].values()}, {"not-run"})
        self.assertEqual(report["release_claim"], "not-established")

    def test_partial_run_never_claims_complete_matrix(self) -> None:
        report = audit.audit({"direct-gate"}, True,
                             runner=lambda *_: self.passed_row(audit.s31.compiler_fingerprint()))
        self.assertTrue(report["selected_passed"])
        self.assertTrue(report["matrix_identity_consistent"])
        self.assertFalse(report["complete_profile_matrix_passed"])
        self.assertEqual(report["cases"]["gate"]["status"], "not-run")

    def test_runner_error_fails_closed(self) -> None:
        def broken(*_):
            raise AssertionError("changed claim accepted")

        report = audit.audit({"direct-gate"}, True, runner=broken)
        self.assertFalse(report["selected_passed"])
        self.assertEqual(report["cases"]["direct-gate"]["status"], "failed")
        self.assertIn("changed claim accepted", report["cases"]["direct-gate"]["error"])

    def test_stale_compiler_fingerprint_blocks_complete_matrix(self) -> None:
        report = audit.audit(audit.case_ids(), True,
                             runner=lambda *_: self.passed_row("0" * 64))
        self.assertTrue(report["selected_passed"])
        self.assertTrue(report["fixture_identity_consistent"])
        self.assertFalse(report["matrix_identity_consistent"])
        self.assertFalse(report["complete_profile_matrix_passed"])

    def test_repeated_fixtures_must_have_matching_digests_across_rows(self) -> None:
        one = {"status": "passed", "source_sha256": "a" * 64,
               "assignment_sha256": "b" * 64,
               "handwritten_source_sha256": "c" * 64}
        rows = {"gate": dict(one), "gate-fri4": dict(one)}
        self.assertTrue(audit.fixture_digests_consistent({"gate", "gate-fri4"}, rows))
        for field in ("source_sha256", "assignment_sha256", "handwritten_source_sha256"):
            with self.subTest(field=field):
                altered = {name: dict(row) for name, row in rows.items()}
                altered["gate-fri4"][field] = "d" * 64
                self.assertFalse(audit.fixture_digests_consistent({"gate", "gate-fri4"}, altered))
        rows["gate-fri4"].pop("source_sha256")
        self.assertFalse(audit.fixture_digests_consistent({"gate", "gate-fri4"}, rows))

    def test_cross_row_fixture_drift_blocks_matrix_identity(self) -> None:
        compiler = audit.s31.compiler_fingerprint()

        def changed_between_rows(case: audit.Case, _work: object) -> dict:
            row = self.passed_row(compiler)
            if case.id == "gate-fri4":
                row["source_sha256"] = "d" * 64
            return row

        report = audit.audit({"gate", "gate-fri4"}, True, runner=changed_between_rows)
        self.assertTrue(report["selected_passed"])
        self.assertFalse(report["fixture_identity_consistent"])
        self.assertFalse(report["matrix_identity_consistent"])

    def test_cli_exits_nonzero_when_rows_pass_but_identity_is_stale(self) -> None:
        stale = {"schema": "s31-v01-supported-profile-audit-v1",
                 "selected_passed": True, "matrix_identity_consistent": False}
        with patch.object(audit, "audit", return_value=stale), \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(audit.main(["--profile", "direct-gate"]), 1)
            self.assertEqual(audit.main(["--list"]), 0)

    def test_inventory_drift_rejected(self) -> None:
        original = audit.cli_lowerings
        try:
            audit.cli_lowerings = lambda: original() | {"new-chip"}
            with self.assertRaisesRegex(ValueError, "new-chip"):
                audit.check_inventory()
        finally:
            audit.cli_lowerings = original

    def test_fri_schedule_drift_rejected(self) -> None:
        original = audit.cli_fri_fold_steps
        try:
            audit.cli_fri_fold_steps = lambda: {1, 4, 8}
            with self.assertRaisesRegex(ValueError, "FRI fold choices"):
                audit.check_inventory()
        finally:
            audit.cli_fri_fold_steps = original


if __name__ == "__main__":
    unittest.main()
