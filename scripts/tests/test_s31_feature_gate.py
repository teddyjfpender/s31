"""Mocked orchestration and fail-closed report checks for the feature gate."""

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import unittest
from unittest.mock import patch

from scripts.release import s31_feature_gate as gate

FINGERPRINT = "a" * 64


def fake_report(check: gate.Check) -> tuple[str, str]:
    fmt = check.format
    if fmt == "unittest":
        return "", ".....\n----------------------------------------------------------------------\nRan 5 tests in 0.001s\n\nOK\n"
    if fmt.startswith("addition-"):
        native = check.native
        report = {"schema": "s31-int-addition-native-v1" if native else "s31-int-addition-source-v1",
                  "lowering": "direct-gate" if native else "sparse-wide-gate",
                  "compiler_sha256": FINGERPRINT,
                  "cases": [{"kind": kind, "source_and_oracle_checked": True,
                             "native_not_run": True,
                             "native_verifier_accepted": True,
                             "changed_public_statement_rejected": True,
                             "native_overflow_rejected": True}
                            for kind in check.expected_kinds]}
    elif fmt.startswith("binary-"):
        report = {"schema": "s31-direct-integer-binary-v1", "native": check.native,
                  "cases": [{"kind": kind, "operation": op,
                             "source_and_oracle_checked": True,
                             "native_verifier_accepted": True,
                             "changed_public_statement_rejected": True,
                             "native_underflow_rejected": True}
                            for kind in check.expected_kinds for op in ("sub_checked", "le")]}
    elif fmt.startswith("multiplication-"):
        report = {"schema": "s31-direct-integer-multiplication-v1", "native": check.native,
                  "compiler_sha256": FINGERPRINT,
                  "cases": [{"kind": kind, "mode": mode,
                             "source_and_oracle_checked": True,
                             "native_verifier_accepted": True,
                             "changed_public_statement_rejected": True,
                             "native_overflow_rejected": mode == "checked"}
                            for kind in check.expected_kinds for mode in check.expected_modes]}
    elif fmt == "static-sum-native":
        report = {"native_verifier_accepted": True,
                  "changed_public_statement_rejected": True,
                  "equal_native_air_geometry": True}
    elif fmt == "record-source-native":
        report = {"schema": "s31-record-source-fragment-native-v2",
                  "capability": "source-to-relation-only",
                  "native_verifier_accepted": True,
                  "abi_valid_changed_claim_rejected_by_proof": True}
    elif fmt.startswith("record-u32-"):
        report = {"schema": "s31-public-u32-record-v2", "native": check.native,
                  "compiler_sha256": FINGERPRINT, "limb_order": "little-endian",
                  "honest": [0, 0xffffffff], "input_range_bits": 32,
                  "result_aliases_public_input": True}
    else:
        width = 8 if "u8" in fmt else 16
        report = {"schema": f"s31-public-u{width}-record-v2", "native": check.native,
                  f"result_u{width}_aliases_input": True,
                  "range_gates_per_input_word": width}
    return json.dumps(report), ""


def fake_execute(check: gate.Check) -> subprocess.CompletedProcess[str]:
    stdout, stderr = fake_report(check)
    return subprocess.CompletedProcess(check.argv(), 0, stdout, stderr)


class FeatureGateTests(unittest.TestCase):
    def test_inventory_is_scoped_and_scripts_exist(self) -> None:
        source = gate.checks("source")
        smoke = gate.checks("smoke")
        full = gate.checks("full")
        self.assertEqual(len(source), 9)
        self.assertEqual(len(smoke), 16)
        self.assertEqual(len(full), 17)
        for inventory in (source, smoke, full):
            self.assertEqual(len({check.id for check in inventory}), len(inventory))
            for check in inventory:
                self.assertTrue((gate.ROOT / check.script).is_file(), check.script)
        self.assertFalse(any(check.native for check in source))
        self.assertTrue(any(check.native for check in smoke))
        self.assertTrue(any(check.native for check in full))

    def test_mocked_source_matrix_passes_without_native(self) -> None:
        report = gate.run_suite("source", execute_fn=fake_execute,
                                fingerprint_fn=lambda: FINGERPRINT)
        self.assertTrue(report["selected_passed"])
        self.assertTrue(report["mode_complete"])
        self.assertEqual(report["release_claim"], "not-established")
        self.assertEqual(report["compiler_sha256_start"], FINGERPRINT)
        self.assertEqual(report["compiler_sha256_end"], FINGERPRINT)
        for row in report["cases"].values():
            self.assertEqual(row["status"], "passed")
            self.assertFalse(row["native"])
            self.assertEqual(len(row["command_sha256"]), 64)
            self.assertEqual(len(row["result_sha256"]), 64)
            self.assertEqual(row["command_sha256"], gate.digest(gate.canonical(row["command"])))

    def test_partial_native_smoke_never_claims_complete(self) -> None:
        report = gate.run_suite("smoke", {"direct-mul-u8-native"},
                                execute_fn=fake_execute, fingerprint_fn=lambda: FINGERPRINT)
        self.assertTrue(report["selected_passed"])
        self.assertFalse(report["mode_complete"])
        self.assertEqual(report["cases"]["direct-add-u8-native"]["status"], "not-run")
        self.assertEqual(report["cases"]["direct-mul-u8-native"]["controls"]["cases"], 2)

    def test_missing_width_and_negative_control_fail_closed(self) -> None:
        add = next(check for check in gate.checks("smoke") if check.id == "direct-add-u8-native")
        stdout, _ = fake_report(add)
        altered = json.loads(stdout)
        altered["cases"] = []
        with self.assertRaisesRegex(ValueError, "missing or extra widths"):
            gate.validate_output(add, json.dumps(altered), "", FINGERPRINT)
        altered = json.loads(stdout)
        altered["cases"][0]["changed_public_statement_rejected"] = False
        with self.assertRaisesRegex(ValueError, "failed a control"):
            gate.validate_output(add, json.dumps(altered), "", FINGERPRINT)
        altered = json.loads(stdout)
        altered["compiler_sha256"] = "b" * 64
        with self.assertRaisesRegex(ValueError, "different compiler fingerprint"):
            gate.validate_output(add, json.dumps(altered), "", FINGERPRINT)

    def test_compiler_drift_and_subprocess_failure_are_nonpassing(self) -> None:
        calls = iter((FINGERPRINT, FINGERPRINT, "b" * 64, "b" * 64))
        drift = gate.run_suite("source", {"v1-source-relation"},
                               execute_fn=fake_execute, fingerprint_fn=lambda: next(calls))
        self.assertFalse(drift["selected_passed"])
        self.assertFalse(drift["compiler_identity_consistent"])
        self.assertIn("drift", drift["cases"]["v1-source-relation"]["error"])

        def failing(check: gate.Check) -> subprocess.CompletedProcess[str]:
            return subprocess.CompletedProcess(check.argv(), 1, "", "forged proof accepted")

        failed = gate.run_suite("source", {"v1-source-relation"},
                                execute_fn=failing, fingerprint_fn=lambda: FINGERPRINT)
        self.assertFalse(failed["selected_passed"])
        self.assertEqual(failed["cases"]["v1-source-relation"]["returncode"], 1)
        self.assertIn("forged proof accepted", failed["cases"]["v1-source-relation"]["error"])

        long_stderr = "early Zig compile error\n" + "x" * 6000 + "\nlate build summary"
        def failed_build(check: gate.Check) -> subprocess.CompletedProcess[str]:
            return subprocess.CompletedProcess(check.argv(), 1, "", long_stderr)
        failed = gate.run_suite("source", {"v1-source-relation"},
                                execute_fn=failed_build, fingerprint_fn=lambda: FINGERPRINT)
        self.assertIn("early Zig compile error", failed["cases"]["v1-source-relation"]["error"])
        self.assertIn("late build summary", failed["cases"]["v1-source-relation"]["error"])

    def test_raw_output_hash_and_script_mutation(self) -> None:
        selected = {"v1-source-relation"}

        def byte_result(check: gate.Check) -> subprocess.CompletedProcess[bytes]:
            stdout, stderr = fake_report(check)
            return subprocess.CompletedProcess(check.argv(), 0, stdout.encode(), stderr.encode())

        report = gate.run_suite("source", selected, execute_fn=byte_result,
                                fingerprint_fn=lambda: FINGERPRINT)
        row = report["cases"]["v1-source-relation"]
        self.assertTrue(report["selected_passed"])
        self.assertEqual(row["stdout_sha256"], gate.digest(b""))
        self.assertEqual(row["result_sha256"], gate.digest(gate.canonical({
            "command_sha256": row["command_sha256"], "returncode": 0,
            "stdout_sha256": row["stdout_sha256"], "stderr_sha256": row["stderr_sha256"],
        })))

        with patch.object(gate.Path, "read_bytes",
                          side_effect=[b"first", b"first", b"changed", b"changed"]):
            changed = gate.run_suite("source", selected, execute_fn=byte_result,
                                     fingerprint_fn=lambda: FINGERPRINT)
        self.assertFalse(changed["selected_passed"])
        self.assertFalse(changed["script_identity_consistent"])
        self.assertIn("script changed", changed["cases"]["v1-source-relation"]["error"])

    def test_unittest_must_run_tests_and_list_does_not_run(self) -> None:
        check = gate.checks("source")[0]
        with self.assertRaisesRegex(ValueError, "nonempty"):
            gate.validate_output(check, "", "Ran 0 tests in 0.001s\n\nOK\n")
        with patch.object(gate, "run_suite", side_effect=AssertionError("executed")):
            with contextlib.redirect_stdout(io.StringIO()) as capture:
                self.assertEqual(gate.main(["--list", "--mode", "smoke"]), 0)
        report = json.loads(capture.getvalue())
        self.assertFalse(report["selected_passed"])
        self.assertEqual({row["status"] for row in report["cases"].values()}, {"not-run"})


if __name__ == "__main__":
    unittest.main()
