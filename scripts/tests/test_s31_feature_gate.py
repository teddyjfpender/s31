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
        count = 2 if check.id == "static-enum-effects-source" else 5
        return "", (".\n----------------------------------------------------------------------\n"
                    f"Ran {count} tests in 0.001s\n\nOK\n")
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
    elif fmt == "static-enum-if-native":
        report = {"schema": "s31-static-enum-if-acceptance-v1",
                  "profile": "direct-m31-v4", "raw": {"qm31_ops": 280},
                  "padded": {"qm31_ops": 512}, "preprocessed_cells": 4096,
                  "equal_relation_and_air": True,
                  "selected_and_eager_partial_arms_rejected": True,
                  "proofs": [{"flag": flag, "x": x, "native_verified": True,
                              "changed_claim_rejected": True,
                              "oracle_passed": True,
                              "proof_bytes": 1000}
                             for flag, x in ((1, 7), (0, 7), (0, 0))]}
    elif fmt == "power-native":
        report = {"schema": "s31-power-chain-native-v1", "lanes": 8,
                  "stages": 4, "exponent_per_stage": 65535,
                  "saved_arithmetic_nodes": 44, "saved_raw_qm31_rows": 88,
                  "halved_padded_rows": True,
                  "cases": [{"kind": kind, "nodes": nodes,
                             "raw_qm31_rows": raw, "padded_qm31_rows": padded,
                             "preprocessed_cells": cells, "proof_bytes": 1000,
                             "native_verified": True,
                             "changed_claim_rejected": True,
                             "independent_oracle_passed": True,
                             "symbolic_exponent_checked": True}
                            for kind, nodes, raw, padded, cells in
                            (("addition-chain", 76, 471, 512, 4096),
                             ("binary", 120, 559, 1024, 8192))]}
    elif fmt == "factor-power-native":
        report = {"schema": "s31-factor-power-native-v1", "lanes": 8,
                  "stages": 4, "exponent_per_stage": 196605,
                  "binary_source_sha256":
                  "0d84aa30895d22dd5c105c7a0a384913d53ef0b0f45364dcbd4470cf93b952a3",
                  "saved_arithmetic_nodes": 44, "saved_raw_qm31_rows": 88,
                  "halved_padded_rows": True,
                  "cases": [{"kind": kind, "nodes": nodes,
                             "raw_qm31_rows": raw, "padded_qm31_rows": padded,
                             "preprocessed_cells": cells, "proof_bytes": 1000,
                             "native_verified": True,
                             "changed_claim_rejected": True,
                             "independent_oracle_passed": True,
                             "symbolic_exponent_checked": True}
                            for kind, nodes, raw, padded, cells in
                            (("factor-chain", 84, 487, 512, 4096),
                             ("binary", 128, 575, 1024, 8192))]}
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
        self.assertEqual(len(source), 10)
        self.assertEqual(len(smoke), 18)
        self.assertEqual(len(full), 21)
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

    def test_static_enum_native_report_requires_all_three_proofs(self) -> None:
        check = next(item for item in gate.checks("full")
                     if item.id == "static-enum-if-native")
        stdout, _ = fake_report(check)
        self.assertEqual(gate.validate_output(check, stdout, "", FINGERPRINT)["cases"], 3)
        for mutation in (lambda report: report["proofs"].pop(),
                         lambda report: report["proofs"][2].update({"native_verified": False}),
                         lambda report: report["proofs"][0].update({"changed_claim_rejected": False}),
                         lambda report: report["raw"].update({"qm31_ops": 281}),
                         lambda report: report.update({"selected_and_eager_partial_arms_rejected": False})):
            report = json.loads(stdout)
            mutation(report)
            with self.assertRaisesRegex(ValueError, "static enum conditional"):
                gate.validate_output(check, json.dumps(report), "", FINGERPRINT)

    def test_static_enum_source_corpus_requires_both_checks(self) -> None:
        check = next(item for item in gate.checks("source")
                     if item.id == "static-enum-effects-source")
        stdout, stderr = fake_report(check)
        self.assertEqual(gate.validate_output(check, stdout, stderr)["tests"], 2)
        with self.assertRaisesRegex(ValueError, "static enum source corpus"):
            gate.validate_output(check, stdout, stderr.replace("Ran 2", "Ran 1"))

    def test_power_chain_native_report_requires_both_proofs_and_costs(self) -> None:
        check = next(item for item in gate.checks("full")
                     if item.id == "pow65535-native")
        stdout, _ = fake_report(check)
        self.assertEqual(gate.validate_output(check, stdout, "")["cases"], 2)
        for mutation in (lambda report: report["cases"].pop(),
                         lambda report: report["cases"][0].update({"padded_qm31_rows": 1024}),
                         lambda report: report["cases"][1].update({"symbolic_exponent_checked": False}),
                         lambda report: report["cases"][0].update({"native_verified": False})):
            report = json.loads(stdout)
            mutation(report)
            with self.assertRaisesRegex(ValueError, "power chain"):
                gate.validate_output(check, json.dumps(report), "")

    def test_factor_power_native_report_requires_both_proofs_and_costs(self) -> None:
        check = next(item for item in gate.checks("full")
                     if item.id == "pow-factor-native")
        stdout, _ = fake_report(check)
        self.assertEqual(gate.validate_output(check, stdout, "")["cases"], 2)
        for mutation in (lambda report: report["cases"].pop(),
                         lambda report: report.update({"binary_source_sha256": "0" * 64}),
                         lambda report: report["cases"][0].update({"padded_qm31_rows": 1024}),
                         lambda report: report["cases"][1].update({"native_verified": False})):
            report = json.loads(stdout)
            mutation(report)
            with self.assertRaisesRegex(ValueError, "factor power"):
                gate.validate_output(check, json.dumps(report), "")

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
