"""Doctor startup, dependencies, timeouts, and native verification controls."""

import json
import contextlib
import io
import shutil
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))
from cli import doctor


class DoctorTests(unittest.TestCase):
    def test_missing_engine_still_emits_structured_diagnostics(self):
        with tempfile.TemporaryDirectory() as temporary:
            s31 = Path(temporary) / "src/frontends/s31"
            (s31 / "python/cli").mkdir(parents=True)
            for name in ("s31.py", "cli/doctor.py"):
                shutil.copyfile(S31 / "python" / name, s31 / "python" / name)
            (s31 / "python/cli/__init__.py").touch()
            result = subprocess.run([sys.executable, "-B", str(s31 / "python/s31.py"), "doctor", "--json"],
                                    text=True, capture_output=True, timeout=30)
            self.assertEqual(result.returncode, 1, result.stderr)
            report = json.loads(result.stdout)
            rows = {row["id"]: row for row in report["checks"]}
            self.assertEqual(rows["source-layout"]["status"], "fail")
            self.assertEqual(rows["frontend-oracle"]["status"], "skip")
            self.assertNotIn("Traceback", result.stderr)

    def setup_tree(self, root, bundle=False):
        s31 = root / "src/frontends/s31"
        for relative in ("src/frontends/s31/build.zig", "src/frontends/s31/build.zig.zon",
                         "src/frontends/s31/python/s31.py", "src/frontends/s31/python/text_frontend.py",
                         "deps/stwo-zig/src/integrations/circuit_cpu/build.zig",
                         "deps/stwo-zig/vectors/circuit/official/compiled_air_constraints_v1.bin",
                         "deps/stwo-zig/vectors/circuit/official/circuit_air.air_programs_v1.bin"):
            path = root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.touch()
        if bundle:
            (root / "SOURCE-BUNDLE.json").write_text("{}")
        else:
            (root / ".git").mkdir()
        return s31

    def fake_runner(self, zig="0.15.2", pin="a" * 40, measurement=True, changed=1,
                    changed_output="error: InvalidInteractionNonce", build_failure=False):
        def run(command, cwd, timeout):
            if command[0] == "git":
                return 0, f"160000 commit {pin}\tdeps/stwo-zig"
            if command[-1] == "version":
                return 0, zig
            if command[0] == "/usr/bin/time":
                return (0, "123 maximum resident set size") if measurement else (1, "sysctl: Operation not permitted")
            if "-c" in command:
                code = command[-1]
                if "pinned_engine_commit" in code:
                    return 0, "a" * 40
                return 0, "smoke passed"
            if "build" in command:
                return (1, "undefined symbol: _abort") if build_failure else (0, "package")
            if any("changed-statement.json" in arg for arg in command):
                return changed, changed_output
            return 0, "proof accepted"
        return run

    def diagnose(self, root, s31, runner, **kwargs):
        with patch.object(doctor, "run", side_effect=runner), patch.object(doctor.shutil, "which", return_value="/tools/zig"), \
                patch.object(doctor.platform, "system", return_value="Linux"), \
                patch.object(doctor.Path, "is_file", return_value=True):
            return doctor.diagnose(root, s31, **kwargs)

    def test_wrong_zig_skips_native(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            report = self.diagnose(root, self.setup_tree(root), self.fake_runner(zig="0.16.0"), native=True)
            rows = {row["id"]: row for row in report["checks"]}
            self.assertEqual(rows["zig"]["status"], "fail")
            self.assertEqual(rows["native-build"]["status"], "skip")
            self.assertFalse(report["passed"])

    def test_missing_zig_is_actionable(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            s31 = self.setup_tree(root)
            with patch.object(doctor, "run", side_effect=self.fake_runner()), \
                    patch.object(doctor.shutil, "which", return_value=None):
                report = doctor.diagnose(root, s31)
            row = next(row for row in report["checks"] if row["id"] == "zig")
            self.assertEqual(row["status"], "fail")
            self.assertIn("PATH", row["remediation"])

    def test_mismatched_engine_pin(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            report = self.diagnose(root, self.setup_tree(root), self.fake_runner(pin="b" * 40))
            row = next(row for row in report["checks"] if row["id"] == "engine-identity")
            self.assertEqual(row["status"], "fail")
            self.assertIn("HEAD pins", row["detail"])

    def test_dirty_engine_paths_are_reported(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            s31 = self.setup_tree(root)
            (root / "deps/stwo-zig/.git").touch()
            runner = self.fake_runner()
            def dirty(command, cwd, timeout):
                if "status" in command:
                    return 0, " M src/prover.zig"
                return runner(command, cwd, timeout)
            report = self.diagnose(root, s31, dirty)
            row = next(row for row in report["checks"] if row["id"] == "engine-identity")
            self.assertEqual(row["status"], "fail")
            self.assertIn("src/prover.zig", row["detail"])

    def test_bundle_uses_identity_helper_without_git(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            runner = self.fake_runner()
            def without_git(command, cwd, timeout):
                self.assertNotEqual(command[0], "git")
                return runner(command, cwd, timeout)
            report = self.diagnose(root, self.setup_tree(root, bundle=True), without_git)
            self.assertTrue(report["passed"])
            self.assertFalse(report["native_passed"])

    def test_native_success_ignores_unavailable_measurement_and_cleans_up(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            created = root / "artifacts"
            created.mkdir()
            with patch.object(doctor.tempfile, "mkdtemp", return_value=str(created)):
                report = self.diagnose(root, self.setup_tree(root), self.fake_runner(measurement=False), native=True)
            self.assertTrue(report["native_passed"])
            self.assertTrue(report["passed"])
            self.assertFalse(created.exists())
            self.assertEqual(next(row for row in report["checks"] if row["id"] == "resource-measurement")["status"], "warn")

    def test_native_build_error_retains_requested_artifacts(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            report = self.diagnose(root, self.setup_tree(root), self.fake_runner(build_failure=True), native=True, keep_artifacts=True)
            try:
                self.assertFalse(report["passed"])
                self.assertTrue(Path(report["native_artifacts"]).is_dir())
                rows = {row["id"]: row for row in report["checks"]}
                self.assertIn("undefined symbol", rows["native-build"]["detail"])
                self.assertEqual(rows["native-prove"]["status"], "skip")
            finally:
                shutil.rmtree(report["native_artifacts"])

    def test_changed_claim_acceptance_or_crash_is_failure(self):
        for code in (0, -11, 2):
            with self.subTest(code=code), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                report = self.diagnose(root, self.setup_tree(root), self.fake_runner(changed=code), native=True)
                self.assertFalse(report["passed"])
                self.assertFalse(report["native_passed"])

    def test_unrelated_verifier_failure_is_not_a_statement_rejection(self):
        for output in ("error: FileNotFound", "error: OutOfMemory", "", "error: InvalidInteractionNonce\nerror: FileNotFound"):
            with self.subTest(output=output), tempfile.TemporaryDirectory() as temporary:
                root = Path(temporary)
                report = self.diagnose(root, self.setup_tree(root), self.fake_runner(changed_output=output), native=True)
                self.assertFalse(report["passed"])
                self.assertFalse(report["native_passed"])

    def test_cleanup_failure_is_structured_and_reports_artifacts(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            s31 = self.setup_tree(root)
            with patch.object(doctor.shutil, "rmtree", side_effect=PermissionError("denied")):
                report = self.diagnose(root, s31, self.fake_runner(), native=True)
            try:
                self.assertFalse(report["passed"])
                self.assertTrue(report["native_passed"])
                self.assertTrue(Path(report["native_artifacts"]).exists())
                row = next(row for row in report["checks"] if row["id"] == "native-cleanup")
                self.assertEqual(row["status"], "fail")
                json.dumps(report)
            finally:
                shutil.rmtree(report["native_artifacts"])

    def test_oracle_check_remains_active_under_python_optimization(self):
        runner = self.fake_runner()
        real_run = doctor.run
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            s31 = self.setup_tree(root)
            (s31 / "python/text_frontend.py").write_text("def compile_text(source): return {}, {}\n")
            (s31 / "python/oracle.py").write_text("def evaluate_relation(relation, assignment): return {'result': [11]}\n")
            def check_code(command, cwd, timeout):
                if "-c" in command and "computed =" in command[-1]:
                    return real_run([sys.executable, "-O", "-B", "-c", command[-1]], cwd, timeout)
                return runner(command, cwd, timeout)
            report = self.diagnose(root, s31, check_code)
            self.assertFalse(report["passed"])
            row = next(row for row in report["checks"] if row["id"] == "frontend-oracle")
            self.assertEqual(row["status"], "fail")
            self.assertIn("unexpected result", row["detail"])

    def test_timeout_and_bounded_error_output(self):
        with self.assertRaisesRegex(RuntimeError, "timed out"):
            doctor.run([sys.executable, "-c", "import time; time.sleep(10)"], S31, 0.05)
        _, output = doctor.run([sys.executable, "-c", "print('x' * 20000)"], S31, 5)
        self.assertLess(len(output), 8100)
        self.assertIn("truncated", output)

    @unittest.skipUnless(sys.platform != "win32", "POSIX process-group cleanup")
    def test_timeout_terminates_build_children(self):
        with tempfile.TemporaryDirectory() as temporary:
            marker = Path(temporary) / "child-finished"
            child = "import time; from pathlib import Path; time.sleep(0.5); Path(" + repr(str(marker)) + ").touch()"
            parent = "import subprocess, sys, time; subprocess.Popen([sys.executable, '-c', " + repr(child) + "]); time.sleep(30)"
            with self.assertRaisesRegex(RuntimeError, "timed out"):
                doctor.run([sys.executable, "-c", parent], S31, 0.2)
            time.sleep(0.6)
            self.assertFalse(marker.exists(), "Timed-out build child survived")

    def test_argument_validation(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            doctor.main(["--timeout", "0"])
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
            doctor.main(["--keep-artifacts"])


if __name__ == "__main__":
    unittest.main()
