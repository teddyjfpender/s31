"""Fail-closed tests for the executed formal release receipt."""

from __future__ import annotations

import contextlib
import io
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from scripts.release import formal_receipt


class FormalReceiptTests(unittest.TestCase):
    def setUp(self) -> None:
        self.enterContext(contextlib.redirect_stderr(io.StringIO()))
        self.temporary = tempfile.TemporaryDirectory(prefix="s31-formal-receipt-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "formal/s31").mkdir(parents=True)
        self.out = self.root / "receipt.json"
        self.logs = self.root / "logs"
        self.clean = formal_receipt.Snapshot("a" * 40, "b" * 64,
                                             "c" * 64, "d" * 64, True)

    def fake_execute(self, command: list[str], *, cwd: Path, stdout,
                     stderr, env: dict[str, str], check: bool) -> subprocess.CompletedProcess:
        self.assertEqual(env["LEAN_NUM_THREADS"], "1")
        self.assertEqual(stderr, subprocess.STDOUT)
        self.assertFalse(check)
        self.assertEqual(cwd, self.root if command[0] == "python3"
                         else self.root / "formal/s31")
        stdout.write((" ".join(command) + ": OK\n").encode())
        return subprocess.CompletedProcess(command, 0)

    def test_success_records_real_logs_and_exact_command_order(self) -> None:
        calls: list[list[str]] = []

        def execute(command: list[str], **kwargs) -> subprocess.CompletedProcess:
            calls.append(command)
            return self.fake_execute(command, **kwargs)

        result = formal_receipt.run(self.out, self.logs, root=self.root,
                                    take_snapshot=lambda _: self.clean, execute=execute)
        self.assertEqual(result["status"], "passed")
        self.assertEqual(calls, list(formal_receipt.FORMAL_COMMANDS.values()))
        self.assertEqual(json.loads(self.out.read_text()), result)
        for name, row in result["checks"].items():
            self.assertEqual(row["command"], formal_receipt.FORMAL_COMMANDS[name])
            self.assertEqual(row["log_sha256"], formal_receipt.digest(Path(row["log"])))

    def test_failure_stops_before_later_checks(self) -> None:
        def execute(command: list[str], **kwargs) -> subprocess.CompletedProcess:
            self.fake_execute(command, **kwargs)
            return subprocess.CompletedProcess(command, 9 if command[0] == "lake" else 0)

        result = formal_receipt.run(self.out, self.logs, root=self.root,
                                    take_snapshot=lambda _: self.clean, execute=execute)
        self.assertEqual(result["status"], "failed")
        self.assertEqual(result["failure"], "lake_build exited 9")
        self.assertEqual(list(result["checks"]), ["bindings", "lake_build"])

    def test_source_drift_fails_even_if_every_command_exits_zero(self) -> None:
        changed = formal_receipt.Snapshot(self.clean.commit, "e" * 64,
                                          self.clean.inventory, self.clean.bindings, True)
        states = iter([self.clean, self.clean, changed])
        result = formal_receipt.run(self.out, self.logs, root=self.root,
                                    take_snapshot=lambda _: next(states),
                                    execute=self.fake_execute)
        self.assertEqual(result["status"], "failed")
        self.assertIn("drift", result["failure"])
        self.assertEqual(list(result["checks"]), ["bindings", "lake_build"])

    def test_dirty_or_symlinked_output_is_rejected_before_execution(self) -> None:
        dirty = formal_receipt.Snapshot(self.clean.commit, self.clean.compiler,
                                        self.clean.inventory, self.clean.bindings, False)
        with self.assertRaisesRegex(ValueError, "clean"):
            formal_receipt.run(self.out, self.logs, root=self.root,
                               take_snapshot=lambda _: dirty, execute=self.fake_execute)
        target = self.root / "target.json"
        target.write_text("{}")
        self.out.symlink_to(target)
        with self.assertRaisesRegex(ValueError, "symlinks"):
            formal_receipt.run(self.out, self.logs, root=self.root,
                               take_snapshot=lambda _: self.clean, execute=self.fake_execute)


if __name__ == "__main__":
    unittest.main()
