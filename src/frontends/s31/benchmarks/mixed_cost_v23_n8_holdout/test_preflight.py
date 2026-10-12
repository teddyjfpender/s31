"""Static controls for the V23 host-idle parser; no native prover is run."""

from __future__ import annotations

import unittest
from unittest.mock import patch
from subprocess import CompletedProcess

import study


class PreflightParserTests(unittest.TestCase):
    def test_space_containing_command_and_decimal_cpu(self) -> None:
        rows = (b"  532   0.0 Core Audio Driver\n"
                b"  624  10.1 /Library/SystemExtensions/io.kandji.KandjiAgent\n"
                b" 1419  17.0 /Users/test/bin/codex app-server\n")
        self.assertEqual(study.blockers(rows, exempt_pid=777), [])

    def test_high_cpu_and_compilers_are_blocked(self) -> None:
        rows = (b"  11  25.0 /usr/bin/python3\n"
                b"  12   0.0 /usr/local/bin/zig\n"
                b"  13  24.9 /usr/bin/python3\n")
        self.assertEqual(study.blockers(rows, exempt_pid=777),
                         ["  11  25.0 /usr/bin/python3", "  12   0.0 /usr/local/bin/zig"])
        self.assertEqual(study.blockers(b"  11  99.0 /usr/bin/python3\n", exempt_pid=11), [])

    def test_two_snapshots_are_required(self) -> None:
        quiet = CompletedProcess([], 0, b"  10  17.0 /usr/bin/codex\n", b"")
        busy = CompletedProcess([], 0, b"  11  25.0 /usr/bin/python3\n", b"")
        with patch.object(study.subprocess, "run", side_effect=[quiet, quiet]) as run, \
                patch.object(study.time, "sleep") as sleep:
            self.assertEqual(study.quiet_host_snapshot(), quiet.stdout + b"\n" + quiet.stdout)
            self.assertEqual(run.call_count, 2)
            sleep.assert_called_once_with(1)
        with patch.object(study.subprocess, "run", side_effect=[quiet, busy]), \
                patch.object(study.time, "sleep"):
            with self.assertRaisesRegex(RuntimeError, "busy CPU"):
                study.quiet_host_snapshot()


if __name__ == "__main__":
    unittest.main()
