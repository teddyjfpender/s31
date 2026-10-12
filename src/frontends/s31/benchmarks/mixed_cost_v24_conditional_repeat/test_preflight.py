"""Static controls for the V24 host-idle parser; no native prover is run."""

from __future__ import annotations

import unittest
import importlib.util
from pathlib import Path
from unittest.mock import patch
from subprocess import CompletedProcess

import study

_audit_spec = importlib.util.spec_from_file_location("v24_test_audit", Path(__file__).with_name("audit.py"))
if _audit_spec is None or _audit_spec.loader is None:
    raise RuntimeError("V24 audit module unavailable")
audit = importlib.util.module_from_spec(_audit_spec)
_audit_spec.loader.exec_module(audit)


class PreflightParserTests(unittest.TestCase):
    def test_independent_audit_rejects_tampered_extra_gate_flags(self) -> None:
        gates = {"wall_one_draw_hits_min": 14, "proof_interval_hits_min": 16}
        valid = {"sample20_wall_median_in_band": True,
                 "wall_one_draw_hits": True, "proof_interval_hits": True}
        metrics = {"wall_sample20_median_in_band": True,
                   "wall_one_draw_interval_hits": 14,
                   "proof_interval_coverage": 16 / 20}
        audit.check_extra_gates(valid, metrics, gates)
        for field, value in (("wall_sample20_median_in_band", False),
                             ("wall_one_draw_interval_hits", 13),
                             ("proof_interval_coverage", 15 / 20)):
            changed = {**metrics, field: value}
            with self.subTest(field=field), self.assertRaisesRegex(
                    ValueError, "independently recomputed"):
                audit.check_extra_gates(valid, changed, gates)

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
