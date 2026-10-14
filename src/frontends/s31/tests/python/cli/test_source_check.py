"""Source-only CLI diagnostics and reproducible relation identity."""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from cli.source_check import check_source, render_source_check
from package.context import lower_text


class SourceCheckTests(unittest.TestCase):
    def test_valid_check_matches_build_relation_without_native_tool(self) -> None:
        source = S31 / "examples/arithmetic/arith4_m31.s31"
        with patch("package.context.invoke", side_effect=AssertionError("native tool called")):
            report = check_source(source)
        relation, encoded, _ = lower_text(source)
        self.assertEqual(report["status"], "valid")
        self.assertEqual(report["program"], relation["name"])
        self.assertEqual(report["relation_nodes"], len(relation["nodes"]))
        self.assertEqual(report["relation_sha256"], hashlib.sha256(encoded).hexdigest())

    def test_invalid_source_has_location_and_machine_readable_exit(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s31-cli-source-check-") as directory:
            source = Path(directory) / "bad.s31"
            source.write_text("circuit bad(public x: [m31; 1]) -> public [m31; 1] {\n    x +\n}\n")
            cli = S31 / "python/s31.py"
            process = subprocess.run(
                [sys.executable, str(cli), "check-source", str(source), "--json"],
                capture_output=True, text=True, check=False,
            )
            self.assertEqual(process.returncode, 1)
            self.assertEqual(process.stderr, "")
            report = json.loads(process.stdout)
            self.assertEqual(report["schema"], "s31-source-check-v1")
            self.assertEqual(report["status"], "invalid")
            self.assertEqual(report["diagnostic"]["line"], 3)
            self.assertEqual(report["diagnostic"]["column"], 1)
            self.assertIn("expected expression", report["diagnostic"]["message"])
            self.assertIn("^", render_source_check(report))

    def test_missing_file_and_wrong_extension_are_diagnostics(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s31-cli-source-check-") as directory:
            folder = Path(directory)
            for source, expected in ((folder / "missing.s31", "No such file"),
                                     (folder / "wrong.txt", "expects a .s31")):
                with self.subTest(source=source):
                    report = check_source(source)
                    self.assertEqual(report["status"], "invalid")
                    self.assertIn(expected, report["diagnostic"]["message"])
                    self.assertIsNone(report["diagnostic"]["line"])


if __name__ == "__main__":
    unittest.main()
