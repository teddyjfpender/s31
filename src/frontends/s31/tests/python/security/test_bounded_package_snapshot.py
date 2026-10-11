"""Package admission must bound untrusted bytes before validating or running code."""

from __future__ import annotations

import hashlib
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.trust import admitted_snapshot, pinned_paths  # noqa: E402


class BoundedPackageSnapshotTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="s31-bounded-package-")
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name) / "package"
        (self.package / "bin").mkdir(parents=True)
        (self.package / "manifest.json").write_text(json.dumps({"name": "bounded"}))
        for name, content in (
            ("source.s31.json", b"relation"),
            ("verification-key.json", b"key"),
            ("bin/s31-bounded-prover", b"prover"),
            ("bin/s31-bounded-native-verifier", b"verifier"),
        ):
            (self.package / name).write_bytes(content)
        (self.package / "bin/s31-bounded-native-verifier").chmod(0o755)
        self.pins = {kind: hashlib.sha256(path.read_bytes()).hexdigest()
                     for kind, path in pinned_paths(self.package).items()}

    def test_unlisted_sidecar_exceeding_byte_cap_fails_before_validation(self) -> None:
        (self.package / "unlisted.sidecar").write_bytes(b"x" * 64)
        original_bytes = sum(path.stat().st_size for path in self.package.rglob("*")
                             if path.is_file()) - 64
        with patch("package.trust.MAX_PACKAGE_BYTES", original_bytes + 16), \
                patch("package.trust.verify_package") as validate:
            with self.assertRaisesRegex(ValueError, "byte limit"):
                with admitted_snapshot(self.package, self.pins):
                    self.fail("oversized unlisted file admitted")
        validate.assert_not_called()

    def test_single_file_cap_stops_large_copy_even_when_aggregate_cap_allows_it(self) -> None:
        (self.package / "unlisted.sidecar").write_bytes(b"x" * 64)
        with patch("package.trust.MAX_PACKAGE_FILE_BYTES", 32), \
                patch("package.trust.verify_package") as validate:
            with self.assertRaisesRegex(ValueError, "byte limit"):
                with admitted_snapshot(self.package, self.pins):
                    self.fail("oversized file admitted")
        validate.assert_not_called()

    def test_entry_cap_stops_deep_unlisted_tree(self) -> None:
        for index in range(8):
            (self.package / f"unlisted-{index}").mkdir()
        with patch("package.trust.MAX_PACKAGE_ENTRIES", 4), \
                patch("package.trust.verify_package") as validate:
            with self.assertRaisesRegex(ValueError, "entry limit"):
                with admitted_snapshot(self.package, self.pins):
                    self.fail("oversized directory tree admitted")
        validate.assert_not_called()

    def test_regular_admission_preserves_verifier_execute_bit(self) -> None:
        with patch("package.trust.verify_package", return_value={"name": "bounded"}):
            with admitted_snapshot(self.package, self.pins) as (snapshot, _manifest):
                executable = snapshot / "bin/s31-bounded-native-verifier"
                self.assertTrue(executable.stat().st_mode & 0o111)
                self.assertEqual(executable.read_bytes(), b"verifier")


if __name__ == "__main__":
    unittest.main()
