"""Reject attempts to reinterpret a text package as an unbound JSON package."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.verify import verify_package  # noqa: E402


class TextPackageBindingTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="s31-text-binding-")
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name)
        self.manifest = {
            "schema": "s31-package-v1",
            "name": "example",
            "artifacts": {
                "source.s31.json": "0" * 64,
                "verification-key.json": "0" * 64,
                "public-abi.json": "0" * 64,
                "cost-report.json": "0" * 64,
                "bin/s31-example-prover": "0" * 64,
                "bin/s31-example-native-verifier": "0" * 64,
            },
        }

    def check_rejected(self, message: str) -> None:
        (self.package / "manifest.json").write_text(json.dumps(self.manifest))
        with self.assertRaisesRegex(ValueError, message):
            verify_package(self.package)

    def test_unlisted_text_source_cannot_bypass_source_binding(self) -> None:
        (self.package / "source.s31").write_text("circuit example() -> public m31 { 1 }\n")
        self.check_rejected("text artifacts require source binding metadata")

    def test_listed_text_artifact_cannot_bypass_source_binding(self) -> None:
        self.manifest["artifacts"]["source-map.json"] = "0" * 64
        self.check_rejected("text artifacts require source binding metadata")

    def test_unlisted_broken_text_symlink_cannot_bypass_source_binding(self) -> None:
        (self.package / "source.s31").symlink_to("missing.s31")
        self.check_rejected("text artifacts require source binding metadata")

    def test_text_source_cannot_downgrade_frontend_version(self) -> None:
        self.manifest["source_text_sha256"] = "0" * 64
        for version in (None, 0, 2, "1", True, 1.0):
            with self.subTest(version=version):
                if version is None:
                    self.manifest.pop("text_frontend_version", None)
                else:
                    self.manifest["text_frontend_version"] = version
                self.check_rejected("text package requires frontend version 1")

    def test_relation_version_requires_integer_json_type(self) -> None:
        for version in (True, 1.0, 2.0):
            with self.subTest(version=version):
                (self.package / "source.s31.json").write_text(
                    json.dumps({"version": version, "name": "example"}))
                self.check_rejected("unsupported S31 relation version")


if __name__ == "__main__":
    unittest.main()
