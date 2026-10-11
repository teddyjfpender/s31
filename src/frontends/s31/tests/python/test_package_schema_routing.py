"""Package schema routing and cache controls without native compilation."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package import build as package_build
from package.context import sha256


class PackageSchemaRoutingTests(unittest.TestCase):
    def test_direct_gate_record_keeps_record_abi_schema(self) -> None:
        self.assertEqual(package_build._key_schema({"version": 1}, "direct-gate", None),
                         "s31-verification-key-direct-manifest-v2")
        self.assertEqual(package_build._key_schema({"version": 2}, "direct-gate", None),
                         "s31-verification-key-direct-record-v2")
        self.assertEqual(package_build._key_schema({"version": 2}, "direct-chip", None),
                         "s31-verification-key-direct-record-chip-v2")

    def test_cached_build_requires_requested_schema(self) -> None:
        cases = (
            (1, "s31-verification-key-direct-manifest-v1", False),
            (1, "s31-verification-key-direct-manifest-v2", True),
            (2, "s31-verification-key-direct-manifest-v2", False),
            (2, "s31-verification-key-direct-record-v2", True),
        )
        with tempfile.TemporaryDirectory(prefix="s31-package-schema-") as directory:
            work = Path(directory)
            for index, (version, cached_schema, accepted) in enumerate(cases):
                with self.subTest(version=version, cached_schema=cached_schema):
                    source = work / f"source-{index}.s31.json"
                    source.write_text(json.dumps({"version": version, "name": "routing"}))
                    output = work / f"package-{index}"
                    output.mkdir()
                    (output / "verification-key.json").write_text(json.dumps({"schema": cached_schema}))
                    manifest = {
                        "program_sha256": sha256(source.read_bytes()),
                        "compiler_sha256": "compiler-pin",
                        "lowering": "direct-gate",
                        "fri_fold_step": 1,
                    }
                    with (patch.object(package_build, "verify_package", return_value=manifest),
                          patch.object(package_build, "compiler_fingerprint", return_value="compiler-pin"),
                          patch.object(package_build, "abi", return_value={"boundary_sha256": "abi-pin"}),
                          patch.object(package_build, "invoke", side_effect=AssertionError("native build called"))):
                        if accepted:
                            self.assertEqual(package_build.build_json(source, output, "direct-gate"), output.resolve())
                        else:
                            with self.assertRaisesRegex(FileExistsError, "verification key schema"):
                                package_build.build_json(source, output, "direct-gate")

    def test_cached_text_build_rejects_old_gate_schema(self) -> None:
        with tempfile.TemporaryDirectory(prefix="s31-text-package-schema-") as directory:
            work = Path(directory)
            source = work / "routing.s31"
            source.write_text(
                "circuit routing(public x: [m31; 4]) -> public [m31; 4] { x }\n")
            _, normalized, _ = package_build.lower_text(source)
            output = work / "package"
            output.mkdir()
            (output / "verification-key.json").write_text(json.dumps({
                "schema": "s31-verification-key-direct-manifest-v1"}))
            manifest = {
                "source_text_sha256": sha256(source.read_bytes()),
                "program_sha256": sha256(normalized),
                "compiler_sha256": "compiler-pin",
                "lowering": "direct-gate",
                "fri_fold_step": 1,
            }
            with (patch.object(package_build, "verify_package", return_value=manifest),
                  patch.object(package_build, "compiler_fingerprint", return_value="compiler-pin"),
                  patch.object(package_build, "invoke", side_effect=AssertionError("native build called"))):
                with self.assertRaisesRegex(FileExistsError, "verification key schema"):
                    package_build.build_text(source, output, "direct-gate")


if __name__ == "__main__":
    unittest.main()
