"""The strict structural release path must run Lean before native verification."""

from __future__ import annotations

import json
import tempfile
import unittest
from contextlib import contextmanager
from pathlib import Path
from unittest.mock import patch

from scripts.release import structural_lean_release as release


class StructuralReleaseTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory(prefix="s31-structural-release-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.package = self.root / "package"
        self.package.mkdir()
        (self.package / "verification-key.json").write_text(json.dumps({
            "schema": "s31-verification-key-direct-manifest-v2"}))
        self.proof = self.root / "proof"
        self.statement = self.root / "statement"
        self.proof.write_bytes(b"proof")
        self.statement.write_bytes(b"statement")
        self.manifest = {"name": "example", "lowering": "direct-gate",
                         "text_frontend_version": 1,
                         "source_text_sha256": "a" * 64,
                         "artifacts": dict.fromkeys(release.REQUIRED, "b" * 64)}
        self.calls: list[str] = []

    @contextmanager
    def pinned(self, _path: Path, _digest: str):
        self.calls.append("pin-checker")
        yield self.root / "checker"

    @contextmanager
    def admitted(self, _package: Path, _pins: dict[str, str]):
        self.calls.append("admit-package")
        yield self.package, self.manifest

    @contextmanager
    def inputs(self, _proof: Path, _statement: Path | None):
        self.calls.append("capture-proof")
        yield self.proof, self.statement

    def native(self, _binary: str, *args: str) -> str:
        self.calls.append("native-key" if args[0] == "check-key" else "native-proof")
        return "accepted"

    def test_lean_runs_before_native_on_one_captured_snapshot(self) -> None:
        def checked(snapshot: Path, manifest: dict, checker: Path) -> None:
            self.assertEqual((snapshot, manifest, checker),
                             (self.package, self.manifest, self.root / "checker"))
            self.calls.append("lean-structural")

        with patch.object(release, "proof_inputs_snapshot", self.inputs), \
             patch.object(release, "_pinned_checker", self.pinned), \
             patch.object(release, "admitted_snapshot", self.admitted), \
             patch.object(release, "check_structural_snapshot", checked), \
             patch.object(release, "invoke", self.native):
            result = release.verify(self.package, self.proof, self.statement,
                                    {}, self.root / "checker", "a" * 64)
        self.assertEqual(result, "accepted")
        self.assertEqual(self.calls, ["capture-proof", "pin-checker",
                                      "admit-package", "lean-structural",
                                      "native-key", "native-proof"])

    def test_lean_rejection_prevents_native_dispatch(self) -> None:
        def rejected(*_args: object) -> None:
            self.calls.append("lean-rejected")
            raise ValueError("wrong tree")

        with patch.object(release, "proof_inputs_snapshot", self.inputs), \
             patch.object(release, "_pinned_checker", self.pinned), \
             patch.object(release, "admitted_snapshot", self.admitted), \
             patch.object(release, "check_structural_snapshot", rejected), \
             patch.object(release, "invoke", self.native):
            with self.assertRaisesRegex(ValueError, "wrong tree"):
                release.verify(self.package, self.proof, self.statement,
                               {}, self.root / "checker", "a" * 64)
        self.assertNotIn("native-key", self.calls)
        self.assertNotIn("native-proof", self.calls)

    def test_missing_artifact_and_record_v2_fail_closed(self) -> None:
        self.manifest["artifacts"].pop("typed-structural-derivation.json")
        with self.assertRaisesRegex(ValueError, "requires every"):
            release.check_structural_snapshot(self.package, self.manifest,
                                              self.root / "checker")
        self.manifest["artifacts"]["typed-structural-derivation.json"] = "b" * 64
        self.manifest["text_frontend_version"] = 2
        with self.assertRaisesRegex(ValueError, "direct-gate text package"):
            release.check_structural_snapshot(self.package, self.manifest,
                                              self.root / "checker")
        self.manifest["text_frontend_version"] = 1
        for name in release.REQUIRED:
            (self.package / name).write_bytes(b"{}\n")
        (self.package / "source.s31.json").write_bytes(b'{"version": 2}\n')
        with self.assertRaisesRegex(ValueError, "relation v1"):
            release.check_structural_snapshot(self.package, self.manifest,
                                              self.root / "checker")


if __name__ == "__main__":
    unittest.main()
