"""A Git-free engine cannot inherit an enclosing checkout's identity."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package import source_identity


class SourceBundleIdentityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory(prefix="s31-source-identity-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.engine = self.root / "deps/stwo-zig"
        (self.engine / "src").mkdir(parents=True)
        (self.engine / "src/engine.zig").write_text("pub const value = 1;\n")
        (self.engine / "build.zig").write_text("pub fn build() void {}\n")

    def fixture(self) -> None:
        manifest = {
            "schema": "s31-complete-source-bundle-v1",
            "engine_commit": "a" * 40,
            "engine_source_sha256": source_identity.engine_source_digest(self.engine),
        }
        (self.root / "SOURCE-BUNDLE.json").write_text(json.dumps(manifest))

    def test_missing_manifest_does_not_fall_through_to_parent_git(self) -> None:
        with patch.object(source_identity, "_ENGINE_SOURCE_DIRS", ("src",)), patch.object(
            source_identity, "_ENGINE_SOURCE_FILES", ("build.zig",)
        ), patch.object(source_identity.subprocess, "check_output",
                        side_effect=AssertionError("must not ask parent Git")):
            with self.assertRaisesRegex(RuntimeError, "no own Git worktree"):
                source_identity.pinned_engine_commit(self.root, self.engine)

    def test_manifest_binds_engine_source_and_commit(self) -> None:
        with patch.object(source_identity, "_ENGINE_SOURCE_DIRS", ("src",)), patch.object(
            source_identity, "_ENGINE_SOURCE_FILES", ("build.zig",)
        ), patch.object(source_identity.subprocess, "check_output",
                        side_effect=AssertionError("bundle must not query Git")):
            self.fixture()
            self.assertEqual(source_identity.pinned_engine_commit(self.root, self.engine),
                             "a" * 40)
            (self.engine / "src/engine.zig").write_text("pub const value = 2;\n")
            with self.assertRaisesRegex(RuntimeError, "differs from its pinned manifest"):
                source_identity.pinned_engine_commit(self.root, self.engine)

    def test_git_marker_must_name_engine_worktree(self) -> None:
        (self.engine / ".git").write_text("gitdir: ../../.git\n")
        with patch.object(source_identity.subprocess, "check_output",
                          return_value=str(self.root)):
            with self.assertRaisesRegex(RuntimeError, "not its own root"):
                source_identity.pinned_engine_commit(self.root, self.engine)


if __name__ == "__main__":
    unittest.main()
