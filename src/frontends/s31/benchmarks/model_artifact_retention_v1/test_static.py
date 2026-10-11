#!/usr/bin/env python3
"""Native-free tests for the future-study frozen-model artifact gate."""

from __future__ import annotations

import hashlib
import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from retain import check, seal


class ModelRetention(unittest.TestCase):
    def test_requires_exact_bytes_in_ancestor_commit(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            repo = base / "repo"
            repo.mkdir()
            subprocess.run(["git", "init", "-q", str(repo)], check=True)
            source = base / "training-model.json"
            source.write_bytes(b'{"fits":{},"schema":"test-model"}\n')
            model_sha = hashlib.sha256(source.read_bytes()).hexdigest()
            protocol_sha = "a" * 64
            artifact = repo / "design/s31/measurements/language/model-artifacts/model.json"
            manifest = artifact.with_name("manifest.json")
            sealed = seal(source, artifact, manifest, model_sha, protocol_sha, repo)
            self.assertEqual(sealed["model_sha256"], model_sha)
            with self.assertRaises(ValueError):
                check(manifest, model_sha, protocol_sha, "0" * 40, repo)
            subprocess.run(["git", "-C", str(repo), "add", "design"], check=True)
            subprocess.run(["git", "-C", str(repo), "-c", "user.name=Retention Test",
                            "-c", "user.email=retention@example.invalid", "commit", "-qm",
                            "Anchor exact model bytes"], check=True)
            anchor = subprocess.check_output(["git", "-C", str(repo),
                                               "rev-parse", "HEAD"], text=True).strip()
            self.assertEqual(check(manifest, model_sha, protocol_sha, anchor, repo)["status"],
                             "committed_model_bytes_verified_before_heldout")
            artifact.write_bytes(artifact.read_bytes() + b" ")
            with self.assertRaisesRegex(ValueError, "retained frozen model bytes"):
                check(manifest, model_sha, protocol_sha, anchor, repo)
            artifact.write_bytes(source.read_bytes())
            changed = json.loads(manifest.read_bytes())
            changed["artifact_bytes"] += 1
            manifest.write_text(json.dumps(changed, sort_keys=True, separators=(",", ":")) + "\n")
            with self.assertRaisesRegex(ValueError, "retained frozen model bytes"):
                check(manifest, model_sha, protocol_sha, anchor, repo)
            with self.assertRaises(ValueError):
                seal(source, artifact, manifest, model_sha, protocol_sha, repo)

    def test_rejects_bad_source_and_path_escape(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            base = Path(temp)
            repo = base / "repo"
            repo.mkdir()
            source = base / "bad.json"
            source.write_bytes(b'{"schema":"one","schema":"two"}\n')
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
                seal(source, repo / "model.json", repo / "manifest.json",
                     digest, "b" * 64, repo)
            source.write_bytes(b'{"schema":"okay"}\n')
            digest = hashlib.sha256(source.read_bytes()).hexdigest()
            with self.assertRaisesRegex(ValueError, "inside the repository"):
                seal(source, base / "outside.json", repo / "manifest.json",
                     digest, "b" * 64, repo)


if __name__ == "__main__":
    unittest.main()
