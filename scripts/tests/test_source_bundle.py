"""Archive layout controls for the complete S31 source distribution."""

from __future__ import annotations

import io
import subprocess
import tarfile
import tempfile
import unittest
from pathlib import Path

from scripts.release.source_bundle import add_archive


def git(repository: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repository), *args], text=True,
        stderr=subprocess.DEVNULL,
    ).strip()


class SourceBundleArchiveTests(unittest.TestCase):
    def repository(self, root: Path) -> Path:
        repository = root / "source"
        repository.mkdir()
        git(repository, "init", "-q")
        return repository

    def commit(self, repository: Path) -> str:
        git(repository, "add", ".")
        git(repository, "-c", "user.name=S31 Test",
            "-c", "user.email=s31-test@example.invalid", "commit", "-qm", "fixture")
        return git(repository, "rev-parse", "HEAD")

    def archive(self, repository: Path, commit: str, prefix: str) -> tarfile.TarFile:
        output = io.BytesIO()
        with tarfile.open(fileobj=output, mode="w", format=tarfile.PAX_FORMAT) as target:
            add_archive(target, repository, commit, prefix)
        output.seek(0)
        return tarfile.open(fileobj=output, mode="r")

    def test_long_pax_path_keeps_bundle_prefix_and_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repository = self.repository(Path(temporary))
            relative = "/".join(["long_" + "x" * 70] * 4) + "/value.cu"
            source = repository / relative
            source.parent.mkdir(parents=True)
            source.write_bytes(b"tracked research file\n")
            commit = self.commit(repository)
            prefix = "s31-v0.1.0-rc.test/deps/stwo-zig/"
            with self.archive(repository, commit, prefix) as result:
                names = result.getnames()
                self.assertTrue(all(name.startswith(prefix) for name in names))
                member = result.getmember(prefix + relative)
                self.assertEqual(result.extractfile(member).read(), source.read_bytes())
                self.assertEqual(member.pax_headers.get("path"), prefix + relative)

    def test_relative_symlink_stays_inside_bundle(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repository = self.repository(Path(temporary))
            target = repository / "deps" / "engine" / "source.txt"
            target.parent.mkdir(parents=True)
            target.write_text("source\n")
            link = repository / "formal" / "engine"
            link.parent.mkdir()
            link.symlink_to("../deps/engine")
            commit = self.commit(repository)
            with self.archive(repository, commit, "s31-test/") as result:
                member = result.getmember("s31-test/formal/engine")
                self.assertTrue(member.issym())
                self.assertEqual(member.linkname, "../deps/engine")

    def test_symlink_escaping_bundle_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            repository = self.repository(Path(temporary))
            (repository / "bad-link").symlink_to("../../outside")
            commit = self.commit(repository)
            with tarfile.open(fileobj=io.BytesIO(), mode="w", format=tarfile.PAX_FORMAT) as target:
                with self.assertRaisesRegex(RuntimeError, "symlink escapes source bundle"):
                    add_archive(target, repository, commit, "s31-test/")


if __name__ == "__main__":
    unittest.main()
