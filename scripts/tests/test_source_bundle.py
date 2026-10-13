"""Archive layout controls for the complete S31 source distribution."""

from __future__ import annotations

import io
import hashlib
import subprocess
import sys
import tarfile
import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

from scripts.release.source_bundle import (
    add_archive, bundle, checked_checkout, load_receipt,
    require_stable_v01_certificate,
)


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

    def test_checkout_rejects_engine_outside_pinned_gitlink(self) -> None:
        from scripts.release import source_bundle

        def fake_git(repository: Path, *args: str) -> str:
            if args == ("status", "--porcelain", "--untracked-files=normal"):
                return ""
            if args == ("rev-parse", "--show-toplevel"):
                return str(source_bundle.ENGINE)
            if args == ("rev-parse", "HEAD"):
                return "b" * 40 if repository == source_bundle.ENGINE else "a" * 40
            if args == ("rev-parse", "HEAD:deps/stwo-zig"):
                return "c" * 40
            raise AssertionError((repository, args))

        with mock.patch.object(source_bundle, "git", side_effect=fake_git):
            with self.assertRaisesRegex(RuntimeError, "pinned Gitlink"):
                checked_checkout()

    def test_candidate_bundle_rechecks_evidence_and_pins_receipt_hashes(self) -> None:
        from scripts.release import source_bundle

        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            receipts = [root / name for name in ("audit.json", "features.json", "formal.json")]
            for path in receipts:
                path.write_text(path.name)
            out = root / "candidate.tar.gz"
            source = "a" * 40
            engine = "b" * 40
            candidate = {"status": "scoped-candidate-gates-passed",
                         "candidate_commit": source, "engine_commit": engine,
                         "receipt_sha256": {
                             "audit": source_bundle.file_sha256(receipts[0]),
                             "features": source_bundle.file_sha256(receipts[1]),
                             "formal": source_bundle.file_sha256(receipts[2]),
                         }}
            with (mock.patch.object(source_bundle, "checked_checkout", return_value=(source, engine)),
                  mock.patch.object(source_bundle, "checked_candidate_evidence",
                                    return_value=candidate) as evidence,
                  mock.patch.object(source_bundle, "git", return_value="c" * 40),
                  mock.patch.object(source_bundle, "engine_source_digest", return_value="d" * 64),
                  mock.patch.object(source_bundle, "compiler_fingerprint", return_value="e" * 64),
                  mock.patch.object(source_bundle, "add_archive", return_value=0)):
                result = bundle("v0.1.0-rc.5", out, audit=receipts[0],
                                features=receipts[1], formal=receipts[2],
                                compiler_sha256="e" * 64, branch="release-rc5")
            evidence.assert_called_once()
            self.assertEqual(result["candidate_gate"]["status"],
                             "scoped-candidate-gates-passed")
            self.assertEqual(result["candidate_gate"]["audit_sha256"],
                             source_bundle.file_sha256(receipts[0]))
            with tarfile.open(out, "r:gz") as archive:
                self.assertEqual(archive.getmember("s31-v0.1.0-rc.5/SOURCE-BUNDLE.json").name,
                                 "s31-v0.1.0-rc.5/SOURCE-BUNDLE.json")

    def test_receipt_hash_covers_exact_parsed_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "receipt.json"
            path.write_bytes(b'{"status":"passed"}\n')
            report, digest = load_receipt(path)
            self.assertEqual(report, {"status": "passed"})
            self.assertEqual(digest, hashlib.sha256(path.read_bytes()).hexdigest())
            link = path.with_name("receipt-link.json")
            link.symlink_to(path.name)
            with self.assertRaisesRegex(ValueError, "may not be a symlink"):
                load_receipt(link)

    def test_candidate_identity_mismatch_does_not_create_archive(self) -> None:
        from scripts.release import source_bundle

        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary) / "candidate.tar.gz"
            with (mock.patch.object(source_bundle, "checked_checkout", return_value=("a" * 40, "b" * 40)),
                  mock.patch.object(source_bundle, "checked_candidate_evidence", return_value={
                      "candidate_commit": "c" * 40, "engine_commit": "b" * 40,
                  })):
                with self.assertRaisesRegex(RuntimeError, "does not identify"):
                    bundle("v0.1.0-rc.5", out, audit=out, features=out,
                           formal=out, compiler_sha256="e" * 64, branch="release-rc5")
            self.assertFalse(out.exists())

    def test_stable_bundle_cannot_be_written_with_candidate_only_evidence(self) -> None:
        from scripts.release import source_bundle

        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary) / "stable.tar.gz"
            with (mock.patch.object(source_bundle, "checked_checkout", return_value=("a" * 40, "b" * 40)),
                  mock.patch.object(source_bundle, "checked_candidate_evidence", return_value={
                      "candidate_commit": "a" * 40, "engine_commit": "b" * 40,
                  }),
                  mock.patch.object(source_bundle, "require_stable_v01_certificate",
                                    side_effect=RuntimeError("native PCS/FRI open")) as security):
                with self.assertRaisesRegex(RuntimeError, "native PCS/FRI open"):
                    bundle("v0.1.0", out, audit=out, features=out,
                           formal=out, compiler_sha256="e" * 64, branch="release")
            security.assert_called_once()
            self.assertFalse(out.exists())

    def test_unreviewed_release_tag_is_rejected_before_checkout(self) -> None:
        from scripts.release import source_bundle

        with mock.patch.object(source_bundle, "checked_checkout") as checkout:
            with self.assertRaisesRegex(ValueError, "source bundle tag"):
                bundle("v0.1.0-rc.test", Path("unused.tar.gz"), audit=Path("unused"),
                       features=Path("unused"), formal=Path("unused"),
                       compiler_sha256="e" * 64, branch="release")
        checkout.assert_not_called()

    def test_stable_tag_requires_proven_native_and_general_compiler_certificates(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            matrix_path = Path(temporary) / "matrix.json"
            report = {"proven_release_admissible": False}
            matrix_path.write_text("matrix")
            fake = types.ModuleType("scripts.release.pcs_fri_v01_blockers")
            fake.MATRIX = matrix_path
            fake.encoded = lambda value: "matrix"
            fake.matrix = lambda root: report
            with mock.patch.dict(sys.modules, {fake.__name__: fake}):
                fake.encoded = lambda value: "changed evidence"
                with self.assertRaisesRegex(RuntimeError, "current reviewed PCS/FRI matrix"):
                    require_stable_v01_certificate()
                fake.encoded = lambda value: "matrix"
                with self.assertRaisesRegex(RuntimeError, "proven native PCS/FRI"):
                    require_stable_v01_certificate()
                report["proven_release_admissible"] = True
                with self.assertRaisesRegex(RuntimeError, "general compiler correspondence"):
                    require_stable_v01_certificate()


if __name__ == "__main__":
    unittest.main()
