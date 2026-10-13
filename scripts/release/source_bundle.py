#!/usr/bin/env python3
"""Package checked S31 v0.1 developer candidates without Git metadata.

GitHub's source archives omit submodules.  The bundle carries both complete
tracked trees and a manifest that the Git-free compiler validates before it
uses the pinned engine commit in a package fingerprint. The stable v0.1.0 tag
stays closed until native PCS/FRI and general compiler correspondence have
source-bound release certificates.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import posixpath
import re
import subprocess
import sys
import tarfile
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[2]
ENGINE = ROOT / "deps/stwo-zig"
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.context import compiler_fingerprint  # noqa: E402
from package.source_identity import engine_source_digest  # noqa: E402

sys.path.insert(0, str(ROOT))
from scripts.release import release_candidate  # noqa: E402

V01_TAG = re.compile(r"v0\.1\.0(?:-rc\.[1-9][0-9]*)?\Z")


def git(repository: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repository), *args], text=True,
    ).strip()


def add_archive(target: tarfile.TarFile, repository: Path, commit: str,
                prefix: str) -> int:
    proc = subprocess.Popen(
        ["git", "-C", str(repository), "archive", "--format=tar", commit],
        stdout=subprocess.PIPE,
    )
    assert proc.stdout is not None
    count = 0
    try:
        with tarfile.open(fileobj=proc.stdout, mode="r|") as archive:
            for entry in archive:
                source_path = PurePosixPath(entry.name)
                if (not source_path.parts or source_path.is_absolute() or
                        ".." in source_path.parts or
                        not (entry.isfile() or entry.isdir() or entry.issym())):
                    raise RuntimeError(f"unsafe Git archive entry: {entry.name}")
                # Extract before rewriting the header. Git archive may carry a
                # PAX `path` field for long names, which otherwise overrides
                # TarInfo.name when the outer archive is written.
                contents = archive.extractfile(entry) if entry.isfile() else None
                entry.name = prefix + entry.name
                if entry.issym():
                    target_path = posixpath.normpath(posixpath.join(
                        posixpath.dirname(entry.name), entry.linkname))
                    root = prefix.rstrip("/")
                    if target_path != root and not target_path.startswith(root + "/"):
                        raise RuntimeError(f"symlink escapes source bundle: {entry.name}")
                entry.pax_headers = {}
                entry.uid = entry.gid = 0
                entry.uname = entry.gname = ""
                target.addfile(entry, contents)
                count += 1
    finally:
        proc.stdout.close()
        status = proc.wait()
    if status != 0:
        raise RuntimeError(f"git archive failed for {repository}")
    return count


def add_bytes(target: tarfile.TarFile, name: str, value: bytes) -> None:
    entry = tarfile.TarInfo(name)
    entry.size = len(value)
    entry.mtime = 0
    entry.mode = 0o644
    entry.uid = entry.gid = 0
    entry.uname = entry.gname = ""
    target.addfile(entry, io.BytesIO(value))


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_receipt(path: Path) -> tuple[dict, str]:
    """Parse and hash the same bytes, so the manifest pins checked evidence."""
    if path.is_symlink():
        raise ValueError(f"release receipt may not be a symlink: {path}")
    raw = path.read_bytes()
    value = json.loads(raw)
    if not isinstance(value, dict):
        raise ValueError(f"release receipt must be a JSON object: {path}")
    return value, hashlib.sha256(raw).hexdigest()


def checked_checkout() -> tuple[str, str]:
    """Return the exact clean S31 commit and its checked-out Gitlink engine."""
    if git(ROOT, "status", "--porcelain", "--untracked-files=normal"):
        raise RuntimeError("S31 source worktree must be clean")
    if git(ENGINE, "status", "--porcelain", "--untracked-files=normal"):
        raise RuntimeError("stwo-zig engine worktree must be clean")
    if Path(git(ENGINE, "rev-parse", "--show-toplevel")).resolve() != ENGINE.resolve():
        raise RuntimeError("stwo-zig must be its own Git worktree")

    source_commit = git(ROOT, "rev-parse", "HEAD")
    engine_commit = git(ENGINE, "rev-parse", "HEAD")
    if engine_commit != git(ROOT, "rev-parse", "HEAD:deps/stwo-zig"):
        raise RuntimeError("stwo-zig checkout differs from the S31 commit's pinned Gitlink")
    return source_commit, engine_commit


def checked_candidate_evidence(*, audit: Path, features: Path, formal: Path,
                               compiler_sha256: str, branch: str, remote: str) -> dict:
    """Recheck the candidate receipts and live remote identity before archiving."""
    audit_report, audit_pin = load_receipt(audit)
    feature_report, feature_pin = load_receipt(features)
    formal_report, formal_pin = load_receipt(formal)
    identity = release_candidate.validate_reports(
        audit_report, feature_report, formal_report,
        compiler=compiler_sha256, root=ROOT,
    )
    candidate = release_candidate.validate_live_identity(
        identity, root=ROOT, remote=remote, branch=branch,
    )
    return {**candidate, "receipt_sha256": {
        "audit": audit_pin, "features": feature_pin, "formal": formal_pin,
    }}


def require_stable_v01_certificate() -> None:
    """Keep the final tag closed until both general proof obligations are gated."""
    from scripts.release.pcs_fri_v01_blockers import MATRIX, encoded, matrix

    report = matrix(ROOT)
    if not MATRIX.is_file() or MATRIX.read_text() != encoded(report):
        raise RuntimeError("stable v0.1.0 requires a current reviewed PCS/FRI matrix")
    if report.get("proven_release_admissible") is not True:
        raise RuntimeError("stable v0.1.0 requires a proven native PCS/FRI certificate")
    # The scoped candidate checker covers finitely many examples. No release
    # checker yet certifies the whole production compiler for all admitted
    # programs; a new source-bound checker must replace this closed gate.
    raise RuntimeError("stable v0.1.0 requires a general compiler correspondence certificate")


def bundle(tag: str, out: Path, *, audit: Path, features: Path, formal: Path,
           compiler_sha256: str, branch: str, remote: str = "origin") -> dict:
    if not V01_TAG.fullmatch(tag):
        raise ValueError("source bundle tag must be v0.1.0-rc.N or v0.1.0")
    source_commit, engine_commit = checked_checkout()
    candidate = checked_candidate_evidence(
        audit=audit, features=features, formal=formal,
        compiler_sha256=compiler_sha256, branch=branch, remote=remote,
    )
    if candidate["candidate_commit"] != source_commit or candidate["engine_commit"] != engine_commit:
        raise RuntimeError("candidate evidence does not identify the bundled source and engine")
    if tag == "v0.1.0":
        require_stable_v01_certificate()
    manifest = {
        "schema": "s31-complete-source-bundle-v1",
        "tag": tag,
        "source_commit": source_commit,
        "source_tree": git(ROOT, "rev-parse", "HEAD^{tree}"),
        "engine_commit": engine_commit,
        "engine_tree": git(ENGINE, "rev-parse", "HEAD^{tree}"),
        "engine_source_sha256": engine_source_digest(ENGINE),
        "compiler_sha256": compiler_fingerprint(),
        "candidate_gate": {
            "status": candidate["status"],
            "audit_sha256": candidate["receipt_sha256"]["audit"],
            "features_sha256": candidate["receipt_sha256"]["features"],
            "formal_sha256": candidate["receipt_sha256"]["formal"],
        },
        "scope": "complete tracked S31 and pinned stwo-zig trees",
    }
    readme = (
        f"# S31 {tag} complete source bundle\n\n"
        "This contains both complete tracked source trees, without Git metadata "
        "or generated caches. The JSON manifest pins their commits and a digest "
        "of the engine code and build assets used by S31. The release asset's "
        "SHA-256 pins the entire archive.\n\n"
        "From this directory, use Zig 0.15.2:\n\n"
        "    cd src/frontends/s31\n"
        "    zig build test -Doptimize=ReleaseSafe -j2\n\n"
        "This is a scoped developer candidate, with open general compiler "
        "correspondence and native PCS/FRI soundness obligations. See "
        "design/s31/release/V01_CANDIDATE.md.\n"
    )
    out.parent.mkdir(parents=True, exist_ok=True)
    temporary = out.with_name(out.name + ".tmp")
    prefix = f"s31-{tag}/"
    try:
        with temporary.open("wb") as raw:
            with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as gz:
                with tarfile.open(fileobj=gz, mode="w|", format=tarfile.PAX_FORMAT) as target:
                    add_archive(target, ROOT, source_commit, prefix)
                    add_archive(target, ENGINE, engine_commit, prefix + "deps/stwo-zig/")
                    add_bytes(target, prefix + "SOURCE-BUNDLE.json",
                              (json.dumps(manifest, sort_keys=True, indent=2) + "\n").encode())
                    add_bytes(target, prefix + "SOURCE-BUNDLE.md", readme.encode())
        temporary.replace(out)
    finally:
        temporary.unlink(missing_ok=True)
    return {"path": str(out), "sha256": file_sha256(out),
            "bytes": out.stat().st_size, **manifest}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--audit", type=Path, required=True)
    parser.add_argument("--features", type=Path, required=True)
    parser.add_argument("--formal", type=Path, required=True)
    parser.add_argument("--compiler-sha256", required=True)
    parser.add_argument("--branch", required=True)
    parser.add_argument("--remote", default="origin")
    args = parser.parse_args()
    print(json.dumps(bundle(
        args.tag, args.out, audit=args.audit, features=args.features,
        formal=args.formal, compiler_sha256=args.compiler_sha256,
        branch=args.branch, remote=args.remote,
    ), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
