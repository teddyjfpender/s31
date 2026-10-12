#!/usr/bin/env python3
"""Package complete, pinned S31 and stwo-zig source without Git metadata.

GitHub's source archives omit submodules.  The bundle carries both complete
tracked trees and a manifest that the Git-free compiler validates before it
uses the pinned engine commit in a package fingerprint.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tarfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
ENGINE = ROOT / "deps/stwo-zig"
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.context import compiler_fingerprint  # noqa: E402
from package.source_identity import engine_source_digest  # noqa: E402


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
                entry.name = prefix + entry.name
                entry.uid = entry.gid = 0
                entry.uname = entry.gname = ""
                target.addfile(entry, archive.extractfile(entry) if entry.isfile() else None)
                count += 1
    finally:
        proc.stdout.close()
    if proc.wait() != 0:
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


def bundle(tag: str, out: Path) -> dict:
    if "/" in tag or tag in {"", ".", ".."}:
        raise ValueError("tag must be one path component")
    if git(ROOT, "status", "--porcelain", "--untracked-files=normal"):
        raise RuntimeError("S31 source worktree must be clean")
    if git(ENGINE, "status", "--porcelain", "--untracked-files=normal"):
        raise RuntimeError("stwo-zig engine worktree must be clean")
    if Path(git(ENGINE, "rev-parse", "--show-toplevel")).resolve() != ENGINE.resolve():
        raise RuntimeError("stwo-zig must be its own Git worktree")

    source_commit = git(ROOT, "rev-parse", "HEAD")
    engine_commit = git(ENGINE, "rev-parse", "HEAD")
    manifest = {
        "schema": "s31-complete-source-bundle-v1",
        "tag": tag,
        "source_commit": source_commit,
        "source_tree": git(ROOT, "rev-parse", "HEAD^{tree}"),
        "engine_commit": engine_commit,
        "engine_tree": git(ENGINE, "rev-parse", "HEAD^{tree}"),
        "engine_source_sha256": engine_source_digest(ENGINE),
        "compiler_sha256": compiler_fingerprint(),
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
        "See design/s31/release/V01_CANDIDATE.md for the finite developer "
        "release scope and open soundness obligations.\n"
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
    args = parser.parse_args()
    print(json.dumps(bundle(args.tag, args.out), sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
