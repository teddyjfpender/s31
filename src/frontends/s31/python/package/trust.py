"""Admit package bytes against SHA-256 pins obtained outside the package.

The native verifier is executable code. A package's own manifest can describe
its contents but cannot authenticate that executable or its key. This module
checks caller-supplied pins before full validation of an untrusted package.
The caller must authenticate the pins through a separate channel.
"""

from __future__ import annotations

import hashlib
import hmac
import json
import os
import re
import shutil
import stat
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator

from package.verify import verify_package


PIN_RE = re.compile(r"[0-9a-f]{64}\Z")
NAME_RE = re.compile(r"[A-Za-z0-9_-]+\Z")
MAX_MANIFEST_BYTES = 4 * 1024 * 1024
# Admission copies untrusted directories before validation. Bound the copy
# itself, including files absent from the self-authored artifact manifest.
MAX_PACKAGE_BYTES = 256 * 1024 * 1024
MAX_PACKAGE_FILE_BYTES = 128 * 1024 * 1024
MAX_PACKAGE_ENTRIES = 512
COPY_CHUNK_BYTES = 1024 * 1024


def _bounded_package_copy(package: Path, snapshot: Path) -> None:
    """Copy a package with hard resource limits enforced during the read.

    ``copytree`` preserves linked entries so the later symlink check can reject
    them. Its ignore callback counts directory entries before descent; the
    copy callback reads regular files in bounded chunks, including files that
    the manifest does not list. No untrusted size declaration is relied on.
    """
    entries = 0
    copied = 0

    def count_entries(_directory: str, names: list[str]) -> set[str]:
        nonlocal entries
        entries += len(names)
        if entries > MAX_PACKAGE_ENTRIES:
            raise ValueError("package snapshot exceeds the entry limit")
        return set()

    def copy_file(source: str, target: str) -> str:
        nonlocal copied
        flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
        try:
            descriptor = os.open(source, flags)
        except OSError as exc:
            raise ValueError("package snapshot contains an inaccessible or linked file") from exc
        with os.fdopen(descriptor, "rb") as original:
            source_stat = os.fstat(original.fileno())
            if not stat.S_ISREG(source_stat.st_mode):
                raise ValueError("package snapshot contains a nonregular file")
            file_bytes = 0
            with open(target, "xb") as captured:
                while chunk := original.read(COPY_CHUNK_BYTES):
                    file_bytes += len(chunk)
                    copied += len(chunk)
                    if file_bytes > MAX_PACKAGE_FILE_BYTES or copied > MAX_PACKAGE_BYTES:
                        raise ValueError("package snapshot exceeds the byte limit")
                    captured.write(chunk)
                os.fchmod(captured.fileno(), stat.S_IMODE(source_stat.st_mode) & 0o777)
        return target

    shutil.copytree(package, snapshot, symlinks=True,
                    ignore=count_entries, copy_function=copy_file)
    if any(path.is_symlink() for path in snapshot.rglob("*")):
        raise ValueError("package snapshot contains a symlink")


def _inside_without_symlinks(package: Path, path: Path) -> bool:
    """Reject aliases at every path component, including a linked bin directory."""
    root = package.resolve(strict=True)
    relative = path.relative_to(package)
    candidate = package
    for part in relative.parts:
        candidate /= part
        if candidate.is_symlink():
            return False
    return path.resolve(strict=True).is_relative_to(root)


def pinned_paths(package: Path) -> dict[str, Path]:
    """Return the exact program and executable artifacts that need pins."""
    manifest_path = package / "manifest.json"
    if not _inside_without_symlinks(package, manifest_path):
        raise ValueError("package manifest is a symlink or escapes the package")
    if manifest_path.stat().st_size > MAX_MANIFEST_BYTES:
        raise ValueError("package manifest exceeds the admission size limit")
    manifest = json.loads(manifest_path.read_text())
    if not isinstance(manifest, dict):
        raise ValueError("invalid package manifest for pinned verifier")
    name = manifest.get("name")
    if not isinstance(name, str) or not NAME_RE.fullmatch(name):
        raise ValueError("invalid package name for pinned verifier")
    paths = {
        "source": package / "source.s31.json",
        "key": package / "verification-key.json",
        "prover": package / "bin" / f"s31-{name}-prover",
        "verifier": package / "bin" / f"s31-{name}-native-verifier",
    }
    if (package / "source.s31").exists() or (package / "source.s31").is_symlink():
        paths["text"] = package / "source.s31"
    return paths


def admit_pinned_package(package: Path, pins: dict[str, str]) -> tuple[dict[str, str], dict]:
    """Check exact external pins, then the package's internal consistency.

    Text packages require a fifth pin for the original `.s31` source. This
    does not authenticate the caller's pin source or prove compiler semantics.
    """
    paths = pinned_paths(package)
    if set(pins) != set(paths):
        required = ", ".join(sorted(paths))
        raise ValueError(f"pinned package requires exactly these digests: {required}")
    if any(not isinstance(digest, str) or not PIN_RE.fullmatch(digest)
           for digest in pins.values()):
        raise ValueError("pins must be lowercase SHA-256 hex digests")
    actual: dict[str, str] = {}
    for kind, path in paths.items():
        if not _inside_without_symlinks(package, path):
            raise ValueError(f"pinned {kind} is a symlink or escapes the package")
        actual[kind] = hashlib.sha256(path.read_bytes()).hexdigest()
        if not hmac.compare_digest(actual[kind], pins[kind]):
            raise ValueError(f"pinned {kind} digest mismatch")
    return actual, verify_package(package)


def check_pinned_package(package: Path, pins: dict[str, str]) -> dict[str, str]:
    """Return the checked digests for callers that do not need the manifest."""
    actual, _ = admit_pinned_package(package, pins)
    return actual


@contextmanager
def unpinned_snapshot(package: Path) -> Iterator[tuple[Path, dict]]:
    """Check and use one private package copy without claiming external trust.

    Internal manifest hashes detect an inconsistent copy. They do not
    authenticate who built the package or which source a caller intended.
    """
    with tempfile.TemporaryDirectory(prefix="s31-unpinned-package-") as temporary:
        snapshot = Path(temporary) / "package"
        _bounded_package_copy(package, snapshot)
        manifest = verify_package(snapshot)
        yield snapshot, manifest


@contextmanager
def admitted_snapshot(package: Path, pins: dict[str, str]) -> Iterator[tuple[Path, dict]]:
    """Verify and execute from private copied bytes, not the mutable input tree."""
    with tempfile.TemporaryDirectory(prefix="s31-pinned-package-") as temporary:
        snapshot = Path(temporary) / "package"
        _bounded_package_copy(package, snapshot)
        _, manifest = admit_pinned_package(snapshot, pins)
        yield snapshot, manifest
