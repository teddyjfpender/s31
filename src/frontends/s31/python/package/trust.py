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
import re
import shutil
import tempfile
from contextlib import contextmanager
from pathlib import Path
from typing import Iterator

from package.verify import verify_package


PIN_RE = re.compile(r"[0-9a-f]{64}\Z")
NAME_RE = re.compile(r"[A-Za-z0-9_-]+\Z")
MAX_MANIFEST_BYTES = 4 * 1024 * 1024


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
def admitted_snapshot(package: Path, pins: dict[str, str]) -> Iterator[tuple[Path, dict]]:
    """Verify and execute from private copied bytes, not the mutable input tree."""
    with tempfile.TemporaryDirectory(prefix="s31-pinned-package-") as temporary:
        snapshot = Path(temporary) / "package"
        shutil.copytree(package, snapshot, symlinks=True)
        if any(path.is_symlink() for path in snapshot.rglob("*")):
            raise ValueError("pinned package snapshot contains a symlink")
        _, manifest = admit_pinned_package(snapshot, pins)
        yield snapshot, manifest
