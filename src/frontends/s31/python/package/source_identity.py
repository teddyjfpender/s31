"""Pin the engine in both Git checkouts and complete source archives.

Git searches parent directories for a repository.  An extracted submodule
without its own ``.git`` must never inherit the enclosing S31 checkout's HEAD.
"""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
from pathlib import Path


_ENGINE_SOURCE_DIRS = (
    "src", "build_support", "third_party", "vectors/circuit",
    "vectors/cairo", "vectors/cairo_traces", "vectors/riscv_guests",
    "vectors/riscv_csp", "vectors/riscv_elfs",
)
_ENGINE_SOURCE_FILES = (
    "build.zig", "build.zig.zon", "vectors/fields.json",
    "vectors/constraint_expr.json", "vectors/air_derive.json",
)
_GENERATED_DIRS = frozenset({".zig-cache", "zig-out", "target", "__pycache__"})


def engine_source_digest(engine_root: Path) -> str:
    """Hash build code and assets used by S31, excluding research/report data."""
    if not (engine_root / "src").is_dir():
        raise RuntimeError("pinned stwo-zig dependency has no src directory")
    paths = [engine_root / name for name in _ENGINE_SOURCE_FILES]
    if any(not path.is_file() for path in paths):
        raise RuntimeError("pinned stwo-zig dependency lacks a required build asset")
    for name in _ENGINE_SOURCE_DIRS:
        directory = engine_root / name
        if not directory.is_dir():
            raise RuntimeError(f"pinned stwo-zig dependency lacks {name}")
        for parent, directories, files in os.walk(directory):
            for child in directories:
                if (Path(parent) / child).is_symlink():
                    raise RuntimeError("pinned stwo-zig dependency contains a source symlink")
            directories[:] = [child for child in directories if child not in _GENERATED_DIRS]
            paths.extend(Path(parent) / file for file in files)
    digest = hashlib.sha256()
    for path in sorted(paths, key=lambda item: item.relative_to(engine_root).as_posix()):
        if path.is_symlink():
            raise RuntimeError("pinned stwo-zig dependency contains a source symlink")
        if not path.is_file():
            raise RuntimeError("pinned stwo-zig dependency contains a non-file source")
        digest.update(path.relative_to(engine_root).as_posix().encode())
        digest.update(b"\0")
        content_digest = hashlib.sha256()
        with path.open("rb") as source:
            for chunk in iter(lambda: source.read(1 << 20), b""):
                content_digest.update(chunk)
        digest.update(content_digest.digest())
    return digest.hexdigest()


def pinned_engine_commit(root: Path, engine_root: Path) -> str:
    """Return the engine commit only after checking the identity mechanism."""
    if (engine_root / ".git").exists():
        top = subprocess.check_output(
            ["git", "-C", str(engine_root), "rev-parse", "--show-toplevel"],
            text=True,
        ).strip()
        if Path(top).resolve() != engine_root.resolve():
            raise RuntimeError("pinned stwo-zig Git worktree is not its own root")
        commit = subprocess.check_output(
            ["git", "-C", str(engine_root), "rev-parse", "HEAD"], text=True,
        ).strip()
        if subprocess.check_output(
            ["git", "-C", str(engine_root), "status", "--porcelain", "--untracked-files=no"],
            text=True,
        ).strip():
            raise RuntimeError("pinned stwo-zig dependency has local modifications")
        return commit

    manifest_path = root / "SOURCE-BUNDLE.json"
    if not manifest_path.is_file():
        raise RuntimeError("pinned stwo-zig has no own Git worktree or SOURCE-BUNDLE.json")
    try:
        manifest = json.loads(manifest_path.read_text())
    except (OSError, json.JSONDecodeError) as exc:
        raise RuntimeError("invalid SOURCE-BUNDLE.json") from exc
    if not isinstance(manifest, dict) or manifest.get("schema") != "s31-complete-source-bundle-v1":
        raise RuntimeError("invalid S31 source-bundle schema")
    commit = manifest.get("engine_commit")
    expected = manifest.get("engine_source_sha256")
    if (not isinstance(commit, str) or len(commit) not in (40, 64) or
            any(c not in "0123456789abcdef" for c in commit) or
            not isinstance(expected, str) or len(expected) != 64 or
            any(c not in "0123456789abcdef" for c in expected)):
        raise RuntimeError("invalid source-bundle engine pin")
    if engine_source_digest(engine_root) != expected:
        raise RuntimeError("source-bundle engine code differs from its pinned manifest")
    return commit
