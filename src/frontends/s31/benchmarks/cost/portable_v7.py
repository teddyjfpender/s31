#!/usr/bin/env python3
"""Content-addressed, relocatable manifest for raw V7 train/held-out files."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import sys
from pathlib import Path, PurePosixPath

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "python"))
import s31

MANIFEST_NAME = "portable-manifest.json"
SCHEMA = "s31-whole-prover-v7-portable-evidence-v1"
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
REQUIRED = ("train/whole-prover-corpus.json",
            "validation/whole-prover-corpus.json",
            "validation/evaluation.json")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_relative(name: str) -> tuple[str, ...]:
    path = PurePosixPath(name)
    if (not name or name != path.as_posix() or path.is_absolute() or
        any(part in ("", ".", "..") for part in path.parts) or
        path.parts[0] not in ("train", "validation")):
        raise ValueError(f"unsafe portable artifact path: {name!r}")
    return path.parts


def checked_file(root: Path, name: str) -> Path:
    """Reject symlinks in every component and paths escaping the bundle root."""
    parts = safe_relative(name)
    current = root
    for component in parts[:-1]:
        current = current / component
        mode = current.lstat().st_mode
        if not stat.S_ISDIR(mode):
            raise ValueError(f"portable artifact parent is not a real directory: {name}")
    current = current / parts[-1]
    if not stat.S_ISREG(current.lstat().st_mode):
        raise ValueError(f"portable artifact is not a regular file: {name}")
    return current


def scan(root: Path) -> dict[str, dict]:
    files = {}
    for split in ("train", "validation"):
        directory = root / split
        if not stat.S_ISDIR(directory.lstat().st_mode):
            raise ValueError(f"missing real {split} evidence directory")
        for base, dirs, filenames in os.walk(directory, followlinks=False):
            for dirname in dirs:
                if not stat.S_ISDIR((Path(base) / dirname).lstat().st_mode):
                    raise ValueError("portable evidence cannot contain symlink directories")
            for filename in filenames:
                path = Path(base) / filename
                name = path.relative_to(root).as_posix()
                path = checked_file(root, name)
                files[name] = {"sha256": s31.file_hash(path), "bytes": path.stat().st_size}
    if not set(REQUIRED) <= files.keys():
        raise ValueError("portable evidence lacks corpus or evaluation files")
    return dict(sorted(files.items()))


def create(root: Path, protocol_sha: str, model_sha: str) -> dict:
    if HEX64.fullmatch(protocol_sha or "") is None or HEX64.fullmatch(model_sha or "") is None:
        raise ValueError("portable manifest requires full protocol and model SHAs")
    path = root / MANIFEST_NAME
    if path.exists():
        raise ValueError("portable manifest already exists; preserve the original snapshot")
    files = scan(root)
    train = json.loads((root / REQUIRED[0]).read_bytes())
    validation = json.loads((root / REQUIRED[1]).read_bytes())
    evaluation = json.loads((root / REQUIRED[2]).read_bytes())
    if (train.get("protocol_sha256") != protocol_sha or
        validation.get("protocol_sha256") != protocol_sha or
        validation.get("frozen_model_sha256") != model_sha or
        evaluation.get("frozen_model_sha256") != model_sha):
        raise ValueError("portable corpus/evaluation differs from freeze SHAs")
    manifest = {"schema": SCHEMA,
                "protocol_sha256": protocol_sha,
                "model_sha256": model_sha,
                "files": files}
    s31.write_json(path, manifest)
    return manifest


def verify(root: Path, expected_manifest_sha: str) -> dict:
    if HEX64.fullmatch(expected_manifest_sha or "") is None:
        raise ValueError("full externally recorded portable manifest SHA required")
    path = root / MANIFEST_NAME
    if not stat.S_ISREG(path.lstat().st_mode) or s31.file_hash(path) != expected_manifest_sha:
        raise ValueError("portable manifest differs from recorded SHA")
    manifest = json.loads(path.read_bytes())
    if manifest.get("schema") != SCHEMA or not isinstance(manifest.get("files"), dict):
        raise ValueError("wrong portable evidence manifest schema")
    actual = scan(root)
    if actual != manifest["files"]:
        raise ValueError("portable evidence files differ from content-addressed manifest")
    return manifest


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    command = parser.add_subparsers(dest="command", required=True)
    create_command = command.add_parser("create")
    create_command.add_argument("--root", type=Path, required=True)
    create_command.add_argument("--protocol-sha256", required=True)
    create_command.add_argument("--model-sha256", required=True)
    verify_command = command.add_parser("verify")
    verify_command.add_argument("--root", type=Path, required=True)
    verify_command.add_argument("--expected-manifest-sha256", required=True)
    args = parser.parse_args()
    if args.command == "create":
        create(args.root.resolve(), args.protocol_sha256, args.model_sha256)
        print(f"portable V7 manifest SHA-256: {s31.file_hash(args.root / MANIFEST_NAME)}")
    else:
        manifest = verify(args.root.resolve(), args.expected_manifest_sha256)
        print(json.dumps({"schema": manifest["schema"],
                          "files": len(manifest["files"]),
                          "manifest_sha256": args.expected_manifest_sha256},
                         indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
