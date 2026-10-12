#!/usr/bin/env python3
"""Seal and preflight-check exact frozen model bytes for a future heldout run.

This tool was added *after* the mixed-stage transfer v1 raw phase and audit.
It cannot retroactively score that run. A future heldout collector must call
``check`` before its first native build and pin the returned anchor/hash.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
from pathlib import Path

SCHEMA = "s31-frozen-model-artifact-v1"
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
HEX40 = re.compile(r"[0-9a-f]{40}\Z")


def canonical(value: dict) -> bytes:
    return (json.dumps(value, sort_keys=True, separators=(",", ":"),
                       ensure_ascii=True) + "\n").encode()


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def unique(pairs: list[tuple[str, object]]) -> dict:
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def root(path: Path) -> Path:
    return Path(subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "--show-toplevel"], text=True).strip()).resolve()


def local_path(repo: Path, path: Path) -> tuple[Path, str]:
    absolute = path.absolute()
    if absolute.is_symlink():
        raise ValueError("model artifact or manifest cannot be a symlink")
    resolved = absolute.resolve()
    try:
        relative = resolved.relative_to(repo).as_posix()
    except ValueError as exc:
        raise ValueError("model artifact or manifest must be inside the repository") from exc
    if relative in ("", "."):
        raise ValueError("model artifact or manifest must be a file path")
    return resolved, relative


def seal(source: Path, artifact: Path, manifest: Path,
         expected_model_sha256: str, protocol_sha256: str, repo: Path) -> dict:
    if not HEX64.fullmatch(expected_model_sha256) or not HEX64.fullmatch(protocol_sha256):
        raise ValueError("full model and protocol SHA-256 values are required")
    repo = repo.resolve()
    artifact, artifact_name = local_path(repo, artifact)
    manifest, manifest_name = local_path(repo, manifest)
    if artifact == manifest or artifact.exists() or manifest.exists():
        raise ValueError("fresh distinct artifact and manifest paths are required")
    if source.is_symlink() or not source.is_file():
        raise ValueError("source model is absent or a symlink")
    data = source.read_bytes()
    model = json.loads(data, object_pairs_hook=unique)
    if (sha(data) != expected_model_sha256 or type(model) is not dict or
            type(model.get("schema")) is not str or not model["schema"]):
        raise ValueError("source model bytes, JSON, or schema differ from frozen hash")
    value = {"schema": SCHEMA, "artifact_path": artifact_name,
             "artifact_sha256": expected_model_sha256,
             "artifact_bytes": len(data), "model_schema": model["schema"],
             "protocol_sha256": protocol_sha256,
             "status": "awaiting_separate_committed_anchor_before_heldout"}
    artifact.parent.mkdir(parents=True, exist_ok=True)
    manifest.parent.mkdir(parents=True, exist_ok=True)
    artifact.write_bytes(data)
    manifest.write_bytes(canonical(value))
    return {"artifact_path": artifact_name, "manifest_path": manifest_name,
            "model_sha256": expected_model_sha256,
            "manifest_sha256": sha(manifest.read_bytes()),
            "status": "seal_written_not_yet_committed"}


def check(manifest: Path, expected_model_sha256: str, protocol_sha256: str,
          anchor_commit: str, repo: Path) -> dict:
    if (not HEX64.fullmatch(expected_model_sha256) or
            not HEX64.fullmatch(protocol_sha256) or
            not HEX40.fullmatch(anchor_commit)):
        raise ValueError("full model/protocol SHA-256 and anchor commit required")
    repo = repo.resolve()
    manifest, manifest_name = local_path(repo, manifest)
    saved = manifest.read_bytes()
    value = json.loads(saved, object_pairs_hook=unique)
    if type(value) is not dict or saved != canonical(value) or set(value) != {
            "schema", "artifact_path", "artifact_sha256", "artifact_bytes",
            "model_schema", "protocol_sha256", "status"}:
        raise ValueError("manifest JSON or keys differ from canonical format")
    if (value["schema"] != SCHEMA or
            value["status"] != "awaiting_separate_committed_anchor_before_heldout" or
            value["artifact_sha256"] != expected_model_sha256 or
            value["protocol_sha256"] != protocol_sha256 or
            type(value["artifact_bytes"]) is not int or value["artifact_bytes"] <= 0 or
            type(value["model_schema"]) is not str or not value["model_schema"]):
        raise ValueError("frozen model manifest differs from expected identity")
    artifact, artifact_name = local_path(repo, repo / value["artifact_path"])
    if artifact_name != value["artifact_path"] or artifact == manifest:
        raise ValueError("manifest artifact path is invalid")
    data = artifact.read_bytes()
    model = json.loads(data, object_pairs_hook=unique)
    if (len(data) != value["artifact_bytes"] or sha(data) != expected_model_sha256 or
            type(model) is not dict or model.get("schema") != value["model_schema"]):
        raise ValueError("retained frozen model bytes differ")
    if subprocess.run(["git", "-C", str(repo), "merge-base", "--is-ancestor",
                       anchor_commit, "HEAD"], check=False,
                      capture_output=True).returncode:
        raise ValueError("model artifact anchor is not an ancestor of this checkout")
    for name, content in ((artifact_name, data), (manifest_name, saved)):
        result = subprocess.run(["git", "-C", str(repo), "show", f"{anchor_commit}:{name}"],
                                check=False, capture_output=True)
        if result.returncode or result.stdout != content:
            raise ValueError(f"model artifact or manifest differs from anchor: {name}")
    return {"schema": SCHEMA, "status": "committed_model_bytes_verified_before_heldout",
            "model_sha256": expected_model_sha256, "manifest_sha256": sha(saved),
            "artifact_path": artifact_name, "anchor_commit": anchor_commit}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    make = sub.add_parser("seal")
    make.add_argument("--source", required=True, type=Path)
    make.add_argument("--artifact", required=True, type=Path)
    make.add_argument("--manifest", required=True, type=Path)
    verify = sub.add_parser("check")
    verify.add_argument("--manifest", required=True, type=Path)
    verify.add_argument("--anchor-commit", required=True)
    for command in (make, verify):
        command.add_argument("--repo", type=Path, default=Path.cwd())
        command.add_argument("--expected-model-sha256", required=True)
        command.add_argument("--protocol-sha256", required=True)
    args = parser.parse_args()
    result = (seal(args.source, args.artifact, args.manifest,
                   args.expected_model_sha256, args.protocol_sha256, root(args.repo))
              if args.command == "seal" else
              check(args.manifest, args.expected_model_sha256, args.protocol_sha256,
                    args.anchor_commit, root(args.repo)))
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
