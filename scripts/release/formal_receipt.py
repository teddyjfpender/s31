#!/usr/bin/env python3
"""Run the pinned Lean release checks and record their actual command logs."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

import s31  # noqa: E402
from scripts.release.release_candidate import FORMAL_COMMANDS  # noqa: E402


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()


@dataclass(frozen=True)
class Snapshot:
    commit: str
    compiler: str
    inventory: str
    bindings: str
    clean: bool


def snapshot(root: Path) -> Snapshot:
    engine = root / "deps/stwo-zig"
    pinned_engine = git(root, "rev-parse", "HEAD:deps/stwo-zig")
    engine_commit = git(engine, "rev-parse", "HEAD")
    clean = (not git(root, "status", "--porcelain", "--untracked-files=normal") and
             not git(engine, "status", "--porcelain", "--untracked-files=normal") and
             engine_commit == pinned_engine)
    return Snapshot(git(root, "rev-parse", "HEAD"), s31.compiler_fingerprint(),
                    digest(root / "formal/s31/proof-inventory.json"),
                    digest(root / "formal/s31/source-bindings.json"), clean)


def _write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                     prefix=f".{path.name}.", suffix=".tmp",
                                     delete=False) as file:
        temporary = Path(file.name)
        json.dump(value, file, indent=2, sort_keys=True)
        file.write("\n")
    os.replace(temporary, path)


def run(out: Path, logs_dir: Path, *, root: Path = ROOT,
        take_snapshot: Callable[[Path], Snapshot] = snapshot,
        execute: Callable[..., subprocess.CompletedProcess] = subprocess.run) -> dict:
    """Run all checks sequentially; a failed or drifting run cannot pass."""
    before = take_snapshot(root)
    if not before.clean:
        raise ValueError("formal receipt requires a clean S31 and pinned engine worktree")
    if out.is_symlink() or logs_dir.is_symlink():
        raise ValueError("formal receipt output paths must not be symlinks")
    logs_dir.mkdir(parents=True, exist_ok=True)
    environment = {**os.environ, "LEAN_NUM_THREADS": "1"}
    checks: dict[str, dict] = {}
    failure: str | None = None
    for name, command in FORMAL_COMMANDS.items():
        log = logs_dir / f"{name}.log"
        if log.is_symlink():
            raise ValueError(f"formal log path is a symlink: {log}")
        cwd = root / "formal/s31" if name != "bindings" else root
        print(f"formal {name}: running", file=sys.stderr, flush=True)
        with log.open("wb") as file:
            result = execute(command, cwd=cwd, env=environment, stdout=file,
                             stderr=subprocess.STDOUT, check=False)
        checks[name] = {"command": command, "returncode": result.returncode,
                        "log": str(log.resolve()), "log_sha256": digest(log)}
        if name == "lake_build" and result.returncode == 0:
            checker = root / "formal/s31/.lake/build/bin/s31-general-linear-structural-check"
            if not checker.is_file() or checker.is_symlink():
                raise ValueError("formal lake build did not produce the structural checker")
            checks[name]["structural_checker_sha256"] = digest(checker)
        after = take_snapshot(root)
        if after != before:
            failure = f"source, compiler, formal inventory, or worktree drift after {name}"
            print(f"formal {name}: {failure}", file=sys.stderr, flush=True)
            break
        if result.returncode != 0:
            failure = f"{name} exited {result.returncode}"
            print(f"formal {name}: {failure}", file=sys.stderr, flush=True)
            break
        print(f"formal {name}: passed", file=sys.stderr, flush=True)
    receipt = {"schema": "s31-v01-formal-checks-v1",
               "source_commit": before.commit,
               "receipt_script_sha256": digest(Path(__file__)),
               "compiler_sha256": before.compiler,
               "inventory_sha256": before.inventory,
               "bindings_sha256": before.bindings,
               "checks": checks,
               "status": "passed" if failure is None else "failed",
               "failure": failure,
               "lean_threads": 1}
    _write_json(out, receipt)
    return receipt


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--logs-dir", type=Path)
    arguments = parser.parse_args()
    out = arguments.out.absolute()
    logs_dir = (arguments.logs_dir or out.parent / f"{out.stem}-logs").absolute()
    try:
        receipt = run(out, logs_dir)
    except (OSError, ValueError, subprocess.CalledProcessError) as error:
        print(f"formal receipt: {error}", file=sys.stderr)
        return 1
    print(json.dumps({"status": receipt["status"], "checks": list(receipt["checks"]),
                      "source_commit": receipt["source_commit"]}, sort_keys=True))
    return 0 if receipt["status"] == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
