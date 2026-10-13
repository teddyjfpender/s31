#!/usr/bin/env python3
"""Exercise the Lean pure source/ABI/typed-interpreter exact-byte gate."""

from __future__ import annotations

import copy
import json
import subprocess
import tempfile
from pathlib import Path


def canonical(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def run(executable: Path, paths: dict[str, Path], accepted: bool) -> None:
    result = subprocess.run(
        [str(executable), *(str(paths[name]) for name in
            ("source", "certificate", "relation", "abi", "assignment", "public_words"))],
        capture_output=True, text=True, check=False, timeout=30,
    )
    if (result.returncode == 0) != accepted:
        raise AssertionError(
            f"accepted={result.returncode == 0}, expected={accepted}; "
            f"{result.stdout} {result.stderr}"
        )


def main() -> None:
    formal = Path(__file__).resolve().parents[2]
    fixture = formal / "fixtures/correspondence/public_abi"
    executable = formal / ".lake/build/bin/s31-general-linear-byte-run-check"
    paths = {name: fixture / f"pure.{suffix}" for name, suffix in (
        ("source", "s31"),
        ("certificate", "certificate.json"),
        ("relation", "relation.json"),
        ("abi", "abi.json"),
        ("assignment", "assignment.json"),
        ("public_words", "public_words.bin"),
    )}
    run(executable, paths, True)

    assignment = json.loads(paths["assignment"].read_bytes())
    changed_private = copy.deepcopy(assignment)
    changed_private["private_inputs"]["b"][0] = 7
    changed_public_output = copy.deepcopy(assignment)
    changed_public_output["public_outputs"]["doubled"][0] = 3
    relation = json.loads(paths["relation"].read_bytes())
    changed_relation = copy.deepcopy(relation)
    changed_relation["nodes"][0]["op"] = "add"
    mutants = [
        ("assignment", canonical(changed_private)),
        ("assignment", canonical(changed_public_output)),
        ("assignment", paths["assignment"].read_bytes().replace(
            b'  "public_inputs": {},', b'  "public_inputs": {},\n  "public_inputs": {},', 1)),
        ("assignment", paths["assignment"].read_bytes().replace(
            b'  "public_inputs": {},', b' "public_inputs": {},', 1)),
        ("relation", canonical(changed_relation)),
        ("source", paths["source"].read_bytes().replace(b"a - b", b"b - a", 1)),
        ("public_words", paths["public_words"].read_bytes()[:-1] + b"\x01"),
    ]
    with tempfile.TemporaryDirectory(prefix="s31-lean-byte-run-") as directory:
        for index, (name, content) in enumerate(mutants):
            path = Path(directory) / f"{index}.{name}"
            path.write_bytes(content)
            modified = dict(paths)
            modified[name] = path
            run(executable, modified, False)
    print(f"accepted reviewed pure fixture; rejected {len(mutants)} mutations")


if __name__ == "__main__":
    main()
