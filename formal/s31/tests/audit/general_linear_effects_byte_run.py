#!/usr/bin/env python3
"""Exercise Lean's exact effectful source/ABI/interpreter byte admission."""

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
    fixture = formal / "fixtures/correspondence"
    executable = formal / ".lake/build/bin/s31-general-linear-effects-byte-run-check"
    paths = {
        "source": fixture / "effects/affine_guard.s31",
        "certificate": fixture / "effects/affine_guard.certificate.json",
        "relation": fixture / "effects/affine_guard.relation.json",
        "abi": fixture / "public_abi/effects.abi.json",
        "assignment": fixture / "public_abi/effects.assignment.json",
        "public_words": fixture / "public_abi/effects.public_words.bin",
    }
    run(executable, paths, True)

    assignment = json.loads(paths["assignment"].read_bytes())
    wrong_witness = copy.deepcopy(assignment)
    wrong_witness["private_inputs"]["y"][0] = 73
    wrong_claim = copy.deepcopy(assignment)
    wrong_claim["public_outputs"]["out"][0] = 72
    relation = json.loads(paths["relation"].read_bytes())
    wrong_operation = copy.deepcopy(relation)
    wrong_operation["nodes"][2]["op"] = "add"
    wrong_constant = copy.deepcopy(relation)
    wrong_constant["nodes"][1]["constant"] = 8
    wrong_assertion = copy.deepcopy(relation)
    wrong_assertion["assertions"][0]["rhs"] = "shifted"
    mutants = [
        ("assignment", canonical(wrong_witness)),
        ("assignment", canonical(wrong_claim)),
        ("assignment", paths["assignment"].read_bytes().replace(
            b'  "private_inputs": {',
            b'  "private_inputs": {},\n  "private_inputs": {', 1)),
        ("assignment", paths["assignment"].read_bytes().replace(
            b'  "private_inputs": {', b' "private_inputs": {', 1)),
        ("relation", canonical(wrong_operation)),
        ("relation", canonical(wrong_constant)),
        ("relation", canonical(wrong_assertion)),
        ("source", paths["source"].read_bytes().replace(
            b"assert_eq(y, scaled)", b"assert_eq(y, shifted)", 1)),
        ("public_words", paths["public_words"].read_bytes()[:-1] + b"\x01"),
    ]
    with tempfile.TemporaryDirectory(prefix="s31-lean-effects-byte-run-") as directory:
        for index, (name, content) in enumerate(mutants):
            path = Path(directory) / f"{index}.{name}"
            path.write_bytes(content)
            modified = dict(paths)
            modified[name] = path
            run(executable, modified, False)
    print(f"accepted reviewed effects fixture; rejected {len(mutants)} mutations")


if __name__ == "__main__":
    main()
