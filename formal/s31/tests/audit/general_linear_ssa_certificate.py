#!/usr/bin/env python3
"""Exercise Lean's exact certificate-byte decoder against reviewed mutations.

The Lean executable checks the arithmetic SSA fixture and a handwritten Lean
source term. This test does not authenticate S31 source bytes or native proofs.
"""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path


def run(executable: Path, path: Path, accepted: bool) -> None:
    completed = subprocess.run([str(executable), str(path)], capture_output=True,
                               text=True, check=False, timeout=30)
    if (completed.returncode == 0) != accepted:
        raise AssertionError(
            f"{path.name}: expected accepted={accepted}, got exit "
            f"{completed.returncode}: {completed.stdout} {completed.stderr}"
        )


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    executable = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else (
        root / ".lake/build/bin/s31-general-linear-certificate-check"
    )
    fixture = root / "fixtures/correspondence/source_relation_ssa_v1.json"
    run(executable, fixture, True)
    document = json.loads(fixture.read_text())
    mutations = {
        "opcode": ("ssa", "nodes", 0, "op", "add"),
        "forward-reference": ("ssa", "nodes", 0, "lhs", 3),
        "output": ("ssa", "output", 2),
        "assertion": ("ssa", "assertions", [[0, 1]]),
        "profile": ("lean_semantic_profile", "other-profile"),
        "digest-syntax": ("source_sha256", "not-a-sha256"),
        "unknown-field": ("unexpected", 1),
        "nested-extra-field": ("ssa", "unexpected", 1),
    }
    with tempfile.TemporaryDirectory(prefix="s31-lean-cert-") as temporary:
        for name, path_and_value in mutations.items():
            mutant = copy.deepcopy(document)
            *path, value = path_and_value
            cursor = mutant
            for key in path[:-1]:
                cursor = cursor[key]
            cursor[path[-1]] = value
            candidate = Path(temporary) / f"{name}.json"
            candidate.write_text(json.dumps(mutant, indent=2, sort_keys=True) + "\n")
            run(executable, candidate, False)
        raw = fixture.read_text()
        byte_mutations = {
            "duplicate-key": raw.replace(
                '  "capability": "source-to-relation-only",',
                '  "capability": "bad-capability",\n'
                '  "capability": "source-to-relation-only",', 1),
            "noncanonical-whitespace": raw.replace(
                '  "capability":', ' "capability":', 1),
            "noncanonical-key-order": raw.replace(
                '  "capability": "source-to-relation-only",\n'
                '  "lean_semantic_profile": "linear-ssa-m31-v1",',
                '  "lean_semantic_profile": "linear-ssa-m31-v1",\n'
                '  "capability": "source-to-relation-only",', 1),
            "oversized": raw + " " * 65536,
        }
        for name, value in byte_mutations.items():
            candidate = Path(temporary) / f"{name}.json"
            candidate.write_text(value)
            run(executable, candidate, False)
        # The generic graph checker allows either visibility. This control
        # checks only that the reviewed fixture runner pins its exact roster.
        visibility = copy.deepcopy(document)
        visibility["ssa"]["inputs"][0]["visibility"] = "public"
        candidate = Path(temporary) / "fixture-visibility-roster.json"
        candidate.write_text(json.dumps(visibility, indent=2,
                                        sort_keys=True) + "\n")
        run(executable, candidate, False)
    print(f"Lean certificate runtime controls: 1 accepted, "
          f"{len(mutations) + len(byte_mutations)} invalid rejected, "
          "1 reviewed-fixture roster mismatch rejected")


if __name__ == "__main__":
    main()
