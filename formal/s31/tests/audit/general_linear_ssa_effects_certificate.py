#!/usr/bin/env python3
"""Mutate a production effects certificate and require Lean gate rejection.

The handwritten Lean source and fixture roster are intentionally independent
of this Python test. The generic checker does not authenticate source bytes.
"""

from __future__ import annotations

import copy
import json
import subprocess
import sys
import tempfile
from pathlib import Path


def run(executable: Path, candidate: Path, accepted: bool) -> None:
    result = subprocess.run([str(executable), str(candidate)],
                            capture_output=True, text=True, check=False,
                            timeout=30)
    if (result.returncode == 0) != accepted:
        raise AssertionError(
            f"{candidate.name}: accepted={result.returncode == 0}, "
            f"expected={accepted}; {result.stdout} {result.stderr}"
        )


def main() -> None:
    root = Path(__file__).resolve().parents[2]
    executable = Path(sys.argv[1]).resolve() if len(sys.argv) == 2 else (
        root / ".lake/build/bin/s31-general-linear-effects-certificate-check"
    )
    fixture = root / "fixtures/correspondence/effects/affine_guard.certificate.json"
    run(executable, fixture, True)
    document = json.loads(fixture.read_text())
    mutations = {
        "wrong-constant": ("ssa", "nodes", 0, "constant", 8),
        "noncanonical-constant": ("ssa", "nodes", 0, "constant", 2147483647),
        "wrong-opcode": ("ssa", "nodes", 2, "op", "add"),
        "forward-reference": ("ssa", "nodes", 0, "lhs", 3),
        "dangling-assertion": ("ssa", "assertions", [[1, 5]]),
        "lost-assertion": ("ssa", "assertions", []),
        "wrong-output": ("ssa", "output", 3),
        "wrong-profile": ("lean_semantic_profile", "linear-ssa-m31-v1"),
        "bad-digest": ("relation_sha256", "not-a-digest"),
        "extra-top-field": ("unexpected", 1),
        "extra-ssa-field": ("ssa", "unexpected", 1),
        "extra-node-field": ("ssa", "nodes", 0, "rhs", 1),
    }
    count = 0
    with tempfile.TemporaryDirectory(prefix="s31-lean-effects-") as temporary:
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
            count += 1

        raw = fixture.read_text()
        byte_mutations = {
            "duplicate-key": raw.replace(
                '  "capability": "source-to-relation-only",',
                '  "capability": "bad",\n'
                '  "capability": "source-to-relation-only",', 1),
            "noncanonical-space": raw.replace('  "capability":', ' "capability":', 1),
            "oversized": raw + " " * 65536,
        }
        for name, contents in byte_mutations.items():
            candidate = Path(temporary) / f"{name}.json"
            candidate.write_text(contents)
            run(executable, candidate, False)
            count += 1

        # Visibility spelling is checked generically. A valid change is
        # rejected here by the reviewer's exact fixture-roster comparison.
        mutant = copy.deepcopy(document)
        mutant["ssa"]["inputs"][0]["visibility"] = "private"
        candidate = Path(temporary) / "reviewed-roster-mismatch.json"
        candidate.write_text(json.dumps(mutant, indent=2, sort_keys=True) + "\n")
        run(executable, candidate, False)
    print(f"Lean effects certificate controls: 1 accepted, {count} invalid "
          "rejected, 1 reviewed-roster mismatch rejected")


if __name__ == "__main__":
    main()
