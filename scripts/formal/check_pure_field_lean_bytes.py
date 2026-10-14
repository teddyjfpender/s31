#!/usr/bin/env python3
"""Required build-plus-parity gate for the pure-field Lean byte checker.

Unlike the general Python test discovery, this command cannot pass by
skipping when the Lean executable has not been built.
"""

from __future__ import annotations

import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FORMAL = ROOT / "formal/s31"
CHECKER = FORMAL / ".lake/build/bin/s31-pure-field-derivation-bytes-check"


def main() -> int:
    with tempfile.TemporaryFile(mode="w+t") as log:
        built = subprocess.run(
            ["lake", "build", "s31-pure-field-derivation-bytes-check"],
            cwd=FORMAL, stdout=log, stderr=subprocess.STDOUT, check=False)
        if built.returncode:
            log.seek(0)
            print(log.read()[-8000:], file=sys.stderr)
            return built.returncode
    if not CHECKER.is_file():
        print(f"Lean checker binary missing after successful build: {CHECKER}",
              file=sys.stderr)
        return 1
    tested = subprocess.run(
        [sys.executable, "-m", "unittest",
         "scripts.tests.test_pure_field_lean_bytes", "-q"],
        cwd=ROOT, check=False)
    return tested.returncode


if __name__ == "__main__":
    raise SystemExit(main())
