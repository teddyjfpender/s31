#!/usr/bin/env python3
"""Audit a sealed pure-field control package across source, IR and Gate rows."""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "src/frontends/s31/python"))

from package.control_air_correspondence import check_control_air  # noqa: E402
from package.verify import verify_package  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--lean-checker", type=Path, default=(
        ROOT / "formal/s31/.lake/build/bin/s31-pure-field-derivation-bytes-check"))
    args = parser.parse_args()
    package = args.package.resolve()
    verify_package(package)
    if not args.lean_checker.is_file():
        parser.error("build the exact-byte checker with: "
                     "cd formal/s31 && lake build s31-pure-field-derivation-bytes-check")
    result = subprocess.run((
        str(args.lean_checker), str(package / "source.s31"),
        str(package / "pure-field-derivation.json"),
        str(package / "source.s31.json"),
    ), capture_output=True, text=True, check=False, timeout=30)
    if result.returncode != 0 or "accepted: exact source" not in result.stdout:
        raise ValueError("Lean exact-byte source derivation rejected package: " +
                         result.stderr.strip())
    report = check_control_air(package)
    report["lean_exact_source_derivation"] = True
    print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
