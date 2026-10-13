#!/usr/bin/env python3
"""A pure ordered-subtraction helper must erase and pass strict release verification."""

from __future__ import annotations

import json
import sys
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(Path(__file__).resolve().parent))

from functional_release import run


if __name__ == "__main__":
    example = S31 / "examples/functional/release_sub4"
    print(json.dumps(run(example, case="ordered-subtraction",
                         result=lambda value: -2 * value,
                         full_public_trace=True), indent=2, sort_keys=True))
