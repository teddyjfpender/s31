#!/usr/bin/env python3
"""Prove that repeated pure helper calls share the handwritten four-gate AIR."""

from __future__ import annotations

import json
from pathlib import Path

from optimized_release import run

EXAMPLE = Path(__file__).resolve().parents[3] / "examples/functional/release_functional_cse4"


if __name__ == "__main__":
    print(json.dumps(run(EXAMPLE, case="functional-cse",
                         source_to_canonical=(0, 1, 2, 3, 1, 2, 3, 4),
                         source_lets=7), indent=2, sort_keys=True))
