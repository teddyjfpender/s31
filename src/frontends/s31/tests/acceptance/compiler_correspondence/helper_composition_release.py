#!/usr/bin/env python3
"""Nested helper arguments and captured functions must erase to two gates."""

from __future__ import annotations

import json

from functional_release import S31, run


if __name__ == "__main__":
    print(json.dumps(run(S31 / "examples/functional/release_helper_composition4",
                         case="nested-helper-body",
                         result=lambda value: 3 * value),
                     indent=2, sort_keys=True))
