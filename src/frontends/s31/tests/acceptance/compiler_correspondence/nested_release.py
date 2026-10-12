#!/usr/bin/env python3
"""Nested function and array arguments must erase to their direct gates."""

from __future__ import annotations

import json

from functional_release import S31, run


if __name__ == "__main__":
    print(json.dumps(run(S31 / "examples/functional/release_nested4",
                         case="nested-static-applications",
                         result=lambda value: value * value + 2 * value),
                     indent=2, sort_keys=True))
