#!/usr/bin/env python3
"""A captured lambda must erase before the strict native release proof."""

from __future__ import annotations

import json

from functional_release import S31, run


if __name__ == "__main__":
    print(json.dumps(run(S31 / "examples/functional/release_closure4",
                         case="captured-closure",
                         result=lambda value: value * value + 2 * value),
                     indent=2, sort_keys=True))
