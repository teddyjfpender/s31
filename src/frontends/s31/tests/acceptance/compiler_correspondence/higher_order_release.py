#!/usr/bin/env python3
"""A named Fn value must erase before the strict native release proof."""

from __future__ import annotations

import json

from functional_release import S31, run


if __name__ == "__main__":
    print(json.dumps(run(S31 / "examples/functional/release_higher_order4",
                         case="higher-order"), indent=2, sort_keys=True))
