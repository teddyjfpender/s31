#!/usr/bin/env python3
"""A returned captured Fn value must erase in a direct curried application."""

from __future__ import annotations

import json

from functional_release import S31, run


if __name__ == "__main__":
    print(json.dumps(run(S31 / "examples/functional/release_curried4",
                         case="returned-closure",
                         result=lambda value: value + value * value),
                     indent=2, sort_keys=True))
