#!/usr/bin/env python3
"""An inline Fn argument must erase before the strict native release proof."""

from __future__ import annotations

import json

from functional_release import S31, run


if __name__ == "__main__":
    print(json.dumps(run(S31 / "examples/functional/release_inline_lambda4",
                         case="inline-lambda",
                         result=lambda value: value**4),
                     indent=2, sort_keys=True))
