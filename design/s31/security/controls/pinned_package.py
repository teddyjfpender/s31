#!/usr/bin/env python3
"""Admit an S31 package against digests obtained from a separate trust root.

The pins must come from a trusted channel. Reading them from the package's own
manifest would make this check circular. Both executable binaries are pinned:
the prover receives private witness data and the verifier decides acceptance.
Text packages additionally require an exact source.s31 pin.
This command only checks files; it does not run either binary or authenticate
the issuer of the pins.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[4]
sys.path.insert(0, str(REPO / "src/frontends/s31/python"))

from package.trust import check_pinned_package, pinned_paths  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--source-sha256", required=True)
    parser.add_argument("--key-sha256", required=True)
    parser.add_argument("--prover-sha256", required=True)
    parser.add_argument("--verifier-sha256", required=True)
    parser.add_argument("--text-sha256", help="required for a package containing source.s31")
    args = parser.parse_args()
    try:
        pins = {
            "source": args.source_sha256,
            "key": args.key_sha256,
            "prover": args.prover_sha256,
            "verifier": args.verifier_sha256,
        }
        if args.text_sha256 is not None:
            pins["text"] = args.text_sha256
        actual = check_pinned_package(args.package, pins)
    except (ValueError, OSError, KeyError, TypeError, RuntimeError,
            UnicodeError, json.JSONDecodeError) as exc:
        print(f"pinned package rejected: {exc}", file=sys.stderr)
        return 1
    print(json.dumps({"accepted": True, "sha256": actual}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
