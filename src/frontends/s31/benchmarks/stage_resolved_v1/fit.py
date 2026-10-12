#!/usr/bin/env python3
"""Freeze historical stage centers and untouched-source interval calibration."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from model import fit, sha

HERE = Path(__file__).resolve().parent


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ledger", type=Path, default=HERE / "historical-stage-ledger.json")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if args.out.exists():
        raise FileExistsError("stage calibration is write-once")
    ledger = json.loads(args.ledger.read_bytes())
    result = fit(ledger, sha(args.ledger), sha(HERE / "model.py"))
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(args.out)


if __name__ == "__main__":
    main()
