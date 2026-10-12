#!/usr/bin/env python3
"""Recommit the case07 Lean-bound 512-row fixed roster with the native PCS.

The input columns are explicit fixture bytes, not reconstructed from the S31
source by the native compiler. This binds the diagnostic roster to the sealed
fixed root for this case. It does not authenticate arbitrary PCS openings.
"""

from __future__ import annotations

import argparse
import copy
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[2]
ROOT = S31.parents[2]
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tools/formal"))

import full_native_roster as roster  # noqa: E402
import alias8_native_fixture as lean_fixture  # noqa: E402
import s31  # noqa: E402

CASE = HERE / "fixtures/case07-full-native-roster.json"
ROOT_PATTERN = re.compile(r"[0-9a-f]{64}")


def recommit(prover: Path, columns: list[list[int]], work: Path,
             name: str) -> str:
    path = work / f"{name}.json"
    path.write_text(json.dumps({"schema": "s31-direct-gate-fixed-columns-v1",
                                "fixed_columns": columns}, separators=(",", ":")))
    result = subprocess.run((str(prover), "inspect-fixed-root-from-columns", str(path)),
                            capture_output=True, text=True, timeout=120, check=False)
    if result.returncode:
        raise ValueError(f"native fixed recommit failed: {result.stderr.strip()}")
    response = json.loads(result.stdout + result.stderr)
    if (type(response) is not dict or set(response) != {"schema", "fixed_root"} or
            response["schema"] != "s31-direct-gate-recommitted-fixed-root-v1" or
            type(response["fixed_root"]) is not str or
            ROOT_PATTERN.fullmatch(response["fixed_root"]) is None):
        raise ValueError("invalid native fixed recommit report")
    return response["fixed_root"]


def run(package: Path, work: Path) -> dict:
    data = json.loads(CASE.read_bytes())
    sample = next(sample for sample, prefix in roster.selected_samples()
                  if prefix == "case07")
    pinned = roster.pinned_cases()[sample.label]
    roster.check_case(data, sample, pinned)
    if lean_fixture.OUTPUT.read_text() != lean_fixture.render():
        raise ValueError("case07 Lean fixture differs from checked 512-row native export")
    manifest = s31.verify_package(package)
    key = json.loads((package / "verification-key.json").read_bytes())
    prover = package / "bin" / f"s31-{manifest['name']}-prover"
    if (manifest.get("source_text_sha256") != data["source_sha256"] or
            key.get("preprocessed_root") != data["sealed_key_root"]):
        raise ValueError("source-bound package differs from pinned case07 diagnostic")
    columns = data["physical"]["fixed_columns"]
    expected = data["sealed_key_root"]
    topology = json.loads(s31.invoke(str(prover), "inspect-topology"))
    if (topology != data["topology"] or
            [column["values"] for column in topology["columns"]] != columns or
            topology["preprocessed_root"] != expected):
        raise ValueError("fresh source-bound topology differs from checked case07 cells/root")
    actual = recommit(prover, columns, work, "honest")
    if actual != expected:
        raise ValueError("explicit fixed rows recommit to a different sealed root")

    mutations = {
        "selector": (0, 16, 0),
        "source_address": (4, 0, 0),
        "island_multiplicity": (7, 16, 0),
    }
    rejected = []
    for name, (column, row, delta) in mutations.items():
        changed = copy.deepcopy(columns)
        changed[column][row] = (changed[column][row] + 1 + delta) % roster.P
        if recommit(prover, changed, work, name) == expected:
            raise AssertionError(f"{name} fixed-cell mutation retained sealed root")
        rejected.append(name)
    swapped = copy.deepcopy(columns)
    swapped[4], swapped[5] = swapped[5], swapped[4]
    if recommit(prover, swapped, work, "column-swap") == expected:
        raise AssertionError("fixed-column permutation retained sealed root")
    rejected.append("column-swap")

    for name, change, error in (
        ("noncanonical", lambda c: c[0].__setitem__(16, roster.P), "NonCanonicalM31Word"),
        ("short-column", lambda c: c[0].pop(), "InvalidDirectTraceShape"),
    ):
        changed = copy.deepcopy(columns)
        change(changed)
        path = work / f"{name}.json"
        path.write_text(json.dumps({"schema": "s31-direct-gate-fixed-columns-v1",
                                    "fixed_columns": changed}, separators=(",", ":")))
        trial = subprocess.run((str(prover), "inspect-fixed-root-from-columns", str(path)),
                               capture_output=True, text=True, timeout=120, check=False)
        if trial.returncode == 0 or error not in trial.stderr:
            raise AssertionError(f"{name} was not rejected at {error}: {trial.stderr}")
        rejected.append(name)
    return {"schema": "s31-alias8-fixed-root-recommit-v1",
            "source_sha256": data["source_sha256"],
            "fixed_cells": 8 * 512, "native_recommitted_root": actual,
            "sealed_key_root": expected, "mutations_rejected": rejected,
            "scope": "diagnostic export equals sealed PCS fixed commitment for case07"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path, help="existing source-bound case07 package")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="s31-alias8-fixed-root-") as directory:
        work = Path(directory)
        if args.package is None:
            sample = next(sample for sample, prefix in roster.selected_samples()
                          if prefix == "case07")
            source = work / "case07.s31"
            source.write_text(sample.source)
            package = s31.build(source, work / "package", "direct-gate")
        else:
            package = args.package.resolve()
        print(json.dumps(run(package, work), sort_keys=True))


if __name__ == "__main__":
    main()
