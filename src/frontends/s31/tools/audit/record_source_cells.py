#!/usr/bin/env python3
"""Audit source-owned fixed Gate cells for a pinned bounded record-v2 package.

The independent exact-source parser determines the arithmetic graph and its
one-lane address allocation. A fresh native topology export supplies all 512
fixed rows; the checker compares the entire export with the package manifest,
asks the pinned prover to recommit its eight columns, and locates each source
arithmetic row. Witness values and PCS/FRI acceptance are outside this audit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.context import invoke, write_json  # noqa: E402
from package.correspondence import (  # noqa: E402
    DIRECT_COLUMN_IDS, parse_canonical_json, replay_direct_topology,
)
from package.record_source_fragment import (  # noqa: E402
    check_package_record_source_relation, parse_record_source_fragment,
)
from package.trust import admitted_snapshot  # noqa: E402

ROW_COUNT = 512


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def source_cells(relation: dict, topology: dict) -> list[dict[str, int | str]]:
    """Locate every source add/mul by independently allocated wire addresses."""
    inputs, nodes = relation["inputs"], relation["nodes"]
    if (relation.get("version") != 2 or not 1 <= len(inputs) <= 8 or
            not 1 <= len(nodes) <= 8 or relation["assertions"] or
            not 1 <= len(relation["public_outputs"]) <= 4 or
            any(item["kind"] != "m31" or item["length"] != 1 for item in inputs) or
            any(item["op"] not in {"add", "mul"} for item in nodes)):
        raise ValueError("outside scalar record-v2 physical source-row fragment")
    names = [item["name"] for item in inputs + nodes]
    if len(names) != len(set(names)):
        raise ValueError("record source wire names repeat")
    address = {item["name"]: (11 if index == 0 else 13 + index)
               for index, item in enumerate(inputs)}
    address.update({item["name"]: 13 + len(inputs) + index
                    for index, item in enumerate(nodes)})
    columns = topology.get("columns")
    if (not isinstance(columns, list) or
            [column.get("id") for column in columns] != list(DIRECT_COLUMN_IDS) or
            any(type(column.get("values")) is not list or
                len(column["values"]) != ROW_COUNT or
                any(type(value) is not int or value < 0 or value >= 2**31 - 1
                    for value in column["values"]) for column in columns)):
        raise ValueError("fixed Gate columns are not eight canonical 512-row columns")
    rows = list(zip(*(column["values"] for column in columns), strict=True))
    matched: list[dict[str, int | str]] = []
    for node in nodes:
        try:
            expected = ((1, 0, 0, 0) if node["op"] == "add" else
                        (0, 0, 0, 1)) + (address[node["lhs"]],
                                         address[node["rhs"]],
                                         address[node["name"]])
        except KeyError as exc:
            raise ValueError("source operand is not a declared earlier wire") from exc
        found = [index for index, row in enumerate(rows) if row[:7] == expected]
        if len(found) != 1:
            raise ValueError(f"source node {node['name']} has {len(found)} matching Gate rows")
        matched.append({"name": node["name"], "op": node["op"],
                        "physical_row": found[0], "in0": expected[4],
                        "in1": expected[5], "out": expected[6]})
    if len({item["physical_row"] for item in matched}) != len(matched):
        raise ValueError("two source instructions share one physical row")
    return matched


def audit(package: Path, pins: dict[str, str]) -> dict:
    with admitted_snapshot(package, pins) as (snapshot, manifest):
        check_package_record_source_relation(snapshot)
        relation = parse_record_source_fragment((snapshot / "source.s31").read_bytes())
        relation_sha = _sha((snapshot / "source.s31.json").read_bytes())
        key = parse_canonical_json((snapshot / "verification-key.json").read_bytes(),
                                   "verification-key.json")
        component = parse_canonical_json((snapshot / "component-manifest.json").read_bytes(),
                                         "component-manifest.json")
        report = parse_canonical_json((snapshot / "cost-report.json").read_bytes(),
                                      "cost-report.json")
        prover = snapshot / "bin" / f"s31-{manifest['name']}-prover"
        topology = json.loads(invoke(str(prover), "inspect-topology"))
        if (key.get("schema") != "s31-verification-key-direct-record-v2" or
                topology.get("preprocessed_root") != key.get("preprocessed_root") or
                component.get("preprocessed_root") != key.get("preprocessed_root") or
                report.get("preprocessed_root") != key.get("preprocessed_root")):
            raise ValueError("record fixed-root metadata differs")
        replay_direct_topology(topology, component, report, relation_sha)
        matched = source_cells(relation, topology)
        with tempfile.TemporaryDirectory(prefix="s31-record-fixed-recommit-") as directory:
            path = Path(directory) / "fixed-columns.json"
            write_json(path, {"schema": "s31-direct-gate-fixed-columns-v1",
                              "fixed_columns": [column["values"]
                                                for column in topology["columns"]]})
            recommitted = json.loads(invoke(str(prover),
                                           "inspect-fixed-root-from-columns", str(path)))
        if (set(recommitted) != {"schema", "fixed_root"} or
                recommitted["schema"] != "s31-direct-gate-recommitted-fixed-root-v1" or
                recommitted["fixed_root"] != key["preprocessed_root"]):
            raise ValueError("recommitted native fixed columns differ from the pinned key")
        return {"schema": "s31-record-v2-source-fixed-cells-v1",
                "source_sha256": pins["text"],
                "relation_sha256": relation_sha,
                "fixed_root": recommitted["fixed_root"],
                "source_cells": matched,
                "fixed_rows": ROW_COUNT,
                "scope": "fixed columns only; no witness or PCS/FRI authentication"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    for kind in ("source", "key", "prover", "verifier", "text"):
        parser.add_argument(f"--{kind}-sha256", required=True)
    args = parser.parse_args()
    pins = {kind: getattr(args, f"{kind}_sha256") for kind in
            ("source", "key", "prover", "verifier", "text")}
    try:
        print(json.dumps(audit(args.package, pins), indent=2, sort_keys=True))
    except (OSError, ValueError, RuntimeError, KeyError, TypeError,
            json.JSONDecodeError) as exc:
        print(f"record Gate source-cell audit rejected: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
