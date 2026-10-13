#!/usr/bin/env python3
"""Native fixed-column smoke test for public and private scalar records."""

from __future__ import annotations

import copy
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tools/audit"))

import s31  # noqa: E402
from record_source_cells import audit, source_cells  # noqa: E402

CASES = (
    ("double", """struct Box { value: [m31; 1] }
circuit double(public x: Box) -> public Box {
    let y = x.value + x.value;
    Box { value: y }
}
""", [{"name": "y", "op": "add", "physical_row": 0,
        "in0": 11, "in1": 11, "out": 14}]),
    ("paired", """struct Pair { left: [m31; 1], right: [m31; 1] }
circuit paired(public x: Pair, private y: Pair) -> public Pair {
    let z = x.left .* y.right;
    Pair { right: x.right, left: z }
}
""", [{"name": "z", "op": "mul", "physical_row": 508,
        "in0": 11, "in1": 16, "out": 17}]),
)


def pins(package: Path, name: str) -> dict[str, str]:
    paths = {"source": package / "source.s31.json",
             "key": package / "verification-key.json",
             "prover": package / "bin" / f"s31-{name}-prover",
             "verifier": package / "bin" / f"s31-{name}-native-verifier",
             "text": package / "source.s31"}
    return {kind: hashlib.sha256(path.read_bytes()).hexdigest()
            for kind, path in paths.items()}


def main() -> None:
    reports = []
    with tempfile.TemporaryDirectory(prefix="s31-record-source-cells-") as directory:
        work = Path(directory)
        for name, source, expected in CASES:
            source_path = work / f"{name}.s31"
            source_path.write_text(source)
            package = s31.build(source_path, work / f"package-{name}", "direct-gate")
            report = audit(package, pins(package, name))
            if (report["source_cells"] != expected or
                    report["fixed_rows"] != 512):
                raise AssertionError(f"{name}: source Gate cells differ from native export")
            prover = package / "bin" / f"s31-{name}-prover"
            exported = subprocess.run((str(prover), "inspect-topology"),
                                      capture_output=True, text=True, check=True)
            topology = json.loads(exported.stdout + exported.stderr)
            relation = json.loads((package / "source.s31.json").read_bytes())
            changed = copy.deepcopy(topology)
            row = expected[0]["physical_row"]
            changed["columns"][6]["values"][row] += 1
            try:
                source_cells(relation, changed)
            except ValueError:
                pass
            else:
                raise AssertionError(f"{name}: changed source output address was accepted")
            reports.append({"case": name, "fixed_root": report["fixed_root"],
                            "source_cells": expected,
                            "changed_output_address_rejected": True})
    print(json.dumps({"schema": "s31-record-v2-source-cell-native-corpus-v1",
                      "cases": reports}, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
