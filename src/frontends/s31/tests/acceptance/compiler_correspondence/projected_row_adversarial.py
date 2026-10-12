#!/usr/bin/env python3
"""Reject resealed changes to source-owned direct-Gate fixed rows.

The native inspector exports the fixed columns, while package admission
independently replays the source's gate schedule. These controls change a
projected source cell and update the package's artifact hash so rejection
cannot be attributed to a stale JSON digest alone.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(S31 / "tests/python/generated"))

import s31
from package.correspondence import check_package
from package.verify import verify_package
from test_source_mutation_correspondence import CORPUS_SHA256, corpus, corpus_digest
from native_source_cells import expected_cells

LABEL = "07:aliases"
ROW_REPLAY_ERROR = "emitted direct-gate selector/address columns differ from gate replay"


def write_json(path: Path, value: dict) -> None:
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def reseal_topology(package: Path, topology: dict) -> None:
    topology_path = package / "gate-topology.json"
    write_json(topology_path, topology)
    manifest_path = package / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["artifacts"][topology_path.name] = sha(topology_path)
    write_json(manifest_path, manifest)
    # The changed topology is listed with its *current* digest. Other package
    # artifacts, including the original native verifier, remain byte-identical.
    for name, digest in manifest["artifacts"].items():
        if sha(package / name) != digest:
            raise AssertionError(f"forged package has a stale artifact digest: {name}")


def reject_at_row_replay(package: Path) -> str:
    for admit in (check_package, verify_package):
        try:
            admit(package)
        except ValueError as exc:
            if str(exc) != ROW_REPLAY_ERROR:
                raise AssertionError(
                    f"{admit.__name__} rejected at an unexpected stage: {exc}") from exc
        else:
            raise AssertionError(f"{admit.__name__} admitted a changed source fixed row")
    return ROW_REPLAY_ERROR


def run(work: Path) -> dict:
    samples = corpus()
    if corpus_digest(samples) != CORPUS_SHA256:
        raise AssertionError("pinned source mutation corpus changed")
    sample = next((entry for entry in samples if entry.label == LABEL), None)
    if sample is None:
        raise AssertionError("pinned alias source is absent")
    cells = expected_cells(sample)
    if len(cells) < 2 or cells[0][0] == cells[1][0]:
        raise AssertionError("expected two distinct source-owned physical rows")

    source = work / "aliases.s31"
    source.write_text(sample.source + "\n")
    package = s31.build(source, work / "honest", "direct-gate")
    check_package(package)
    verify_package(package)
    prover = package / "bin" / f"s31-{json.loads((package / 'manifest.json').read_text())['name']}-prover"
    exported = json.loads(s31.invoke(str(prover), "inspect-topology"))
    sealed = json.loads((package / "gate-topology.json").read_text())
    if exported != sealed:
        raise AssertionError("honest topology differs from fresh native export")

    # First source instruction is an add at physical row 3. Change only its
    # opcode selector to pointwise multiplication. The sealed file digest is
    # updated, but the source-derived gate replay still expects an add flag.
    first = cells[0]
    if first[1:5] != [1, 0, 0, 0]:
        raise AssertionError("pinned first source operation is no longer add")
    opcode_dir = work / "forged-opcode"
    shutil.copytree(package, opcode_dir)
    opcode = json.loads((opcode_dir / "gate-topology.json").read_text())
    row = first[0]
    opcode["columns"][0]["values"][row] = 0
    opcode["columns"][3]["values"][row] = 1
    reseal_topology(opcode_dir, opcode)
    opcode_error = reject_at_row_replay(opcode_dir)

    # Move the first source instruction to the second source row by swapping
    # all eight fixed cells. This keeps both rows' selectors, addresses, and
    # multiplicities canonical and leaves the row count unchanged.
    moved_dir = work / "forged-row-position"
    shutil.copytree(package, moved_dir)
    moved = json.loads((moved_dir / "gate-topology.json").read_text())
    first_row, second_row = cells[0][0], cells[1][0]
    for column in moved["columns"]:
        column["values"][first_row], column["values"][second_row] = (
            column["values"][second_row], column["values"][first_row])
    reseal_topology(moved_dir, moved)
    position_error = reject_at_row_replay(moved_dir)

    return {"schema": "s31-projected-row-adversarial-v1",
            "source": LABEL, "source_rows": [first_row, second_row],
            "honest_package_admitted": True,
            "opcode_selector_rejected_at": opcode_error,
            "row_position_rejected_at": position_error,
            "resealed_artifact_hashes_checked": True}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, help="retain native package and forged copies")
    args = parser.parse_args()
    if args.work:
        work = args.work.resolve()
        work.mkdir(parents=True, exist_ok=True)
        result = run(work)
    else:
        with tempfile.TemporaryDirectory(prefix="s31-projected-row-") as temp:
            result = run(Path(temp))
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
