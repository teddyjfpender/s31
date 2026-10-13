#!/usr/bin/env python3
"""Build a short-lane direct package and reject re-sealed native-row forgeries.

This checks package admission, not PCS/FRI soundness. The source has add,
sub, mul, a three-lane public input and a three-lane public output.
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

from package.build import build_text  # noqa: E402
from package.pure_native_rows import make_certificate  # noqa: E402
from package.verify import verify_package  # noqa: E402

SOURCE = ("circuit three(public x: [m31; 3]) -> public [m31; 3] { "
          "let a = x + x; let b = a - x; let c = a .* b; c }\n")


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def reseal(package: Path, name: str, value: object) -> None:
    path = package / name
    path.write_bytes(encoded(value))
    manifest_path = package / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    manifest["artifacts"][name] = hashlib.sha256(path.read_bytes()).hexdigest()
    manifest_path.write_bytes(encoded(manifest))


def must_reject(package: Path, contains: str) -> None:
    try:
        make_certificate(package)
    except ValueError as exc:
        if contains not in str(exc):
            raise AssertionError(f"wrong rejection: {exc}") from exc
    else:
        raise AssertionError("forged row plan entered the native certificate")
    try:
        verify_package(package)
    except ValueError:
        pass
    else:
        raise AssertionError("forged package passed ordinary verification")


def run(work: Path, existing: Path | None) -> dict:
    package = existing if existing is not None else work / "package"
    if existing is None:
        source = work / "short3.s31"
        source.write_text(SOURCE)
        build_text(source, package, "direct-gate")
    if (package / "source.s31").read_text() != SOURCE:
        raise AssertionError("test package has unexpected source")
    verified = verify_package(package)
    certificate = make_certificate(package)
    if (certificate["lane_count"] != 3 or
            [item["op"] for item in certificate["source_rows"]] !=
            ["add", "sub", "mul"]):
        raise AssertionError("native source row roster differs from test graph")

    topology = json.loads((package / "gate-topology.json").read_bytes())
    source_rows = certificate["source_rows"]
    if len({row["trace_row"] for row in source_rows}) != 3:
        raise AssertionError("source rows overlap")
    for label, mutate, expected in (
        ("selector", lambda t: t["columns"][0]["values"].__setitem__(
            source_rows[0]["trace_row"], 0), "selector/address columns differ"),
        ("operand", lambda t: t["sub"][0].__setitem__("in1", 20),
         "selector/address columns differ"),
        ("public-copy", lambda t: t["add"][3].__setitem__("in0", 0),
         "selector/address columns differ"),
        ("extra-row", lambda t: t["add"].append({"in0": 1, "in1": 1, "out": 511}),
         "row layout differs"),
    ):
        forged = work / f"forged-{label}"
        shutil.copytree(package, forged)
        changed = json.loads(encoded(topology))
        mutate(changed)
        reseal(forged, "gate-topology.json", changed)
        must_reject(forged, expected)
        shutil.rmtree(forged)

    forged = work / "forged-certificate"
    shutil.copytree(package, forged)
    changed = json.loads((forged / "pure-native-rows-certificate.json").read_bytes())
    changed["source_rows"][0]["op"] = "mul"
    reseal(forged, "pure-native-rows-certificate.json", changed)
    try:
        verify_package(forged)
    except ValueError as exc:
        if "certificate differs from replay" not in str(exc):
            raise AssertionError(f"wrong certificate rejection: {exc}") from exc
    else:
        raise AssertionError("re-sealed wrong certificate passed verification")
    shutil.rmtree(forged)
    return {"schema": "s31-short-lane-native-controls-v1",
            "source_rows": source_rows, "forgeries_rejected": 5,
            "honest_package_verified": verified["schema"] == "s31-package-v1"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path)
    parser.add_argument("--package", type=Path)
    args = parser.parse_args()
    if args.work:
        work = args.work.resolve()
        work.mkdir(parents=True, exist_ok=True)
        result = run(work, args.package.resolve() if args.package else None)
    else:
        with tempfile.TemporaryDirectory(prefix="s31-pure-short-native-") as temporary:
            result = run(Path(temporary), args.package.resolve() if args.package else None)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
