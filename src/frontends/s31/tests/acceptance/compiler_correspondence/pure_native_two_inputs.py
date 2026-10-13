#!/usr/bin/env python3
"""Build a two-public-input Gate package and reject re-sealed row forgeries."""

from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import struct
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from package.build import build_text  # noqa: E402
from package.manifest_digest import direct_gate_v2_digest  # noqa: E402
from package.pure_native_rows import make_certificate  # noqa: E402
from package.verify import verify_package  # noqa: E402

SOURCE = ("circuit duo2(public x: [m31; 2], public y: [m31; 2]) "
          "-> public [m31; 2] { let a = x + y; let b = a - x; "
          "let c = y .* a; c }\n")


def encoded(value: object) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()


def reseal(package: Path, changes: dict[str, object]) -> None:
    manifest_path = package / "manifest.json"
    manifest = json.loads(manifest_path.read_bytes())
    for name, value in changes.items():
        path = package / name
        path.write_bytes(encoded(value))
        manifest["artifacts"][name] = hashlib.sha256(path.read_bytes()).hexdigest()
    manifest_path.write_bytes(encoded(manifest))


def reject(package: Path, expected: str) -> None:
    try:
        make_certificate(package)
    except ValueError as exc:
        if expected not in str(exc):
            raise AssertionError(f"wrong independent rejection: {exc}") from exc
    else:
        raise AssertionError("forgery passed independent native-row replay")
    try:
        verify_package(package)
    except ValueError:
        pass
    else:
        raise AssertionError("forgery passed package verification")


def run(work: Path, existing: Path | None) -> dict:
    package = existing if existing is not None else work / "package"
    if existing is None:
        source = work / "duo2.s31"
        source.write_text(SOURCE)
        build_text(source, package, "direct-gate")
    if (package / "source.s31").read_text() != SOURCE:
        raise AssertionError("test package has unexpected source")
    verify_package(package)
    certificate = make_certificate(package)
    if (certificate["lane_count"] != 2 or
            certificate["source_rows"][0]["id"] != 2 or
            [item["op"] for item in certificate["source_rows"]] !=
            ["add", "sub", "mul"] or
            sum(certificate["gate_counts"].values()) != 512):
        raise AssertionError("source-derived two-input row roster changed")
    assignment = work / "assignment.json"
    s31.write_json(assignment, {
        "public_inputs": {"x": [2, 3], "y": [5, 7]},
        "private_inputs": {}, "public_outputs": {"c": [35, 70]},
    })
    proof = s31.trial(package, assignment, work / "proof")
    if not proof["native_verifier_accepted"]:
        raise AssertionError("native verifier rejected the honest two-input proof")

    topology = json.loads((package / "gate-topology.json").read_bytes())
    source_row = certificate["source_rows"][0]["trace_row"]
    forged = work / "forged-selector"
    shutil.copytree(package, forged)
    mutant = json.loads(encoded(topology))
    mutant["columns"][0]["values"][source_row] = 0
    reseal(forged, {"gate-topology.json": mutant})
    reject(forged, "selector/address columns differ")
    shutil.rmtree(forged)

    forged = work / "forged-public-binding"
    shutil.copytree(package, forged)
    report = json.loads((forged / "cost-report.json").read_bytes())
    report["public_binding"][1]["word_start"] = 0
    reseal(forged, {"cost-report.json": report})
    reject(forged, "public word projection differs")
    shutil.rmtree(forged)

    forged = work / "forged-public-abi-order"
    shutil.copytree(package, forged)
    abi = json.loads((forged / "public-abi.json").read_bytes())
    abi["public_inputs"].reverse()
    reseal(forged, {"public-abi.json": abi})
    reject(forged, "public ABI differs")
    shutil.rmtree(forged)

    # Swap the source add operands. Its arithmetic meaning and address use
    # counts are unchanged. Update both fixed columns, their component
    # digests, both key/report copies and a matching declared root. The
    # independent source-derived schedule must still reject the altered row.
    forged = work / "forged-self-consistent-row"
    shutil.copytree(package, forged)
    mutant = json.loads(encoded(topology))
    gate = mutant["add"][source_row]
    gate["in0"], gate["in1"] = gate["in1"], gate["in0"]
    for index, field in ((4, "in0"), (5, "in1")):
        mutant["columns"][index]["values"][source_row] = gate[field]
    component = json.loads((forged / "component-manifest.json").read_bytes())
    fake_root = "a" * 64
    mutant["preprocessed_root"] = fake_root
    component["preprocessed_root"] = fake_root
    for index in (4, 5):
        values = mutant["columns"][index]["values"]
        component["preprocessed_columns"][index]["values_sha256"] = hashlib.sha256(
            b"".join(struct.pack("<I", value) for value in values)).hexdigest()
    key = json.loads((forged / "verification-key.json").read_bytes())
    report = json.loads((forged / "cost-report.json").read_bytes())
    key["preprocessed_root"] = fake_root
    report["preprocessed_root"] = fake_root
    key["component_manifest"] = component
    report["component_manifest"] = component
    digest = direct_gate_v2_digest(component)
    key["manifest_precommitment_sha256"] = digest
    report["manifest_precommitment_sha256"] = digest
    reseal(forged, {"gate-topology.json": mutant,
                    "component-manifest.json": component,
                    "verification-key.json": key,
                    "cost-report.json": report})
    reject(forged, "native gates differ from source-derived full schedule")
    shutil.rmtree(forged)
    return {"schema": "s31-two-public-input-native-controls-v1",
            "honest_package_verified": True, "forgeries_rejected": 4,
            "native_proof_verified": True, "proof_bytes": proof["proof_bytes"],
            "source_rows": certificate["source_rows"]}


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
        with tempfile.TemporaryDirectory(prefix="s31-pure-two-native-") as temporary:
            result = run(Path(temporary), args.package.resolve() if args.package else None)
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
