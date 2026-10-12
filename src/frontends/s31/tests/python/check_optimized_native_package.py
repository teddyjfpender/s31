"""Opt-in native direct-gate package smoke test for reversed/CSE source.

Run explicitly on a clean pinned Stwo dependency. The normal package builder
remains v2-only; this script attaches the separate v3 correspondence artifact
to a temporary package and checks a resealed native-report mutation.
"""

from __future__ import annotations

import json
import shutil
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.build import build
from package.context import file_hash, invoke, write_json
from package.correspondence import (check_optimized_package, digest,
                                    make_optimized_certificate)

SOURCE = ("circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] { "
          "let a = x + x; let b = x .* x; let c = a + b; "
          "let d = b + a; d }\n")
CANONICAL_DIGEST = "2088c1bad15f2ba5b52f0214e9d3d66744b9c84aa6218aa336d8b337157e7132"


def attach_v3(package: Path) -> None:
    topology = json.loads(invoke(
        str(package / "bin" / "s31-reverse_share-prover"), "inspect-topology"))
    topology_path = package / "gate-topology.json"
    write_json(topology_path, topology)
    manifest_path = package / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    manifest["artifacts"][topology_path.name] = file_hash(topology_path)
    write_json(manifest_path, manifest)

    certificate_path = package / "correspondence-certificate.json"
    write_json(certificate_path, make_optimized_certificate(package))
    manifest["artifacts"][certificate_path.name] = file_hash(certificate_path)
    write_json(manifest_path, manifest)


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="s31-optimized-native-") as directory:
        root = Path(directory)
        source = root / "reverse_share.s31"
        source.write_text(SOURCE)
        package = build(source, root / "package", "direct-gate")
        if (package / "correspondence-certificate.json").exists():
            raise AssertionError("default v2 builder unexpectedly admitted optimized source")
        attach_v3(package)
        checked = check_optimized_package(package)
        if (checked["source_ssa"]["source_to_canonical"] != [0, 1, 2, 3, 3] or
                checked["key_core"]["canonical_ir_sha256"] != CANONICAL_DIGEST or
                [(row["qm31_start"], row["qm31_end"])
                 for row in checked["gate_schedule"]] !=
                [(0, 6), (6, 7), (7, 8), (8, 9)]):
            raise AssertionError("native optimized certificate differs from pinned fixture")

        forged = root / "forged"
        shutil.copytree(package, forged)
        report_path = forged / "cost-report.json"
        report = json.loads(report_path.read_text())
        report["source_map"][-1]["qm31_start"] = 9
        write_json(report_path, report)
        manifest_path = forged / "manifest.json"
        manifest = json.loads(manifest_path.read_text())
        manifest["artifacts"][report_path.name] = file_hash(report_path)
        write_json(manifest_path, manifest)
        if manifest["artifacts"][report_path.name] != digest(report_path.read_bytes()):
            raise AssertionError("forged cost report was not resealed")
        try:
            check_optimized_package(forged)
        except ValueError as error:
            if "native gate spans differ" not in str(error):
                raise
        else:
            raise AssertionError("resealed malformed native source map was admitted")
        print("optimized native package accepted; resealed bad source span rejected")


if __name__ == "__main__":
    main()
