#!/usr/bin/env python3
"""Export and optionally Lean-check compact IR bytes from a bounded package.

This audit utility copies a package to private storage, checks its internal
manifest and independent direct-gate correspondence certificate, then derives
the compact canonical IR from the copied source. It does not authenticate the
package's publisher or replace native proof verification.

Usage:
  python3 export_package_canonical_ir.py PACKAGE --output canonical-ir.json
  python3 export_package_canonical_ir.py PACKAGE --output canonical-ir.json --lean-check
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
ROOT = S31.parents[2]
FORMAL = ROOT / "formal/s31"
sys.path.insert(0, str(S31 / "python"))

from package.correspondence import (canonical_ir_bytes, check_package,
                                    parse_source, read_canonical_json)
from package.trust import unpinned_snapshot


def export(package: Path, output: Path, lean_checker: Path | None = None) -> dict:
    """Export bytes only after all package copies agree on the IR digest."""
    package = package.resolve()
    output = output.resolve()
    if output == package or package in output.parents:
        raise ValueError("audit output must be outside the original package")
    if output.exists():
        raise FileExistsError(f"audit output already exists: {output}")
    if not output.parent.is_dir():
        raise FileNotFoundError(f"audit output directory does not exist: {output.parent}")

    with unpinned_snapshot(package) as (snapshot, manifest):
        if (manifest.get("lowering") != "direct-gate" or
                "source_text_sha256" not in manifest):
            raise ValueError("audit requires a bounded direct-gate text package")
        certificate = check_package(snapshot)
        source = (snapshot / "source.s31").read_bytes()
        normalized = (snapshot / "source.s31.json").read_bytes()
        relation, syntax = parse_source(source)
        expected_normalized = (json.dumps(relation, indent=2, sort_keys=True) + "\n").encode("ascii")
        if normalized != expected_normalized or syntax != certificate["source_ssa"]:
            raise ValueError("package relation or SSA differs from independent source parse")
        ir = canonical_ir_bytes(syntax)
        ir_digest = hashlib.sha256(ir).hexdigest()
        for name in ("manifest.json", "verification-key.json", "cost-report.json",
                     "component-manifest.json"):
            record = read_canonical_json(snapshot / name)
            if record.get("canonical_ir_sha256") != ir_digest:
                raise ValueError(f"{name} canonical IR digest differs from source")

        lean_checked = False
        if lean_checker is not None:
            if not lean_checker.is_file():
                raise FileNotFoundError(
                    f"Lean checker missing: {lean_checker}; run "
                    "cd formal/s31 && lake build s31-alias-relation-check")
            with tempfile.TemporaryDirectory(prefix="s31-ir-audit-") as directory:
                ir_path = Path(directory) / "canonical-ir.json"
                ir_path.write_bytes(ir)
                result = subprocess.run([
                    str(lean_checker), str(snapshot / "source.s31"),
                    str(snapshot / "source.s31.json"), str(ir_path),
                ], text=True, capture_output=True, check=False)
            try:
                report = json.loads(result.stdout)
            except json.JSONDecodeError as exc:
                raise ValueError(f"Lean checker did not return JSON: {result.stderr}") from exc
            expected_gates = [
                {"id": step["id"], "lhs": step["lhs"], "rhs": step["rhs"],
                 "op": step["op"]}
                for step in syntax["instructions"]
            ]
            if (result.returncode != 0 or report.get("accepted") is not True or
                    report.get("checker") != "AliasCanonicalIrBytes.checkAliasCanonical" or
                    report.get("output_wire") != syntax["output"] or
                    report.get("gates") != expected_gates):
                raise ValueError(f"Lean three-file audit rejected package: {report}; "
                                 f"stderr: {result.stderr}")
            lean_checked = True

    with output.open("xb") as exported:
        exported.write(ir)
    return {"canonical_ir_sha256": ir_digest,
            "gates": len(syntax["instructions"]),
            "lean_checked": lean_checked,
            "output": str(output)}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("package", type=Path)
    parser.add_argument("--output", type=Path, required=True,
                        help="new path for exact compact canonical IR bytes")
    parser.add_argument("--lean-check", action="store_true",
                        help="also run the built three-file Lean checker")
    args = parser.parse_args()
    checker = (FORMAL / ".lake/build/bin/s31-alias-relation-check"
               if args.lean_check else None)
    try:
        result = export(args.package, args.output, checker)
    except (OSError, RuntimeError, ValueError, KeyError) as exc:
        parser.exit(1, f"canonical IR audit: {exc}\n")
    print(json.dumps(result, sort_keys=True))


if __name__ == "__main__":
    main()
