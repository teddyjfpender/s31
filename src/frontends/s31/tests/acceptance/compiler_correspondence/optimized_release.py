#!/usr/bin/env python3
"""Explicit v3 optimization must save gates and admit an authenticated native proof."""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
from package.correspondence import (OPTIMIZED_SCHEMA, check_optimized_package,
                                    parse_source_optimized)  # noqa: E402
from package.trust import pinned_paths  # noqa: E402
from functional_release import SAME_AIR  # noqa: E402

EXAMPLE = S31 / "examples/functional/release_optimized4"
P = (1 << 31) - 1


def run(example: Path = EXAMPLE, *, case: str = "straightline",
        source_to_canonical: tuple[int, ...] = (0, 1, 2, 3, 3, 4),
        source_lets: int = 5) -> dict:
    source = example / "functional.s31"
    manual_source = example / "manual.s31"
    relation, syntax = parse_source_optimized(source.read_bytes())
    _, manual_syntax = parse_source_optimized(manual_source.read_bytes())
    if (syntax["source_to_canonical"] != list(source_to_canonical) or
            len(relation["nodes"]) != source_lets or
            len(syntax["instructions"]) != 4 or
            len(manual_syntax["instructions"]) != 4):
        raise AssertionError("source operations were not shared as expected")

    with tempfile.TemporaryDirectory(prefix="s31-optimized-release-") as directory:
        work = Path(directory)
        manual = s31.build(manual_source, work / "manual", "direct-gate")
        package = s31.build(source, work / "optimized", "direct-gate",
                            correspondence="optimized")
        manifest = s31.verify_package(package)
        if manifest.get("correspondence_schema") != OPTIMIZED_SCHEMA:
            raise AssertionError("optimized package is missing its v3 marker")
        try:
            s31.build(source, package, "direct-gate")
        except FileExistsError:
            pass
        else:
            raise AssertionError("conservative build reused an optimized package")
        checked = check_optimized_package(package)
        if (checked["source_ssa"] != syntax or
                checked["relation_sha256"] != s31.sha256((package / "source.s31.json").read_bytes()) or
                checked["status"]["native_root_binding"] !=
                "native-reported-fixed-root-matches-key"):
            raise AssertionError("optimized package lacks rooted source correspondence")

        manual_cost = json.loads((manual / "cost-report.json").read_text())
        cost = json.loads((package / "cost-report.json").read_text())
        different = [field for field in SAME_AIR if cost[field] != manual_cost[field]]
        if different:
            raise AssertionError(f"optimized source changed native AIR geometry: {different}")
        if cost["raw"]["qm31_ops"] != 324 or cost["padded"]["qm31_ops"] != 512:
            raise AssertionError("optimized source exceeded its pinned direct-gate AIR cost")
        if cost["canonical_ir_sha256"] != checked["key_core"]["canonical_ir_sha256"]:
            raise AssertionError("native canonical IR differs from checked source")

        values = [0, 1, 2, 7]
        expected = [(4 * value + 2 * value * value) % P for value in values]
        assignment = work / "assignment.json"
        s31.write_json(assignment, {"public_inputs": {"x": values},
                                    "private_inputs": {}, "public_outputs": {"e": expected}})
        trial = s31.trial(package, assignment, work / "proof")
        if not trial["native_verifier_accepted"]:
            raise AssertionError("optimized package native proof was rejected")

        pins = {kind: s31.file_hash(path) for kind, path in pinned_paths(package).items()}
        flags = [item for kind, digest in pins.items() for item in (f"--{kind}-sha256", digest)]
        command = [sys.executable, str(S31 / "python/s31.py"), "verify-release",
                   str(package), str(work / "proof/proof.bin"), "--statement",
                   str(work / "proof/statement.json"), *flags]
        s31.invoke(*command)

        changed_statement = work / "changed-statement.json"
        s31.write_json(changed_statement, {"public_inputs": {"x": values},
                                           "public_outputs": {"e": [0, 6, 16, 127]}})
        changed_command = command.copy()
        changed_command[changed_command.index(str(work / "proof/statement.json"))] = str(changed_statement)
        try:
            s31.invoke(*changed_command)
        except RuntimeError:
            pass
        else:
            raise AssertionError("strict release verifier accepted a false public output")

        # A v3 package cannot silently fall back to the conservative checker.
        manifest_path = package / "manifest.json"
        original_manifest = manifest_path.read_bytes()
        try:
            for marker in (None, "unknown-correspondence-v99", "missing-certificate"):
                changed_manifest = json.loads(original_manifest)
                if marker is None:
                    changed_manifest.pop("correspondence_schema")
                elif marker == "missing-certificate":
                    changed_manifest["artifacts"].pop("correspondence-certificate.json")
                else:
                    changed_manifest["correspondence_schema"] = marker
                s31.write_json(manifest_path, changed_manifest)
                try:
                    s31.verify_package(package)
                except ValueError:
                    pass
                else:
                    raise AssertionError(f"correspondence schema {marker!r} was admitted")
        finally:
            manifest_path.write_bytes(original_manifest)

        return {"schema": "s31-optimized-release-v1", "case": case,
                "source_lets": source_lets, "native_arithmetic_gates": 4,
                "raw_qm31_rows": cost["raw"]["qm31_ops"],
                "padded_qm31_rows": cost["padded"]["qm31_ops"],
                "proof_bytes": trial["proof_bytes"],
                "optimized_and_manual_air_equal": True,
                "rooted_v3_certificate_checked": True,
                "strict_release_proof_accepted": True,
                "changed_public_claim_rejected": True,
                "certificate_downgrade_rejected": True}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
