#!/usr/bin/env python3
"""Check source-bound helper/tuple erasure against native direct-Gate rows."""

from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))
sys.path.insert(0, str(ROOT))

import s31  # noqa: E402
import package.build as package_build  # noqa: E402
from package.fixed_root_join import proof_roots  # noqa: E402
from package.pure_native_rows import (ARTIFACT, STRUCTURAL_SCHEMA,  # noqa: E402
                                      admitted_source_package, make_certificate)
from package.source_relation_fragment import (LEAN_EFFECTS_PROFILE,  # noqa: E402
                                              check_source_relation_certificate)
from package.structural_derivation import (ARTIFACT as STRUCTURAL_ARTIFACT,  # noqa: E402
                                           check_certificate, evaluate_assignment)
from package.verify import verify_package  # noqa: E402
from package.trust import pinned_paths  # noqa: E402
from scripts.release.structural_lean_release import verify as verify_structural_release  # noqa: E402

SOURCE = """fn subtract(a: [m31; 2], b: [m31; 2]) -> [m31; 2] { a - b }
circuit combined_native(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {
    let pair = (x, y);
    let left = pair.0;
    let right = pair.1;
    let out = subtract(left, right);
    out
}
"""
FLAT = """circuit combined_native(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {
    let out = x - y;
    out
}
"""
AIR_FIELDS = ("canonical_ir_sha256", "profile", "chip", "raw", "padded",
              "preprocessed_cells", "preprocessed_columns", "preprocessed_root",
              "input_packing", "public_binding", "finalization", "fri")


def read(package: Path, name: str) -> dict:
    return json.loads((package / name).read_bytes())


def run() -> dict[str, object]:
    old_invoke = package_build.invoke

    def bounded_invoke(*args: str) -> str:
        if args[:2] == ("zig", "build"):
            args = (*args[:2], "-j4", *args[2:])
        return old_invoke(*args)

    package_build.invoke = bounded_invoke
    try:
        with tempfile.TemporaryDirectory(prefix="s31-combined-native-") as directory:
            work = Path(directory)
            combined_source, flat_source = work / "combined.s31", work / "flat.s31"
            combined_source.write_text(SOURCE)
            flat_source.write_text(FLAT)
            combined = s31.build(combined_source, work / "combined", "direct-gate")
            flat = s31.build(flat_source, work / "flat", "direct-gate")
            verify_package(combined)
            verify_package(flat)
            source_certificate = combined / "source-relation-certificate.json"
            if not source_certificate.is_file():
                raise AssertionError("combined helper/tuple lacks an effects source certificate")
            enrolled = check_source_relation_certificate(
                (combined / "source.s31").read_bytes(),
                (combined / "source.s31.json").read_bytes(),
                source_certificate.read_bytes())
            if enrolled["lean_semantic_profile"] != LEAN_EFFECTS_PROFILE:
                raise AssertionError("combined source did not enter Lean effects profile")
            if not admitted_source_package(combined):
                raise AssertionError("exact combined source did not enter native row checker")
            cert = make_certificate(combined)
            flat_cert = make_certificate(flat)
            if (cert != read(combined, ARTIFACT) or cert["schema"] != STRUCTURAL_SCHEMA or
                    cert["capability"] != "typed-structural-to-native-fixed-rows-only" or
                    "typed_structural_derivation_sha256" not in cert or
                    "source_relation_certificate_sha256" in cert or
                    flat_cert["source_rows"] != cert["source_rows"] or
                    len(cert["source_rows"]) != 1 or
                    cert["source_rows"][0]["op"] != "sub" or
                    sum(cert["gate_counts"].values()) != 512):
                raise AssertionError("combined source did not erase to one reviewed subtraction")
            combined_topology = read(combined, "gate-topology.json")
            flat_topology = read(flat, "gate-topology.json")
            if (combined_topology["columns"] != flat_topology["columns"] or
                    cert["preprocessed_root"] != flat_cert["preprocessed_root"] or
                    any(read(combined, "cost-report.json")[field] !=
                        read(flat, "cost-report.json")[field] for field in AIR_FIELDS)):
                raise AssertionError("helper/tuple syntax changed native AIR rows or cost")

            source_bytes = (combined / "source.s31").read_bytes()
            relation_bytes = (combined / "source.s31.json").read_bytes()
            abi_bytes = (combined / "public-abi.json").read_bytes()
            structural_bytes = (combined / STRUCTURAL_ARTIFACT).read_bytes()
            check_certificate(source_bytes, relation_bytes, abi_bytes,
                              "direct-gate", structural_bytes)
            assignment = work / "assignment.json"
            s31.write_json(assignment, {"public_inputs": {"x": [7, 11], "y": [3, 5]},
                                        "private_inputs": {},
                                        "public_outputs": {"out": [4, 6]}})
            if evaluate_assignment(source_bytes, relation_bytes, abi_bytes, "direct-gate",
                                   structural_bytes, assignment.read_bytes())["public_words"] != [
                                       7, 11, 3, 5, 4, 6, 0, 0]:
                raise AssertionError("checked combined source value differs from public ABI")
            trial = s31.trial(combined, assignment, work / "trial")
            if trial["native_verifier_accepted"] is not True:
                raise AssertionError("native verifier rejected combined proof")
            checker = ROOT / "formal/s31/.lake/build/bin/s31-general-linear-structural-check"
            if not checker.is_file():
                raise AssertionError("structural release requires the built Lean checker")
            checker_pin = hashlib.sha256(checker.read_bytes()).hexdigest()
            pins = {kind: hashlib.sha256(path.read_bytes()).hexdigest()
                    for kind, path in pinned_paths(combined).items()}
            release_script = ROOT / "scripts/release/structural_lean_release.py"
            release_script_sha256 = hashlib.sha256(release_script.read_bytes()).hexdigest()
            release_command = [
                sys.executable, str(release_script),
                str(combined), str(work / "trial/proof.bin"),
                "--statement", str(work / "trial/statement.json"),
                "--lean-checker", str(checker),
                "--lean-checker-sha256", checker_pin,
            ]
            for kind, digest in pins.items():
                release_command.extend((f"--{kind}-sha256", digest))
            released = subprocess.run(release_command, cwd=ROOT,
                                      capture_output=True, text=True,
                                      timeout=120, check=False)
            if released.returncode or not released.stdout.strip():
                raise AssertionError("strict Lean structural release failed: "
                                     f"{released.stdout} {released.stderr}")
            if hashlib.sha256(release_script.read_bytes()).hexdigest() != release_script_sha256:
                raise AssertionError("structural release script changed during native trial")
            try:
                verify_structural_release(
                    combined, work / "trial/proof.bin", work / "trial/statement.json",
                    pins, checker, "0" * 64)
            except ValueError as exc:
                if "pin mismatch" not in str(exc):
                    raise
            else:
                raise AssertionError("structural release accepted an untrusted Lean checker")
            missing = work / "missing-structural"
            shutil.copytree(combined, missing)
            (missing / STRUCTURAL_ARTIFACT).unlink()
            try:
                verify_structural_release(
                    missing, work / "trial/proof.bin", work / "trial/statement.json",
                    pins, checker, checker_pin)
            except (ValueError, FileNotFoundError):
                pass
            else:
                raise AssertionError("structural release accepted a missing typed tree")
            proof_bytes = (work / "trial/proof.bin").read_bytes()
            proof_fixed, _, main_offset = proof_roots(proof_bytes)
            fixed_offset = main_offset - len(proof_fixed)
            if proof_fixed.hex() != cert["preprocessed_root"]:
                raise AssertionError("accepted proof fixed root differs from checked rows")
            changed = bytearray(proof_bytes)
            changed[fixed_offset] ^= 1
            changed_path = work / "changed-proof.bin"
            changed_path.write_bytes(changed)
            manifest = read(combined, "manifest.json")
            verifier = combined / "bin" / f"s31-{manifest['name']}-native-verifier"
            rejected = subprocess.run((str(verifier), str(changed_path),
                                       str(work / "trial/statement.json"),
                                       str(combined / "verification-key.json")),
                                      capture_output=True, text=True, check=False,
                                      timeout=120)
            if (rejected.returncode == 0 or
                    rejected.stderr.strip() != "error: InvalidPreprocessedRoot"):
                raise AssertionError("changed fixed root was not rejected")
            return {"schema": "s31-combined-helper-tuple-native-rows-v1",
                    "source_rows": cert["source_rows"],
                    "fixed_root": proof_fixed.hex(),
                    "flat_air_equal": True,
                    "native_proof_verified": True,
                    "structural_lean_release_verified": True,
                    "structural_lean_checker_sha256": checker_pin,
                    "structural_release_script_sha256": release_script_sha256,
                    "wrong_checker_pin_rejected": True,
                    "missing_structural_tree_rejected": True,
                    "changed_fixed_root_rejected": True,
                    "proof_bytes": trial["proof_bytes"]}
    finally:
        package_build.invoke = old_invoke


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True))
