#!/usr/bin/env python3
"""Check static tuple source bytes through a verified direct-Gate proof root."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[6]
S31 = ROOT / "src/frontends/s31"
sys.path.insert(0, str(S31 / "python"))

import s31  # noqa: E402
import package.build as package_build  # noqa: E402
from package.context import invoke, write_json  # noqa: E402
from package.fixed_root_join import proof_roots  # noqa: E402
from package.pure_native_rows import ARTIFACT, admitted_ssa, make_certificate  # noqa: E402
from package.source_relation_fragment import check_source_relation_certificate  # noqa: E402
from package.verify import verify_package  # noqa: E402

SOURCE = """circuit tuple_native(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {
    let pair = (x, y);
    let out = pair.0 + pair.1;
    out
}
"""


def _checked_lean(checker: Path, package: Path, assignment: Path) -> None:
    words = assignment.parent / "public-words.bin"
    words.write_bytes(b"".join(value.to_bytes(4, "little")
                               for value in (1, 2, 3, 4, 4, 6, 0, 0)))
    common = [str(package / "source.s31"),
              str(package / "source-relation-certificate.json"),
              str(package / "source.s31.json"), str(package / "public-abi.json")]
    subprocess.run([str(checker), "static", *common], check=True,
                   capture_output=True, text=True, timeout=45)
    subprocess.run([str(checker), "run", *common, str(assignment), str(words)],
                   check=True, capture_output=True, text=True, timeout=45)


def run(checker: Path) -> dict[str, object]:
    if not checker.is_file():
        raise FileNotFoundError(f"build the Lean checker first: {checker}")
    old_invoke = package_build.invoke

    def bounded_invoke(*args: str) -> str:
        if args[:2] == ("zig", "build"):
            args = (*args[:2], "-j8", *args[2:])
        return old_invoke(*args)

    package_build.invoke = bounded_invoke
    try:
        with tempfile.TemporaryDirectory(prefix="s31-static-tuple-native-") as directory:
            work = Path(directory)
            source = work / "tuple.s31"
            source.write_text(SOURCE)
            package = s31.build(source, work / "package", "direct-gate")
            verify_package(package)
            source_bytes = (package / "source.s31").read_bytes()
            source_cert = check_source_relation_certificate(
                source_bytes, (package / "source.s31.json").read_bytes(),
                (package / "source-relation-certificate.json").read_bytes())
            if not admitted_ssa(source_cert, source_bytes) or admitted_ssa(source_cert):
                raise AssertionError("tuple admission did not require exact source bytes")
            native_cert = make_certificate(package)
            if native_cert != json.loads((package / ARTIFACT).read_text()):
                raise AssertionError("installed tuple native certificate differs from replay")
            if (native_cert["capability"] != "source-relation-to-native-fixed-rows-only" or
                    len(native_cert["source_rows"]) != 1 or
                    native_cert["source_rows"][0]["op"] != "add" or
                    sum(native_cert["gate_counts"].values()) != 512):
                raise AssertionError("tuple did not erase to the reviewed direct-Gate roster")

            assignment = work / "assignment.json"
            s31.write_json(assignment, {"public_inputs": {"x": [1, 2], "y": [3, 4]},
                                        "private_inputs": {},
                                        "public_outputs": {"out": [4, 6]}})
            _checked_lean(checker, package, assignment)
            trial = s31.trial(package, assignment, work / "trial")
            if not trial["native_verifier_accepted"]:
                raise AssertionError("native verifier rejected tuple proof")

            manifest = json.loads((package / "manifest.json").read_text())
            key = json.loads((package / "verification-key.json").read_text())
            topology = json.loads((package / "gate-topology.json").read_text())
            prover = package / "bin" / f"s31-{manifest['name']}-prover"
            fixed_columns = [column["values"] for column in topology["columns"]]
            columns_path = work / "fixed-columns.json"
            write_json(columns_path, {"schema": "s31-direct-gate-fixed-columns-v1",
                                      "fixed_columns": fixed_columns})
            recommitted = json.loads(invoke(str(prover), "inspect-fixed-root-from-columns",
                                            str(columns_path)))
            proof = work / "trial/proof.bin"
            proof_bytes = proof.read_bytes()
            proof_fixed, _, fixed_offset = proof_roots(proof_bytes)
            if (recommitted.get("schema") != "s31-direct-gate-recommitted-fixed-root-v1" or
                    proof_fixed.hex() != native_cert["preprocessed_root"] or
                    proof_fixed.hex() != recommitted.get("fixed_root") or
                    proof_fixed.hex() != key.get("preprocessed_root")):
                raise AssertionError("source-derived fixed cells differ from accepted proof root")

            # Change the actual commitment in the supplied proof, then ask
            # the same native verifier to check the same public statement.
            changed = bytearray(proof_bytes)
            changed[fixed_offset] ^= 1
            changed_path = work / "changed-proof.bin"
            changed_path.write_bytes(changed)
            verifier = package / "bin" / f"s31-{manifest['name']}-native-verifier"
            rejected = subprocess.run((str(verifier), str(changed_path),
                                       str(work / "trial/statement.json"),
                                       str(package / "verification-key.json")),
                                      capture_output=True, text=True, check=False, timeout=120)
            if (rejected.returncode == 0 or
                    rejected.stderr.strip() != "error: InvalidPreprocessedRoot"):
                raise AssertionError("native verifier did not reject the changed fixed root")

            changed_source = SOURCE.replace("pair.0 + pair.1", "pair.0 + pair.0").encode()
            try:
                check_source_relation_certificate(
                    changed_source, (package / "source.s31.json").read_bytes(),
                    (package / "source-relation-certificate.json").read_bytes())
            except ValueError:
                pass
            else:
                raise AssertionError("changed tuple projection retained exact-byte certificate")
            return {"schema": "s31-static-tuple-native-rows-v1",
                    "lean_source_and_run_accepted": True,
                    "source_rows": native_cert["source_rows"],
                    "fixed_root": proof_fixed.hex(),
                    "fixed_root_recommitted": True,
                    "native_proof_verified": True,
                    "changed_fixed_commitment_rejected": True,
                    "changed_source_projection_rejected": True,
                    "proof_bytes": trial["proof_bytes"]}
    finally:
        package_build.invoke = old_invoke


if __name__ == "__main__":
    checker = (Path(sys.argv[1]) if len(sys.argv) == 2 else
               ROOT / "formal/s31/.lake/build/bin/s31-general-linear-effects-package-check")
    print(json.dumps(run(checker.resolve()), sort_keys=True))
