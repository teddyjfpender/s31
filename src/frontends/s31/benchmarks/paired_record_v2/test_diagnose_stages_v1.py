#!/usr/bin/env python3
"""Native-free integrity checks for the post-study mixed stage diagnostic."""

import json
import tempfile
import unittest
from pathlib import Path

from diagnose_stages_v1 import measure, parse_prover_stage

SOURCE = "a" * 64
REGISTRY = "b" * 64
IDENTITY = "c" * 64
MANIFEST = {
    "schema": "s31-mixed-component-inspection-general-v3",
    "source_sha256": SOURCE,
    "registry_manifest_sha256": REGISTRY,
    "circuit_identity_sha256": IDENTITY,
}
STAGES = {
    "profile_rebuild_ns": 1,
    "semantic_evaluation_ns": 2,
    "topology_compile_ns": 3,
    "witness_compile_ns": 4,
    "native_prove_including_setup_ns": 5,
    "envelope_and_serialization_ns": 6,
    "package_total_ns": 21,
}


def stage_line(*, identity: str = IDENTITY, total: int = 21) -> bytes:
    stages = {**STAGES, "package_total_ns": total}
    report = {
        "schema": "s31-mixed-general-prover-stages-v1",
        "source_sha256": SOURCE,
        "registry_manifest_sha256": REGISTRY,
        "circuit_identity_sha256": identity,
        "proof_bytes": 5,
        "statement_bytes": 3,
        "stages_ns": stages,
        "external_native_verification_ns": None,
    }
    return ("S31_MIXED_STAGE_V1 " + json.dumps(report) + "\n").encode()


def executable(path: Path, body: str) -> None:
    path.write_text("#!/usr/bin/env python3\n" + body)
    path.chmod(0o755)


class StageDiagnosticTests(unittest.TestCase):
    def test_rejects_different_source_identity_and_bad_partition(self) -> None:
        with self.assertRaisesRegex(ValueError, "source or saved artifacts"):
            parse_prover_stage(stage_line(identity="d" * 64), MANIFEST, b"proof", b"abc")
        with self.assertRaisesRegex(ValueError, "intervals are malformed"):
            parse_prover_stage(stage_line(total=20), MANIFEST, b"proof", b"abc")
        with self.assertRaisesRegex(ValueError, "exactly one"):
            parse_prover_stage(stage_line() * 2, MANIFEST, b"proof", b"abc")
        duplicate = stage_line().replace(b'"proof_bytes": 5,',
                                         b'"proof_bytes": 5, "proof_bytes": 5,')
        with self.assertRaisesRegex(ValueError, "duplicate JSON field"):
            parse_prover_stage(duplicate, MANIFEST, b"proof", b"abc")

    def test_external_verification_required_before_report(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            inspector, prover, verifier = (root / name for name in
                                           ("inspector", "prover", "verifier"))
            assignment, typed = root / "assignment.json", root / "typed.json"
            assignment.write_text("{}")
            typed.write_bytes(b"abc")
            executable(inspector, f"print({json.dumps(json.dumps(MANIFEST))})\n")
            executable(prover, "import pathlib,sys\n"
                       "pathlib.Path(sys.argv[2]).write_bytes(b'proof')\n"
                       "pathlib.Path(sys.argv[3]).write_bytes(pathlib.Path(sys.argv[4]).read_bytes())\n"
                       f"sys.stderr.buffer.write({stage_line()!r})\n")
            executable(verifier, "import pathlib,sys\n"
                       "assert pathlib.Path(sys.argv[1]).read_bytes()==b'proof'\n"
                       "assert pathlib.Path(sys.argv[2]).read_bytes()==b'abc'\n")
            result = measure(prover, verifier, inspector, assignment, typed,
                             root / "accepted")
            self.assertTrue(result["external_native_verification_accepted"])
            self.assertIsNone(result["engine_setup_preprocessing_ns"])
            self.assertEqual(result["prover_internal_stages_ns"], STAGES)
            self.assertEqual(result["first_verified_process_wall_ns"],
                             result["prover_process_wall_ns"] +
                             result["external_verifier_process_wall_ns"])
            self.assertTrue((root / "accepted/report.json").is_file())
            executable(verifier, "raise SystemExit(1)\n")
            with self.assertRaisesRegex(RuntimeError, "command failed"):
                measure(prover, verifier, inspector, assignment, typed,
                        root / "rejected")
            self.assertFalse((root / "rejected/report.json").exists())
            executable(verifier, "import pathlib,sys\n"
                       "pathlib.Path(sys.argv[1]).write_bytes(b'changed')\n")
            with self.assertRaisesRegex(ValueError, "changed during verification"):
                measure(prover, verifier, inspector, assignment, typed,
                        root / "mutated")
            self.assertFalse((root / "mutated/report.json").exists())


if __name__ == "__main__":
    unittest.main()
