"""V7 evidence paths remain verifiable after moving the artifact directory."""

import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "benchmarks"))
sys.path.insert(0, str(S31 / "benchmarks" / "cost"))
sys.path.insert(0, str(S31 / "python"))

import portable_v7
import replay_portable_v7
import v7_protocol
from benchmark_arithmetic_rss_v2 import assignment, program
import s31


class PortableV7Tests(unittest.TestCase):
    def fixture(self, root: Path):
        protocol_sha, model_sha = "a" * 64, "b" * 64
        (root / "train").mkdir(parents=True)
        (root / "validation").mkdir(parents=True)
        (root / "train/whole-prover-corpus.json").write_text(json.dumps({
            "protocol_sha256": protocol_sha,
        }))
        (root / "validation/whole-prover-corpus.json").write_text(json.dumps({
            "protocol_sha256": protocol_sha, "frozen_model_sha256": model_sha,
        }))
        (root / "validation/evaluation.json").write_text(json.dumps({
            "frozen_model_sha256": model_sha,
        }))
        (root / "train/proof.bin").write_bytes(b"immutable proof bytes")
        return protocol_sha, model_sha

    def test_content_addressed_manifest_survives_directory_move(self):
        with tempfile.TemporaryDirectory() as directory:
            original = Path(directory) / "original"
            protocol_sha, model_sha = self.fixture(original)
            manifest = portable_v7.create(original, protocol_sha, model_sha)
            digest = s31.file_hash(original / portable_v7.MANIFEST_NAME)
            moved = Path(directory) / "other-location" / "evidence"
            moved.parent.mkdir()
            shutil.move(original, moved)
            self.assertEqual(portable_v7.verify(moved, digest), manifest)
            (moved / "train/proof.bin").write_bytes(b"tampered proof bytes")
            with self.assertRaisesRegex(ValueError, "content-addressed manifest"):
                portable_v7.verify(moved, digest)

    def test_manifest_rejects_symlinks_and_unsafe_paths(self):
        for value in ("../train/a", "train/../validation/a", "/train/a",
                      "train//a", "validation/./a"):
            with self.subTest(value=value), self.assertRaises(ValueError):
                portable_v7.safe_relative(value)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "evidence"
            protocol_sha, model_sha = self.fixture(root)
            (root / "train/linked-proof.bin").symlink_to(root / "train/proof.bin")
            with self.assertRaisesRegex(ValueError, "regular file"):
                portable_v7.create(root, protocol_sha, model_sha)

    def test_report_paths_are_provenance_hints_and_statements_still_bind(self):
        replay_portable_v7.suffix(
            "/old-machine/run/train/arithmetic_1/assignments/00.json",
            ("arithmetic_1", "assignments", "00.json"), "assignment")
        with self.assertRaisesRegex(ValueError, "wrong relative suffix"):
            replay_portable_v7.suffix(
                "/old-machine/run/train/other/assignments/00.json",
                ("arithmetic_1", "assignments", "00.json"), "assignment")
        with tempfile.TemporaryDirectory() as directory:
            trial = Path(directory)
            claim = {"public_inputs": {}, "public_outputs": {"result": [8]}}
            (trial / "statement.json").write_text(json.dumps(claim))
            changed = {"public_inputs": {}, "public_outputs": {"result": [9]}}
            (trial / "changed-statement.json").write_text(json.dumps(changed))
            replay_portable_v7.check_statement(claim, trial, "public_outputs.result[0]")
            changed["public_outputs"]["result"][0] = 8
            (trial / "changed-statement.json").write_text(json.dumps(changed))
            with self.assertRaisesRegex(ValueError, "wrong fields"):
                replay_portable_v7.check_statement(claim, trial, "public_outputs.result[0]")

    def test_split_audit_reads_moved_source_and_trial_without_old_root(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory) / "new-location"
            base = root / "train"
            name = "arithmetic_1"
            source = base / "generated-sources" / f"{name}.s31.json"
            source.parent.mkdir(parents=True)
            body = [{"op": "square"}, {"op": "add_const", "constant": 3}]
            s31.write_json(source, program("v7_relocated_arithmetic", 1, body))
            assigned = assignment(1, body, 90)
            assignment_path = base / name / "assignments/00.json"
            assignment_path.parent.mkdir(parents=True)
            s31.write_json(assignment_path, assigned)
            package = base / name / "package"
            package.mkdir(parents=True)
            (package / "source.s31.json").write_bytes(source.read_bytes())
            trial = base / name / "trials/00"
            trial.mkdir(parents=True)
            proof = trial / "proof.bin"
            proof.write_bytes(b"proof")
            statement = {key: assigned[key] for key in ("public_inputs", "public_outputs")}
            s31.write_json(trial / "statement.json", statement)
            changed = json.loads(json.dumps(statement))
            field = next(iter(changed["public_outputs"]))
            changed["public_outputs"][field][0] += 1
            s31.write_json(trial / "changed-statement.json", changed)
            compact = {"proof_sha256": s31.file_hash(proof), "proof_bytes": 5,
                       "native_verifier_accepted": True,
                       "changed_public_statement_rejected": f"public_outputs.{field}[0]",
                       "independent_value_oracle": {
                           "status": "passed",
                           "computed_public_outputs": assigned["public_outputs"]}}
            provenance = {str(path.relative_to(v7_protocol.ROOT)): s31.file_hash(path)
                          for path in (S31 / "python/oracle.py",
                                       S31 / "python/poseidon2_oracle.py")}
            report = {**compact, "schema": "s31-trial-v1",
                      "program": "v7_relocated_arithmetic", "lowering": "direct-gate",
                      "assignment": f"/old-machine/run/train/{name}/assignments/00.json",
                      "package": f"/old-machine/run/train/{name}/package",
                      "program_sha256": s31.file_hash(source),
                      "canonical_ir_sha256": "c" * 64,
                      "profile": "direct-m31-v4",
                      "independent_value_oracle_provenance": {
                          "source_sha256": provenance}}
            s31.write_json(trial / "trial-report.json", report)
            source_sha = s31.file_hash(source)
            assignment_sha = s31.assignment_digest(assignment_path)
            build = {"package_reused": False, "package_build_wall_seconds": 1.0}
            case = {"family": "arithmetic", "lowering": "direct-gate",
                    "source": f"/old-machine/run/train/generated-sources/{source.name}",
                    "source_sha256": source_sha,
                    "assignment_sha256": [assignment_sha],
                    "package_build": build, "chip_manifest_binding": None,
                    "trials": [compact], "profile": "direct-m31-v4"}
            corpus = {"schema": "s31-whole-prover-cost-corpus-v7", "split": "train",
                      "protocol_sha256": "a" * 64,
                      "measurement_tool_sha256": "b" * 64,
                      "host": {"machine": "original"},
                      "frozen_model_sha256": None, "cases": {name: case}}
            protocol = {"measurement_tool_sha256": "b" * 64,
                        "host": {"machine": "original"},
                        "samples_per_program": 1,
                        "compiler_sha256": "d" * 64,
                        "inventory": {"train": {name: {
                            "family": "arithmetic", "lowering": "direct-gate",
                            "source_sha256": source_sha,
                            "assignment_sha256": [assignment_sha]}}}}
            manifest = {"compiler_sha256": "d" * 64,
                        "name": "v7_relocated_arithmetic",
                        "lowering": "direct-gate",
                        "program_sha256": source_sha,
                        "canonical_ir_sha256": "c" * 64}
            built = {"programs": {name: {"package_build": build}}}
            with (patch.object(replay_portable_v7, "check_build_inventory",
                               return_value=built),
                  patch.object(replay_portable_v7.s31, "verify_package",
                               return_value=manifest)):
                controls = replay_portable_v7.audit_split(
                    root, "train", corpus, protocol, "a" * 64, "e" * 40,
                    None, None, False)
            self.assertEqual(controls["proofs"], 1)
            self.assertEqual(controls["assignments"], 1)


if __name__ == "__main__":
    unittest.main()
