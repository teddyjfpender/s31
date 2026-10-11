"""V7 evidence paths remain verifiable after moving the artifact directory."""

import contextlib
import io
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
import publish_whole_prover_cost_v7
import replay_portable_v7
import v7_protocol
from v7_statement import check_trial_statement
from abi.binding_v2 import flat_assignment_from_typed, statement_from_assignment
from package.context import lower_text
from benchmark_arithmetic_rss_v2 import assignment, program
import s31


class PortableV7Tests(unittest.TestCase):
    def test_require_pass_exits_nonzero_after_writing_failed_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            audit = Path(directory) / "audit.json"
            publisher_args = ["publish", "train.json", "model.json", "validation.json",
                              "evaluation.json", "--expected-protocol-sha256", "a" * 64,
                              "--protocol-anchor-commit", "b" * 40,
                              "--expected-model-sha256", "c" * 64,
                              "--model-anchor-commit", "d" * 40,
                              "--out", str(audit), "--native", "--require-pass"]
            with (patch.object(sys, "argv", publisher_args),
                  patch.object(publish_whole_prover_cost_v7, "publish",
                               return_value={"local_accuracy_gate_pass": False}),
                  contextlib.redirect_stdout(io.StringIO()),
                  self.assertRaisesRegex(SystemExit, "accuracy gate failed")):
                publish_whole_prover_cost_v7.main()
            self.assertIs(json.loads(audit.read_text())["local_accuracy_gate_pass"], False)

            replay_args = ["replay", "--root", directory,
                           "--expected-manifest-sha256", "e" * 64,
                           "--expected-protocol-sha256", "a" * 64,
                           "--protocol-anchor-commit", "b" * 40,
                           "--expected-model-sha256", "c" * 64,
                           "--model-anchor-commit", "d" * 40,
                           "--native", "--require-pass"]
            with (patch.object(sys, "argv", replay_args),
                  patch.object(replay_portable_v7, "replay",
                               return_value={"local_accuracy_gate_pass": False}),
                  contextlib.redirect_stdout(io.StringIO()),
                  self.assertRaisesRegex(SystemExit, "accuracy gate failed")):
                replay_portable_v7.main()

    def test_require_pass_cannot_skip_native_proof_controls(self):
        for main, args in (
                (publish_whole_prover_cost_v7.main,
                 ["publisher", "train", "model", "validation", "evaluation",
                  "--expected-protocol-sha256", "a" * 64,
                  "--protocol-anchor-commit", "b" * 40,
                  "--expected-model-sha256", "c" * 64,
                  "--model-anchor-commit", "d" * 40,
                  "--out", "audit", "--require-pass"]),
                (replay_portable_v7.main,
                 ["replay", "--root", "evidence",
                  "--expected-manifest-sha256", "e" * 64,
                  "--expected-protocol-sha256", "a" * 64,
                  "--protocol-anchor-commit", "b" * 40,
                  "--expected-model-sha256", "c" * 64,
                  "--model-anchor-commit", "d" * 40, "--require-pass"])):
            with self.subTest(main=main.__module__), \
                    patch.object(sys, "argv", args), \
                    contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit) as caught:
                main()
            self.assertEqual(caught.exception.code, 2)

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
            source = {"version": 1, "name": "statement_control", "inputs": [],
                      "nodes": [{"name": "result", "op": "constant", "constant": 8,
                                 "length": 1}], "public_outputs": ["result"]}
            claim = {"public_inputs": {}, "public_outputs": {"result": [8]}}
            (trial / "statement.json").write_text(json.dumps(claim))
            changed = {"public_inputs": {}, "public_outputs": {"result": [9]}}
            (trial / "changed-statement.json").write_text(json.dumps(changed))
            check_trial_statement(source, claim, trial, "public_outputs.result[0]")
            changed["public_outputs"]["result"][0] = 8
            (trial / "changed-statement.json").write_text(json.dumps(changed))
            with self.assertRaisesRegex(ValueError, "wrong fields"):
                check_trial_statement(source, claim, trial, "public_outputs.result[0]")

    def test_changed_control_requires_canonical_flat_abi_words_and_shape(self):
        source = {"version": 1, "name": "statement_ranges",
                  "inputs": [{"name": "tag", "kind": "u16", "length": 2,
                              "visibility": "public"}],
                  "nodes": [{"name": "result", "op": "constant", "constant": 8,
                             "length": 2}], "public_outputs": ["result"]}
        claim = {"public_inputs": {"tag": [65535, 9]},
                 "public_outputs": {"result": [(1 << 31) - 2, 10]}}
        with tempfile.TemporaryDirectory() as directory:
            trial = Path(directory)
            s31.write_json(trial / "statement.json", claim)
            for changed_field, category, field, accepted, rejected in (
                    ("public_inputs.tag[0]", "public_inputs", "tag", 0,
                     (65536, -1, True, "7")),
                    ("public_outputs.result[0]", "public_outputs", "result",
                     0, ((1 << 31) - 1, -1, False))):
                valid = json.loads(json.dumps(claim))
                valid[category][field][0] = accepted
                s31.write_json(trial / "changed-statement.json", valid)
                check_trial_statement(source, claim, trial, changed_field)
                for value in rejected:
                    malformed = json.loads(json.dumps(claim))
                    malformed[category][field][0] = value
                    s31.write_json(trial / "changed-statement.json", malformed)
                    with self.subTest(changed_field=changed_field, value=value), \
                            self.assertRaisesRegex(ValueError, "noncanonical ABI words"):
                        check_trial_statement(source, claim, trial, changed_field)
            wrong_shape = json.loads(json.dumps(claim))
            wrong_shape["public_inputs"]["tag"] = [8]
            s31.write_json(trial / "changed-statement.json", wrong_shape)
            with self.assertRaisesRegex(ValueError, "noncanonical ABI words or shape"):
                check_trial_statement(source, claim, trial, "public_inputs.tag[0]")
            arbitrary = json.loads(json.dumps(claim))
            arbitrary["public_outputs"]["result"][0] = 2
            s31.write_json(trial / "changed-statement.json", arbitrary)
            with self.assertRaisesRegex(ValueError, "frozen trial mutation"):
                check_trial_statement(source, claim, trial, "public_outputs.result[0]")

    def test_changed_control_accepts_canonical_record_abi_and_rejects_bad_leaf(self):
        source, _, _ = lower_text(S31 / "examples/arithmetic/record_input_sum.s31")
        typed = json.loads((S31 / "examples/arithmetic/record_input_sum.valid.json").read_bytes())
        flat = flat_assignment_from_typed(source, json.dumps(typed).encode())
        original = statement_from_assignment(source, flat)
        changed = json.loads(original)
        changed["leaves"][0]["words"][0] += 1
        with tempfile.TemporaryDirectory() as directory:
            trial = Path(directory)
            (trial / "statement.json").write_bytes(original)
            # Record statements have canonical compact JSON and a final newline.
            (trial / "changed-statement.json").write_bytes(
                (json.dumps(changed, sort_keys=True, separators=(",", ":")) + "\n").encode())
            check_trial_statement(source, typed, trial, "leaves[0].words[0]")
            changed["leaves"][0]["words"][0] = (1 << 31) - 1
            (trial / "changed-statement.json").write_bytes(
                (json.dumps(changed, sort_keys=True, separators=(",", ":")) + "\n").encode())
            with self.assertRaisesRegex(ValueError, "noncanonical public M31 word"):
                check_trial_statement(source, typed, trial, "leaves[0].words[0]")

    def test_ordinary_publisher_rejects_malformed_changed_statement(self):
        source = {"version": 1, "name": "saved_trial", "inputs": [],
                  "nodes": [{"name": "result", "op": "constant", "constant": 8,
                             "length": 1}], "public_outputs": ["result"]}
        assignment = {"public_inputs": {}, "private_inputs": {},
                      "public_outputs": {"result": [8]}}
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            name = "arithmetic_1"
            package = base / name / "package"
            package.mkdir(parents=True)
            s31.write_json(package / "source.s31.json", source)
            assignments = base / name / "assignments"
            assignments.mkdir()
            s31.write_json(assignments / "00.json", assignment)
            trial = base / name / "trials" / "00"
            trial.mkdir(parents=True)
            s31.write_json(trial / "statement.json", {
                "public_inputs": {}, "public_outputs": {"result": [8]}})
            s31.write_json(trial / "changed-statement.json", {
                "public_inputs": {}, "public_outputs": {"result": [-1]}})
            s31.write_json(trial / "trial-report.json", {})
            case = {"trials": [{"changed_public_statement_rejected":
                                 "public_outputs.result[0]",
                                 "independent_value_oracle": {
                                     "computed_public_outputs": {"result": [8]}}}]}
            with patch.object(publish_whole_prover_cost_v7, "evaluate_relation",
                              return_value={"result": [8]}), \
                    self.assertRaisesRegex(ValueError, "noncanonical ABI words"):
                publish_whole_prover_cost_v7.replay_trials(
                    base, name, case, {"name": "saved_trial"}, False)

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
            cost = {"raw": {"vm": 1}, "padded": {"vm": 2},
                    "preprocessed_cells": 1, "profile": "direct-m31-v4",
                    "fri": {"pow_bits": 26, "log_blowup_factor": 1,
                            "last_layer_degree_bound": 1, "queries": 70,
                            "fold_step": 1}}
            s31.write_json(package / "cost-report.json", cost)
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
                    "trials": [compact], "profile": "direct-m31-v4",
                    "raw": cost["raw"], "padded": cost["padded"],
                    "preprocessed_cells": cost["preprocessed_cells"],
                    "visible_fri": s31.visible_fri(cost, "direct-gate")}
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
            poisoned = {**case, "raw": {"vm": 999},
                        "padded": {"vm": 1024}, "preprocessed_cells": 999}
            with (patch.object(replay_portable_v7, "check_build_inventory",
                               return_value=built),
                  patch.object(replay_portable_v7.s31, "verify_package",
                               return_value=manifest),
                  self.assertRaisesRegex(ValueError, "corpus geometry differs")):
                replay_portable_v7.audit_split(
                    root, "train", {**corpus, "cases": {name: poisoned}},
                    protocol, "a" * 64, "e" * 40, None, None, False)


if __name__ == "__main__":
    unittest.main()
