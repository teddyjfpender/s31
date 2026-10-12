"""V8 pipeline guards and second-source RSS checks without native builds."""

import contextlib
import copy
import hashlib
import io
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(S31 / "benchmarks"), str(S31 / "benchmarks" / "cost"),
                str(S31 / "python")]

import benchmark_whole_prover_cost_v8 as collector
import independent_v8_gate as independent
import portable_v8
import publish_whole_prover_cost_v8 as publisher
import replay_portable_v8 as portable_replay
import v8_protocol
import whole_prover_predictor_v8 as predictor
import s31


class CostV8PipelineTests(unittest.TestCase):
    def test_protocol_template_carries_design_and_discloses_excluded_mixed_profile(self):
        with (patch.object(v8_protocol.s31, "compiler_fingerprint", return_value="f" * 64),
              patch.object(v8_protocol, "host_identity", return_value={"host": "static-test"}),
              patch.object(v8_protocol, "tool_paths", return_value=[])):
            protocol = v8_protocol.protocol_template()
        self.assertEqual(protocol["revision"], "8")
        self.assertEqual(protocol["splits"], v8_protocol.DESIGN["splits"])
        self.assertEqual(protocol["rss_uncertainty"], v8_protocol.DESIGN["rss_uncertainty"])
        self.assertEqual(protocol["prospective_design_sha256"],
                         s31.file_hash(v8_protocol.v8_design.DESIGN))
        self.assertEqual(protocol["v7r1_audit_sha256"],
                         v8_protocol.DESIGN["historical_v7r1_audit_sha256"])
        self.assertEqual(protocol["paired_mixed_vs_generic"]["status"],
                         "excluded-until-general-profile-admitted-and-packaged")

    def test_collector_refuses_native_work_without_frozen_protocol(self):
        with tempfile.TemporaryDirectory(prefix="s31-v8-no-freeze-") as directory:
            args = type("Args", (), {"out": Path(directory), "split": "train",
                                    "phase": "build", "expected_protocol_sha256": "0" * 64,
                                    "protocol_anchor_commit": "1" * 40,
                                    "expected_model_sha256": None, "model_anchor_commit": None,
                                    "model": None})()
            with (patch.object(v8_protocol, "PROTOCOL", Path(directory) / "missing.json"),
                  patch.object(collector, "require_protocol", v8_protocol.require_protocol),
                  patch.object(collector.s31, "build", side_effect=AssertionError("native called")),
                  self.assertRaisesRegex(ValueError, "full externally recorded protocol SHA")):
                collector.run(args)

    def test_protocol_rejects_changed_pow_policy_before_anchor_check(self):
        with tempfile.TemporaryDirectory(prefix="s31-v8-protocol-") as directory:
            path = Path(directory) / "protocol.json"
            with (patch.object(v8_protocol.s31, "compiler_fingerprint", return_value="f" * 64),
                  patch.object(v8_protocol, "host_identity", return_value={"host": "static-test"}),
                  patch.object(v8_protocol, "tool_paths", return_value=[])):
                protocol = v8_protocol.protocol_template()
            protocol["pow_bits_required"] = 0
            s31.write_json(path, protocol)
            with (patch.object(v8_protocol, "PROTOCOL", path),
                  patch.object(v8_protocol, "require_committed"),
                  self.assertRaisesRegex(ValueError, "changed pow_bits_required")):
                v8_protocol.require_protocol(s31.file_hash(path), "a" * 40)

    def test_rss_fit_uses_fixed_floor_and_matches_independent_prediction(self):
        records = []
        for i, rows in enumerate((16, 32, 64, 128, 256, 512)):
            records.append({"name": f"train_{i}", "features": {"padded_rows": rows},
                            "case": {"trials": [{"prover_peak_rss_bytes":
                                                  16_000_000 + 128 * rows + (j % 5) * 4096}
                                                 for j in range(100)]}})
        fit = predictor.fit_rss_interval(records, "padded_rows", "arithmetic", 2 * 1024**2)
        self.assertEqual(fit["training_programs"], 6)
        self.assertEqual(fit["training_trials"], 600)
        self.assertEqual(len(fit["calibration"]), 6)
        self.assertGreaterEqual(fit["relative_radius"], 0)
        target = predictor.predict_rss_interval(fit, {"padded_rows": 96})
        self.assertGreaterEqual(target["upper"] - target["center"], 2 * 1024**2)
        policy = {"wall_stages": {"one": {"feature": "constant", "fit": {"constant": 1.0}}},
                  "wall_interval": {"ratio_p05": 0.8, "ratio_p95": 1.2},
                  "proof_bytes": {"feature": "constant", "fit": {"constant": 128.0},
                                  "training_loo_max_abs_log_error": 0.01,
                                  "training_trial_ratio_p05": 1.0,
                                  "training_trial_ratio_p95": 1.0},
                  "prover_peak_rss_bytes": fit}
        second = independent.prediction(policy, {"constant": 1.0, "padded_rows": 96})
        self.assertEqual(second["prover_peak_rss_bytes"], target)
        with self.assertRaisesRegex(ValueError, "predeclared 2 MiB"):
            predictor.fit_rss_interval(records, "padded_rows", "arithmetic", 0)

    def test_release_gate_requires_native_and_preserves_failed_audit(self):
        with tempfile.TemporaryDirectory(prefix="s31-v8-gate-") as directory:
            audit = Path(directory) / "audit.json"
            publish_args = ["publish", "train", "model", "validation", "evaluation",
                            "--expected-protocol-sha256", "a" * 64,
                            "--protocol-anchor-commit", "b" * 40,
                            "--expected-model-sha256", "c" * 64,
                            "--model-anchor-commit", "d" * 40,
                            "--out", str(audit), "--native", "--require-pass"]
            with (patch.object(sys, "argv", publish_args),
                  patch.object(publisher, "publish", return_value={"local_accuracy_gate_pass": False}),
                  contextlib.redirect_stdout(io.StringIO()),
                  self.assertRaisesRegex(SystemExit, "accuracy gate failed")):
                publisher.main()
            self.assertIs(json.loads(audit.read_text())["local_accuracy_gate_pass"], False)
            replay_args = ["replay", "--root", directory,
                           "--expected-manifest-sha256", "e" * 64,
                           "--expected-protocol-sha256", "a" * 64,
                           "--protocol-anchor-commit", "b" * 40,
                           "--expected-model-sha256", "c" * 64,
                           "--model-anchor-commit", "d" * 40,
                           "--native", "--require-pass"]
            with (patch.object(sys, "argv", replay_args),
                  patch.object(portable_replay, "replay", return_value={"local_accuracy_gate_pass": False}),
                  contextlib.redirect_stdout(io.StringIO()),
                  self.assertRaisesRegex(SystemExit, "accuracy gate failed")):
                portable_replay.main()
            for main, args in ((publisher.main, publish_args),
                               (portable_replay.main, replay_args)):
                with (patch.object(sys, "argv", [arg for arg in args if arg != "--native"]),
                      contextlib.redirect_stderr(io.StringIO()),
                      self.assertRaises(SystemExit) as exit_result):
                    main()
                self.assertEqual(exit_result.exception.code, 2)

    def test_portable_manifest_relocates_and_rejects_changed_proof(self):
        for unsafe in ("../train/proof.bin", "train/../validation/a", "/train/a",
                       "train//a", "validation/./a"):
            with self.subTest(unsafe=unsafe), self.assertRaises(ValueError):
                portable_v8.safe_relative(unsafe)
        with tempfile.TemporaryDirectory(prefix="s31-v8-portable-") as directory:
            original = Path(directory) / "original"
            (original / "train").mkdir(parents=True)
            (original / "validation").mkdir()
            protocol_sha, model_sha = "a" * 64, "b" * 64
            s31.write_json(original / "train/whole-prover-corpus.json",
                           {"protocol_sha256": protocol_sha})
            s31.write_json(original / "validation/whole-prover-corpus.json",
                           {"protocol_sha256": protocol_sha, "frozen_model_sha256": model_sha})
            s31.write_json(original / "validation/evaluation.json",
                           {"frozen_model_sha256": model_sha})
            (original / "train/proof.bin").write_bytes(b"saved proof")
            manifest = portable_v8.create(original, protocol_sha, model_sha)
            digest = s31.file_hash(original / portable_v8.MANIFEST_NAME)
            moved = Path(directory) / "moved"
            shutil.move(original, moved)
            self.assertEqual(portable_v8.verify(moved, digest), manifest)
            (moved / "train/proof.bin").write_bytes(b"changed proof")
            with self.assertRaisesRegex(ValueError, "content-addressed manifest"):
                portable_v8.verify(moved, digest)

    def test_fitted_model_rejects_program_specific_verifier_startup_miss(self):
        def digest(value):
            return hashlib.sha256(value.encode()).hexdigest()

        def specimen(split, names, protocol):
            cases = {}
            for size in names:
                name = f"arithmetic_{size}"
                source_sha = digest(f"{split}/{name}/source")
                assignments = [digest(f"{split}/{name}/{i}") for i in range(100)]
                protocol["inventory"][split][name] = {
                    "family": "arithmetic", "lowering": "direct-gate",
                    "source_sha256": source_sha, "assignment_sha256": assignments,
                }
                trials = []
                for _ in range(100):
                    trials.append({
                        "native_verifier_accepted": True,
                        "changed_public_statement_rejected": "public_outputs.result[0]",
                        "independent_value_oracle": {"status": "passed"},
                        "prove_seconds": .055,
                        "verify_seconds": .030,
                        "prover_stages": {
                            "witness_seconds": .005, "setup_seconds": .005,
                            "prove_seconds": .030, "prove_excluding_pow_seconds": .020,
                            "interaction_pow_seconds": .005, "fri_pow_seconds": .005,
                            "runtime_other_seconds": .005,
                            "total_through_verification_seconds": .045,
                        },
                        "proof_bytes": 1000 + size * 10,
                        "prover_peak_rss_bytes": 10_000_000 + size * 1_000,
                    })
                cases[name] = {
                    "family": "arithmetic", "source_sha256": source_sha,
                    "assignment_sha256": assignments,
                    "lowering": "direct-gate", "profile": "direct-m31-v4",
                    "visible_fri": v8_protocol.VISIBLE_FRI,
                    "package_build": {"package_build_wall_seconds": 1.0,
                                      "package_reused": False},
                    "chip_manifest_binding": None,
                    "raw": {"qm31_ops": size}, "padded": {"qm31_ops": size},
                    "preprocessed_cells": 8 * size, "trials": trials,
                    "compiler_sha256": "a" * 64,
                }
            return cases

        with tempfile.TemporaryDirectory() as directory:
            protocol = {
                "schema": v8_protocol.SCHEMA, "profiles": {"arithmetic": "direct-gate"},
                "profile_by_family": {"arithmetic": "direct-m31-v4"},
                "visible_fri": v8_protocol.VISIBLE_FRI, "pow_bits_required": 26,
                "samples_per_program": 100, "accuracy_gate": v8_protocol.GATES,
                "stage_features": {
                    "runtime_witness_seconds": "raw_rows",
                    "runtime_setup_seconds": "preprocessed_cells",
                    "runtime_prove_excluding_pow_seconds": "raw_rows",
                    "runtime_interaction_pow_seconds": "constant",
                    "runtime_fri_pow_seconds": "constant",
                    "runtime_runtime_other_seconds": "padded_rows",
                    "prover_process_unattributed_seconds": "constant",
                    "native_verify_process_wall_seconds": "padded_rows",
                    "proof_bytes": "padded_rows",
                    "prover_peak_rss_bytes": "padded_rows",
                },
                "splits": {split: {"arithmetic_rounds": sizes, "chip_rounds": [],
                                   "hash_depths": [], "signed_widths": []}
                           for split, sizes in (("train", [16, 32, 64, 128, 256]),
                                                ("validation", [24, 48, 96, 192, 384]))},
                "inventory": {"train": {}, "validation": {}},
                "selection_policy": "disabled",
                "rss_uncertainty": v8_protocol.RSS_UNCERTAINTY,
            }
            train_cases = specimen("train", protocol["splits"]["train"]["arithmetic_rounds"],
                                   protocol)
            validation_cases = specimen(
                "validation", protocol["splits"]["validation"]["arithmetic_rounds"], protocol)
            protocol_path = Path(directory) / "protocol.json"
            protocol_path.write_text(json.dumps(protocol, sort_keys=True))
            protocol_sha = v8_protocol.sha(protocol_path.read_bytes())
            common = {"measurement_tool_sha256": "b" * 64,
                      "protocol_sha256": protocol_sha, "host": {"test": "same-host"},
                      "samples_per_program": 100}
            train = {**common, "schema": predictor.CORPUS_SCHEMA, "split": "train",
                     "cases": train_cases}
            validation = {**common, "schema": predictor.CORPUS_SCHEMA,
                          "split": "validation", "cases": validation_cases}
            with patch.object(predictor, "PROTOCOL", protocol_path):
                model = predictor.fit_model(train, protocol)
                clean = predictor.evaluate(model, validation, protocol)
                self.assertEqual(independent.check_saved_evaluation(model, validation, protocol, clean)
                                 ["programs_checked"], 5)
                changed_floor = copy.deepcopy(model)
                changed_floor["families"]["arithmetic"]["prover_peak_rss_bytes"][
                    "fixed_absolute_floor_bytes"] = 0
                with self.assertRaisesRegex(ValueError, "RSS floor differs"):
                    independent.check_saved_evaluation(changed_floor, validation, protocol, clean)
                self.assertTrue(all(row["process_stage_gate_pass"]
                                    for row in clean["programs"]))
                validation_cases["arithmetic_96"]["trials"] = [
                    {**trial, "verify_seconds": .063}
                    for trial in validation_cases["arithmetic_96"]["trials"]]
                missed = predictor.evaluate(model, validation, protocol)
                self.assertFalse(independent.check_saved_evaluation(model, validation, protocol, missed)
                                 ["local_accuracy_gate_pass"])
                self.assertFalse(missed["local_accuracy_gate_pass"])
                self.assertFalse(next(row for row in missed["programs"]
                                      if row["program"] == "arithmetic_96")
                                 ["process_stage_gate_pass"])
                missed["accuracy"]["arithmetic"]["paired_prove_and_verify_wall_seconds"][
                    "trial_interval_coverage"] = 1.0
                with self.assertRaisesRegex(ValueError, "independent held-out value differs"):
                    independent.check_saved_evaluation(model, validation, protocol, missed)


if __name__ == "__main__":
    unittest.main()
