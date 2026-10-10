"""Prospective v4 split, expected-wall target and honest failure gates."""

import hashlib
import json
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

S31_ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(S31_ROOT / "benchmarks"), str(S31_ROOT / "python"),
                str(Path(__file__).resolve().parent)]

from benchmark_whole_prover_cost_v4 import workload_cases
from stage_aware_predictor_v1 import actual_target
from whole_prover_predictor_v4 import PROTOCOL, evaluate, fit_model, wall_center
from publish_whole_prover_cost_v4 import publish
from test_whole_prover_predictor_v3 import materialize_v3_corpus, synthetic_corpus
from test_publish_stage_aware_cost_v1 import write_json


def corpus(split: str, protocol: dict) -> dict:
    result = synthetic_corpus(split, protocol)
    result["schema"] = "s31-whole-prover-cost-corpus-v4"
    result["protocol_sha256"] = hashlib.sha256(PROTOCOL.read_bytes()).hexdigest()
    return result


class WholeProverV4Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.protocol = json.loads(PROTOCOL.read_text())

    def test_fresh_split_has_distinct_sources_and_assignments(self) -> None:
        from oracle import evaluate_relation
        from package.context import lower_text

        with TemporaryDirectory() as directory:
            train = workload_cases("train", Path(directory) / "train", 2, self.protocol)
            held = workload_cases("validation", Path(directory) / "held", 2, self.protocol)
            self.assertEqual((len(train), len(held)), (18, 16))
            self.assertFalse({item["source"].read_bytes() for item in train} &
                             {item["source"].read_bytes() for item in held})
            def assignments(items: list[dict]) -> set[bytes]:
                return {json.dumps(value, sort_keys=True).encode()
                        for item in items for value in item["assignments"]}
            self.assertFalse(assignments(train) & assignments(held))
            for item in train + held:
                source = item["source"]
                relation = (lower_text(source)[0] if source.suffix == ".s31"
                            else json.loads(source.read_text()))
                for assignment in item["assignments"]:
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"])

    def test_expected_wall_is_sum_of_stage_means_and_pow_is_constant(self) -> None:
        train = corpus("train", self.protocol)
        model = fit_model(train, self.protocol)
        arithmetic = model["families"]["arithmetic"]
        self.assertEqual(arithmetic["wall_stages"]["runtime_fri_pow_seconds"]["feature"],
                         "constant")
        self.assertEqual(arithmetic["wall_stages"]["runtime_interaction_pow_seconds"]["feature"],
                         "constant")
        case = train["cases"]["arithmetic_40"]
        from whole_prover_predictor_v3 import case_features

        self.assertGreater(wall_center(arithmetic["wall_stages"], case_features(case)), 0)
        self.assertEqual(arithmetic["wall_interval"]["training_trial_ratios"], 500)
        self.assertGreater(arithmetic["wall_interval"]["ratio_p95"],
                           arithmetic["wall_interval"]["ratio_p05"])
        self.assertFalse(model["automatic_lowering_selection_enabled"])

    def test_heldout_gates_reject_bad_transfer_and_source_leakage(self) -> None:
        train = corpus("train", self.protocol)
        model = fit_model(train, self.protocol)
        held = corpus("validation", self.protocol)
        result = evaluate(model, held, self.protocol)
        self.assertFalse(result["local_accuracy_gate_pass"])
        self.assertFalse(result["automatic_lowering_selection_enabled"])
        first = held["cases"]["arithmetic_80"]["trials"]
        measured_mean = sum(actual_target(trial, "paired_prove_and_verify_wall_seconds")
                            for trial in first) / len(first)
        report = next(row for row in result["programs"] if row["program"] == "arithmetic_80")
        self.assertAlmostEqual(report["targets"]["paired_prove_and_verify_wall_seconds"]
                               ["measured_point"], measured_mean)
        held["cases"]["arithmetic_80"]["source_sha256"] = model["training_source_sha256"][0]
        with self.assertRaisesRegex(ValueError, "source leaked"):
            evaluate(model, held, self.protocol)

    def test_pow_policy_and_host_are_bound(self) -> None:
        train = corpus("train", self.protocol)
        for case in train["cases"].values():
            case["visible_fri"]["pow_bits"] = 25
        with self.assertRaisesRegex(ValueError, "PoW bit policy"):
            fit_model(train, self.protocol)
        train = corpus("train", self.protocol)
        model = fit_model(train, self.protocol)
        held = corpus("validation", self.protocol)
        held["host"] = {"machine": "another-host"}
        with self.assertRaisesRegex(ValueError, "host"):
            evaluate(model, held, self.protocol)

    def test_publisher_requires_prevalidation_hash_and_keeps_failed_gate(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            train = corpus("train", self.protocol)
            train_path = materialize_v3_corpus(root / "train", train)
            model = fit_model(train, self.protocol)
            model["training_corpus_sha256"] = hashlib.sha256(train_path.read_bytes()).hexdigest()
            model_path = root / "model.json"
            write_json(model_path, model)
            model_sha = hashlib.sha256(model_path.read_bytes()).hexdigest()
            held = corpus("validation", self.protocol)
            held["frozen_model_sha256"] = model_sha
            held_path = materialize_v3_corpus(root / "validation", held)
            evaluation = evaluate(model, held, self.protocol)
            evaluation["frozen_model_sha256"] = model_sha
            evaluation["validation_corpus_sha256"] = hashlib.sha256(
                held_path.read_bytes()).hexdigest()
            evaluation_path = root / "evaluation.json"
            write_json(evaluation_path, evaluation)

            def case_for(package: Path) -> dict:
                return {"train": train, "validation": held}[
                    package.parent.parent.name]["cases"][package.parent.name]

            def manifest(package: Path) -> dict:
                case = case_for(package)
                return {"compiler_sha256": "c" * 64,
                        "program_sha256": case["source_sha256"],
                        "lowering": case["lowering"]}

            with patch("publish_whole_prover_cost_v4.s31.verify_package",
                       side_effect=manifest), patch(
                           "publish_whole_prover_cost_v4.chip_manifest_binding",
                           side_effect=lambda package: case_for(package)["chip_manifest_binding"]):
                report = publish(train_path, model_path, held_path, evaluation_path, model_sha)
                self.assertFalse(report["local_accuracy_gate_pass"])
                self.assertFalse(report["automatic_lowering_selection_enabled"])
                self.assertEqual(report["artifact_controls"]["validation"]
                                 ["saved_assignment_digest_matched"], 1600)
                assignment_path = root / "validation/arithmetic_80/assignments/00.json"
                original = assignment_path.read_bytes()
                tampered = json.loads(original)
                tampered["public_outputs"]["result"][0] += 1
                write_json(assignment_path, tampered)
                with self.assertRaisesRegex(ValueError, "saved assignment digest"):
                    publish(train_path, model_path, held_path, evaluation_path,
                            model_sha)
                assignment_path.write_bytes(original)
                with self.assertRaisesRegex(ValueError, "externally recorded"):
                    publish(train_path, model_path, held_path, evaluation_path, "0" * 64)


if __name__ == "__main__":
    unittest.main()
