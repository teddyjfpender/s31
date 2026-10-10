"""Independent RSS protocol split, positive affine fit, and proof audit."""

import hashlib
import json
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

S31_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31_ROOT / "benchmarks"))
sys.path.insert(0, str(Path(__file__).resolve().parent))

from arithmetic_rss_predictor_v2 import PROTOCOL, evaluate, fit_model
from benchmark_arithmetic_rss_v2 import workloads
from publish_arithmetic_rss_v2 import publish
from test_publish_stage_aware_cost_v1 import materialize_corpus, write_json


def digest(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def synthetic_corpus(split: str, protocol: dict) -> dict:
    spec = protocol[split]
    entries = ([(r, "train") for r in spec["rounds"]] if split == "train" else
               [(r, body) for body in spec["bodies"] for r in spec["rounds"]])
    cases = {}
    for rounds, body in entries:
        name = f"arith_rss_{body}_{rounds}"
        raw = 321 + (3 if body == "triple" else 2) * rounds
        padded = 1 << (raw - 1).bit_length()
        trials = []
        for index in range(protocol["samples_per_program"]):
            trials.append({
                "native_verifier_accepted": True,
                "changed_public_statement_rejected": "public_outputs.result[0]",
                "independent_value_oracle": {"status": "passed"},
                "prover_peak_rss_bytes": 8_000_000 + 1300 * padded + (index % 5 - 2) * 4096,
            })
        cases[name] = {
            "source_sha256": digest(f"source:{split}:{name}"),
            "compiler_sha256": "c" * 64,
            "lowering": "direct-gate", "profile": "synthetic-direct",
            "visible_fri": {"pow_bits": 26},
            "raw": {"qm31_ops": raw}, "padded": {"qm31_ops": padded},
            "preprocessed_cells": 8 * padded,
            "package_build": {"package_build_wall_seconds": 1.0,
                              "package_reused": False},
            "assignment_sha256": [digest(f"{split}:{name}:{index}")
                                  for index in range(protocol["samples_per_program"])],
            "trials": trials,
        }
    return {
        "schema": "s31-arithmetic-rss-corpus-v2", "split": split,
        "protocol_sha256": hashlib.sha256(PROTOCOL.read_bytes()).hexdigest(),
        "samples_per_program": protocol["samples_per_program"],
        "compiler_sha256": "c" * 64,
        "host": {"machine": "synthetic"}, "cases": cases,
    }


class ArithmeticRssV2Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.protocol = json.loads(PROTOCOL.read_text())

    def test_new_source_split_and_independent_oracle(self) -> None:
        sys.path.insert(0, str(S31_ROOT / "python"))
        from oracle import evaluate_relation
        with TemporaryDirectory() as directory:
            train = workloads("train", Path(directory) / "train", self.protocol)
            validation = workloads("validation", Path(directory) / "validation", self.protocol)
            self.assertEqual((len(train), len(validation)), (5, 8))
            self.assertFalse({item["name"] for item in train} &
                             {item["name"] for item in validation})
            for item in train + validation:
                relation = json.loads(item["source"].read_text())
                self.assertEqual(evaluate_relation(relation, item["assignments"][0]),
                                 item["assignments"][0]["public_outputs"])

    def test_affine_fit_and_new_program_gate(self) -> None:
        train = synthetic_corpus("train", self.protocol)
        validation = synthetic_corpus("validation", self.protocol)
        model = fit_model(train, self.protocol)
        self.assertEqual(len(model["training_source_sha256"]), 5)
        self.assertGreater(model["candidate_positive_affine"]["intercept_bytes"], 0)
        self.assertGreater(model["candidate_positive_affine"]["bytes_per_padded_row"], 0)
        result = evaluate(model, validation, self.protocol)
        self.assertTrue(result["targeted_rss_accuracy_gate_pass"])
        self.assertFalse(result["automatic_lowering_selection_enabled"])
        self.assertEqual(len(result["programs"]), 8)
        validation["cases"]["arith_rss_pair_48"]["assignment_sha256"][0] = model["training_assignment_sha256"][0]
        with self.assertRaisesRegex(ValueError, "assignment leaked"):
            evaluate(model, validation, self.protocol)

    def test_bad_rss_data_cannot_pass_or_fit(self) -> None:
        train = synthetic_corpus("train", self.protocol)
        model = fit_model(train, self.protocol)
        validation = synthetic_corpus("validation", self.protocol)
        for trial in validation["cases"]["arith_rss_pair_768"]["trials"]:
            trial["prover_peak_rss_bytes"] *= 2
        result = evaluate(model, validation, self.protocol)
        self.assertFalse(result["targeted_rss_accuracy_gate_pass"])
        self.assertFalse(result["automatic_lowering_selection_enabled"])
        for case in train["cases"].values():
            rows = sum(case["padded"].values())
            for trial in case["trials"]:
                trial["prover_peak_rss_bytes"] = 50_000_000 - 1300 * rows
        with self.assertRaisesRegex(ValueError, "positive affine RSS hypothesis"):
            fit_model(train, self.protocol)

    def test_publisher_replays_model_and_audits_proofs(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            train = synthetic_corpus("train", self.protocol)
            train_path = materialize_corpus(root / "train", train)
            model = fit_model(train, self.protocol)
            model["training_corpus_sha256"] = hashlib.sha256(train_path.read_bytes()).hexdigest()
            model_path = root / "model.json"
            write_json(model_path, model)
            validation = synthetic_corpus("validation", self.protocol)
            validation["frozen_model_sha256"] = hashlib.sha256(model_path.read_bytes()).hexdigest()
            validation_path = materialize_corpus(root / "validation", validation)
            evaluation = evaluate(model, validation, self.protocol)
            evaluation["frozen_model_sha256"] = hashlib.sha256(model_path.read_bytes()).hexdigest()
            evaluation["validation_corpus_sha256"] = hashlib.sha256(validation_path.read_bytes()).hexdigest()
            evaluation_path = root / "evaluation.json"
            write_json(evaluation_path, evaluation)
            report = publish(train_path, model_path, validation_path, evaluation_path)
            self.assertEqual(report["training_controls"]["saved_proof_digest_matched"], 100)
            self.assertEqual(report["validation_controls"]["saved_proof_digest_matched"], 160)
            proof = root / "validation" / "arith_rss_pair_48" / "trials" / "00" / "proof.bin"
            proof.write_bytes(b"tampered")
            with self.assertRaisesRegex(ValueError, "saved proof bytes"):
                publish(train_path, model_path, validation_path, evaluation_path)


if __name__ == "__main__":
    unittest.main()
