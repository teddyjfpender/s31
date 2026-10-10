"""Pinned prospective cost evidence must agree with native proof artifacts."""

import hashlib
import json
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

S31_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31_ROOT / "benchmarks"))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from publish_stage_aware_cost_v1 import publish
from stage_aware_predictor_v1 import PROTOCOL, evaluate, fit_model
from test_stage_aware_predictor_v1 import synthetic_corpus


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, sort_keys=True) + "\n")


def materialize_corpus(root: Path, corpus: dict) -> Path:
    for name, case in corpus["cases"].items():
        source = root / "generated-sources" / f"{name}.s31"
        source.parent.mkdir(parents=True, exist_ok=True)
        source.write_text(f"source:{corpus['split']}:{name}")
        case["source"] = str(source)
        case["source_sha256"] = hashlib.sha256(source.read_bytes()).hexdigest()
        scale = sum(case["raw"].values())
        for index, trial in enumerate(case["trials"]):
            directory = root / name / "trials" / f"{index:02d}"
            directory.mkdir(parents=True)
            proof = bytes([index % 256]) * scale
            (directory / "proof.bin").write_bytes(proof)
            trial["proof_bytes"] = len(proof)
            trial["proof_sha256"] = hashlib.sha256(proof).hexdigest()
            write_json(directory / "trial-report.json", trial)
    path = root / "stage-aware-corpus.json"
    write_json(path, corpus)
    return path


class PublishStageAwareTests(unittest.TestCase):
    def test_refit_replay_and_saved_proof_audit(self) -> None:
        protocol = json.loads(PROTOCOL.read_text())
        with TemporaryDirectory() as directory:
            root = Path(directory)
            train = synthetic_corpus("train", protocol)
            train_path = materialize_corpus(root / "train", train)
            model = fit_model(train, protocol)
            model["training_corpus_sha256"] = hashlib.sha256(train_path.read_bytes()).hexdigest()
            model_path = root / "model.json"
            write_json(model_path, model)
            validation = synthetic_corpus("validation", protocol)
            validation["frozen_model_sha256"] = hashlib.sha256(model_path.read_bytes()).hexdigest()
            validation_path = materialize_corpus(root / "validation", validation)
            evaluation = evaluate(model, validation, protocol)
            evaluation["frozen_model_sha256"] = hashlib.sha256(model_path.read_bytes()).hexdigest()
            evaluation["validation_corpus_sha256"] = hashlib.sha256(validation_path.read_bytes()).hexdigest()
            evaluation_path = root / "evaluation.json"
            write_json(evaluation_path, evaluation)
            pinned = publish(train_path, model_path, validation_path, evaluation_path)
            self.assertEqual(pinned["training_controls"]["saved_proof_digest_matched"], 260)
            self.assertEqual(pinned["validation_controls"]["saved_proof_digest_matched"], 240)
            self.assertFalse(pinned["automatic_lowering_selection_enabled"])
            proof = root / "validation" / "arithmetic_32" / "trials" / "00" / "proof.bin"
            proof.write_bytes(b"tampered")
            with self.assertRaisesRegex(ValueError, "saved proof bytes"):
                publish(train_path, model_path, validation_path, evaluation_path)


if __name__ == "__main__":
    unittest.main()
