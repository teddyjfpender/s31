"""Synthetic scoring and chronology attacks; no native build or timing."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import study


def predictions() -> dict:
    return {"warm_wall_quantile_ns": {"0.05": 80, "0.5": 100, "0.95": 120},
            "proof_bytes_center": 1000, "proof_bytes_interval": [900, 1100]}


def corpus(tail_count: int = 0) -> dict:
    records = []
    for number, (shape, count) in enumerate(study.p.SPLITS["heldout"]):
        trials = []
        for index, repeat in study.TRIALS:
            wall = 500 if index > 79 - tail_count else 100
            trials.append({"claim_index": index, "repeat": repeat,
                           "assignment_sha256": f"heldout-a-{number}-{index}",
                           "statement_sha256": f"heldout-s-{number}-{index}",
                           "first_verified_process_wall_ns": wall,
                           "proof_bytes": 1000})
        records.append({"name": f"{shape}_n{count}", "shape": shape,
                        "call_count": count, "source_sha256": f"heldout-source-{number}",
                        "cold_warm": {}, "build_wall_ns": 1, "trials": trials})
    return {"records": records}


class HeldoutScoringTests(unittest.TestCase):
    def evaluate_synthetic(self, tail_count: int = 0,
                           leak_source: bool = False) -> dict:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "train.json").write_bytes(study.v2.canonical({"records": []}))
            heldout = corpus(tail_count)
            (root / "heldout.json").write_bytes(study.v2.canonical(heldout))
            tracked_train = root / "tracked-train.json"
            tracked_heldout = root / "tracked-heldout.json"
            evaluation = root / "evaluation.json"
            tracked_train.write_bytes((root / "train.json").read_bytes())
            tracked_heldout.write_bytes((root / "heldout.json").read_bytes())
            fitted = {"training_source_sha256": ["heldout-source-0" if leak_source
                                                    else "train-source"],
                      "training_assignment_sha256": ["train-assignment"],
                      "training_statement_sha256": ["train-statement"]}
            protocol = {"gates": study.p.GATES}
            with patch.object(study, "TRAIN", tracked_train), \
                 patch.object(study, "HELDOUT", tracked_heldout), \
                 patch.object(study, "EVALUATION", evaluation), \
                 patch.object(study, "frozen", return_value=(protocol, "protocol")), \
                 patch.object(study, "anchor_required", return_value=fitted), \
                 patch.object(study, "check_corpus"), \
                 patch.object(study, "audit"), \
                 patch.object(study.model, "prediction", return_value=predictions()):
                if leak_source:
                    with self.assertRaisesRegex(ValueError, "leaked"):
                        study.evaluate(root, "model", "anchor")
                    self.assertFalse(evaluation.exists())
                    return {}
                result = study.evaluate(root, "model", "anchor")
                saved = study.v2.parse(evaluation.read_bytes())
            self.assertEqual(result["evaluation_sha256"], study.v2.sha(evaluation.read_bytes()))
            return saved

    def test_known_distribution_passes_all_six_gates(self) -> None:
        saved = self.evaluate_synthetic()
        self.assertTrue(saved["all_gates_pass"])
        self.assertEqual(set(saved["gate_pass"]), {"wall_error", "wall_coverage",
                                                   "wall_per_source", "proof_error",
                                                   "proof_coverage", "proof_per_source"})
        self.assertTrue(all(saved["gate_pass"].values()))

    def test_heavy_tail_fails_coverage_despite_correct_median(self) -> None:
        saved = self.evaluate_synthetic(tail_count=25)
        self.assertFalse(saved["all_gates_pass"])
        self.assertTrue(saved["gate_pass"]["wall_error"])
        self.assertFalse(saved["gate_pass"]["wall_coverage"])
        self.assertFalse(saved["gate_pass"]["wall_per_source"])
        self.assertTrue(saved["gate_pass"]["proof_coverage"])
        self.assertEqual(saved["metrics"]["wall_program_p90_median_relative_error"], 0)

    def test_source_leakage_is_rejected_before_scoring(self) -> None:
        self.evaluate_synthetic(leak_source=True)


class ChronologyTests(unittest.TestCase):
    def test_stale_model_anchor_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            train, model, anchor, protocol = (root / name for name in
                                             ("train.json", "model.json", "anchor.json",
                                              "protocol.json"))
            train.write_bytes(study.v2.canonical({"records": []}))
            protocol.write_bytes(study.v2.canonical({}))
            expected_model = {"schema": "synthetic-model"}
            model.write_bytes(study.v2.canonical(expected_model))
            model_sha = study.v2.sha(model.read_bytes())
            anchor.write_bytes(study.v2.canonical({
                "schema": "s31-mixed-cost-v4-model-anchor",
                "status": "commit-training-model-anchor-before-heldout-build",
                "protocol_sha256": "protocol",
                "train_corpus_sha256": study.v2.sha(train.read_bytes()),
                "model_sha256": model_sha}))
            with patch.object(study, "TRAIN", train), \
                 patch.object(study, "MODEL", model), \
                 patch.object(study, "ANCHOR", anchor), \
                 patch.object(study, "PROTOCOL", protocol), \
                 patch.object(study, "check_corpus"), \
                 patch.object(study, "model_from_training", return_value=expected_model), \
                 patch.object(study, "committed", return_value=False):
                with self.assertRaisesRegex(ValueError, "committed training-only anchor"):
                    study.anchor_required("protocol", model_sha, "0" * 40)

    def test_heldout_anchor_guard_runs_before_creating_output(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            with patch.object(study, "frozen", return_value=({}, "protocol")), \
                 patch.object(study, "anchor_required", side_effect=ValueError("stale anchor")):
                with self.assertRaisesRegex(ValueError, "stale anchor"):
                    study.run("heldout", root, "model", "0" * 40)
            self.assertFalse((root / "heldout").exists())


if __name__ == "__main__":
    unittest.main()
