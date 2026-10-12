"""Pinned cost evidence must agree with saved native trial artifacts."""

import hashlib
import json
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

S31_SOURCE_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31_SOURCE_ROOT / "benchmarks"))
from publish_whole_prover_multiscale import publish


class PinnedEvidenceTests(unittest.TestCase):
    def test_saved_proof_and_corpus_binding_are_checked(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            trial_dir = root / "arithmetic_16/trials/00"
            trial_dir.mkdir(parents=True)
            proof = trial_dir / "proof.bin"
            proof.write_bytes(b"native-proof")
            trial = {
                "proof_sha256": hashlib.sha256(proof.read_bytes()).hexdigest(),
                "proof_bytes": proof.stat().st_size,
                "native_verifier_accepted": True,
                "changed_public_statement_rejected": "public_outputs.result[0]",
                "independent_value_oracle": {"status": "passed"},
            }
            (trial_dir / "trial-report.json").write_text(json.dumps(trial))
            corpus = {
                "schema": "s31-multiscale-cost-corpus-v1", "host": {"machine": "test"},
                "samples_per_program": 1,
                "cases": {"arithmetic_16": {
                    "family": "arithmetic", "source_sha256": "a" * 64,
                    "compiler_sha256": "b" * 64, "lowering": "direct-gate",
                    "profile": "direct-m31-v4", "raw": {"qm31_ops": 1},
                    "padded": {"qm31_ops": 16}, "preprocessed_cells": 128,
                    "package_build": {"package_build_wall_seconds": 1.0},
                    "assignment_sha256": ["c" * 64],
                    "observed_cost_model": {"metrics": {
                        "paired_prove_and_verify_wall_seconds": {"median": 0.1},
                        "proof_bytes": {"median": proof.stat().st_size},
                        "prover_peak_rss_bytes": {"median": 1000},
                    }},
                }},
            }
            corpus_path = root / "multiscale-corpus.json"
            corpus_path.write_text(json.dumps(corpus))
            evaluation = {
                "schema": "s31-whole-prover-held-out-evaluation-v1",
                "corpus_sha256": hashlib.sha256(corpus_path.read_bytes()).hexdigest(),
                "accuracy": {"proof_bytes": {}}, "predictions": [],
                "cost_accuracy_gate_pass": False,
                "automatic_lowering_selection_enabled": False,
                "selection_reasons": ["insufficient training"],
            }
            evaluation_path = root / "held-out-evaluation.json"
            evaluation_path.write_text(json.dumps(evaluation))
            pinned = publish(corpus_path, evaluation_path)
            self.assertEqual(pinned["controls"], {
                "native_accepted": 1, "changed_claim_rejected": 1,
                "independent_oracle_passed": 1,
            })
            proof.write_bytes(b"tampered")
            with self.assertRaisesRegex(ValueError, "saved proof bytes"):
                publish(corpus_path, evaluation_path)
            proof.write_bytes(b"native-proof")
            evaluation["corpus_sha256"] = "0" * 64
            evaluation_path.write_text(json.dumps(evaluation))
            with self.assertRaisesRegex(ValueError, "not bound"):
                publish(corpus_path, evaluation_path)


if __name__ == "__main__":
    unittest.main()
