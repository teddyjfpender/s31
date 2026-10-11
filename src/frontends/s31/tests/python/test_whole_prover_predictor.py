"""Held-out cost evaluation must group by program and disable unsafe selection."""

import hashlib
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

S31_SOURCE_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31_SOURCE_ROOT / "benchmarks"))

from whole_prover_predictor import evaluate
from benchmark_whole_prover_multiscale import (
    ARITHMETIC_ROUNDS, HASH_DEPTHS, SIGNED_WIDTHS,
    arithmetic_assignment, arithmetic_program, hash_assignment, hash_program,
    workload_cases,
)
sys.path.insert(0, str(S31_SOURCE_ROOT / "python"))
from oracle import evaluate_relation


def case(name: str, family: str, scale: int, latency_multiplier: float = 1.0) -> dict:
    def metric(value: float) -> dict:
        return {"observations": 5, "median": value}

    return {
        "family": family,
        "source_sha256": hashlib.sha256(name.encode()).hexdigest(),
        "padded": {"qm31_ops": scale},
        "preprocessed_cells": 8 * scale,
        "observed_cost_model": {
            "verified_trials": 5,
            "metrics": {
                "paired_prove_and_verify_wall_seconds": metric(latency_multiplier * 0.001 * scale ** 0.5),
                "proof_bytes": metric(100 * scale ** 0.5),
                "prover_peak_rss_bytes": metric(1000 * (8 * scale) ** 0.5),
            },
        },
    }


def corpus(families=("arithmetic", "hash", "fixed_width"), noisy=False) -> dict:
    rows = {}
    for family in families:
        for scale in (16, 64, 256, 1024):
            name = f"{family}_{scale}"
            multiplier = 10.0 if noisy and name == "hash_256" else 1.0
            rows[name] = case(name, family, scale, multiplier)
    return {"cases": rows}


class PredictorTests(unittest.TestCase):
    def test_multiscale_generators_match_independent_value_oracle(self) -> None:
        for rounds in ARITHMETIC_ROUNDS:
            for index in (0, 2):
                assignment = arithmetic_assignment(rounds, index)
                self.assertEqual(evaluate_relation(arithmetic_program(rounds), assignment),
                                 assignment["public_outputs"])
        for depth in HASH_DEPTHS:
            for index in (0, 2):
                assignment = hash_assignment(depth, index)
                self.assertEqual(evaluate_relation(hash_program(depth), assignment),
                                 assignment["public_outputs"])

    def test_multiscale_corpus_has_twelve_programs_and_distinct_assignments(self) -> None:
        with TemporaryDirectory() as directory:
            workloads = workload_cases(Path(directory), 3)
            self.assertEqual(len(workloads), 12)
            self.assertEqual({item["family"] for item in workloads},
                             {"arithmetic", "hash", "fixed_width"})
            self.assertEqual(len(ARITHMETIC_ROUNDS), 4)
            self.assertEqual(len(HASH_DEPTHS), 4)
            self.assertEqual(len(SIGNED_WIDTHS), 4)
            for item in workloads:
                self.assertTrue(item["source"].is_file())
                self.assertEqual(len(item["assignments"]), 3)
                self.assertEqual(len({str(a) for a in item["assignments"]}), 3)

    def test_program_level_holdout_and_uncertainty(self) -> None:
        result = evaluate(corpus())
        self.assertEqual(result["programs"], 12)
        self.assertEqual(len(result["predictions"]), 36)
        self.assertEqual(result["unpredicted"], [])
        for item in result["predictions"]:
            self.assertEqual(item["training_programs"], 3)
            self.assertAlmostEqual(item["relative_error"], 0, places=10)
            self.assertLessEqual(item["empirical_interval"]["lower"], item["measured"] * (1 + 1e-10))
            self.assertGreaterEqual(item["empirical_interval"]["upper"], item["measured"] * (1 - 1e-10))
        self.assertTrue(result["cost_accuracy_gate_pass"])
        self.assertFalse(result["automatic_lowering_selection_enabled"])

    def test_weak_held_out_error_fails_accuracy_gate(self) -> None:
        result = evaluate(corpus(noisy=True))
        self.assertFalse(result["cost_accuracy_gate_pass"])
        self.assertGreater(result["accuracy"]["paired_prove_and_verify_wall_seconds"]["max_relative_error"], 0.35)
        self.assertFalse(result["automatic_lowering_selection_enabled"])

    def test_duplicate_source_identity_is_rejected(self) -> None:
        sample = corpus(families=("arithmetic",))
        sample["cases"]["arithmetic_64"]["source_sha256"] = sample["cases"]["arithmetic_16"]["source_sha256"]
        with self.assertRaisesRegex(ValueError, "leak a program"):
            evaluate(sample)

    def test_mixed_profile_and_repeated_assignment_are_rejected(self) -> None:
        sample = corpus(families=("arithmetic",))
        sample["cases"]["arithmetic_64"]["profile"] = "different-profile"
        with self.assertRaisesRegex(ValueError, "mixed profile"):
            evaluate(sample)
        sample = corpus(families=("arithmetic",))
        sample["cases"]["arithmetic_16"]["assignment_sha256"] = ["same"] * 5
        with self.assertRaisesRegex(ValueError, "assignments must be distinct"):
            evaluate(sample)

    def test_too_few_training_scales_is_explicit(self) -> None:
        sample = {"cases": {name: case(name, "arithmetic", scale)
                            for name, scale in (("small", 16), ("large", 64))}}
        result = evaluate(sample)
        self.assertEqual(result["predictions"], [])
        self.assertEqual(len(result["unpredicted"]), 6)
        self.assertFalse(result["automatic_lowering_selection_enabled"])


if __name__ == "__main__":
    unittest.main()
