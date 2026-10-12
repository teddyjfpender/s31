"""Native-free checks for the frozen geometry transfer protocol and scorer."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
sys.path[:0] = [str(HERE), str(S31 / "python")]

from oracle import evaluate_relation  # noqa: E402
from independent_score import value as independent_value  # noqa: E402
from study import (GEOMETRY, HELDOUT, LIMITS, METRICS, P, SAMPLES, TRAIN,
                   assignment_for, calibration, inventory, metric, score, source_for)  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def trial(wall: float, after_pow: float, proof: int, rss: int) -> dict:
    return {"native_verifier_accepted": True,
            "changed_public_statement_rejected": "public_outputs.p1[0]",
            "independent_value_oracle": {"status": "passed"},
            "prove_seconds": wall - .01, "verify_seconds": .01,
            "prover_stages": {"fri_pow_seconds": wall - after_pow,
                              "interaction_pow_seconds": 0.0},
            "proof_bytes": proof, "prover_peak_rss_bytes": rss}


class GeometryTransferTests(unittest.TestCase):
    def test_all_sources_and_assignments_have_independent_field_semantics(self) -> None:
        self.assertEqual((TRAIN, HELDOUT), ((32, 192, 384), (96, 256, 448)))
        self.assertEqual({GEOMETRY[g] for g in TRAIN}, {512, 1024})
        self.assertEqual({GEOMETRY[g] for g in HELDOUT}, {512, 1024})
        planned = inventory()
        self.assertEqual(len({v["source_sha256"] for v in planned.values()}), 6)
        digests = [digest for entry in planned.values()
                   for digest in entry["assignment_sha256"]]
        self.assertEqual(len(digests), 6 * SAMPLES)
        self.assertEqual(len(set(digests)), len(digests))
        for gates in (*TRAIN, *HELDOUT):
            relation, _ = compile_text(source_for(gates))
            self.assertEqual(len(relation["nodes"]), gates)
            for sample in (0, 1, 11):
                assignment = assignment_for(gates, sample)
                self.assertEqual(evaluate_relation(relation, assignment),
                                 assignment["public_outputs"])
            self.assertEqual(assignment_for(gates, 0)["public_inputs"]["x"],
                             [P - 2, P - 1, 0, 1])

    def test_metric_controls_and_pow_accounting(self) -> None:
        row = trial(.12, .04, 56000, 9_000_000)
        self.assertAlmostEqual(metric(row, "paired_wall_seconds"), .12)
        self.assertAlmostEqual(metric(row, "paired_after_pow_seconds"), .04)
        self.assertEqual(metric(row, "proof_bytes"), 56000)
        self.assertAlmostEqual(independent_value(row, "paired_wall_seconds"), .12)
        self.assertAlmostEqual(independent_value(row, "paired_after_pow_seconds"), .04)
        for mutation in ({"native_verifier_accepted": False},
                         {"changed_public_statement_rejected": False},
                         {"independent_value_oracle": {"status": "failed"}}):
            with self.assertRaises(ValueError):
                metric({**row, **mutation}, "proof_bytes")
        with self.assertRaisesRegex(ValueError, "PoW timers"):
            metric({**row, "prover_stages": {}}, "paired_after_pow_seconds")

    def test_sealed_stratum_model_and_heldout_scoring(self) -> None:
        train = {32: [trial(.10, .04, 55000, 9_000_000)] * SAMPLES,
                 192: [trial(.12, .05, 57000, 9_500_000)] * SAMPLES,
                 384: [trial(.20, .08, 62000, 12_000_000)] * SAMPLES}
        model = calibration(train)
        self.assertEqual(set(model), {"512", "1024"})
        self.assertEqual(set(model["512"]), set(METRICS))
        self.assertAlmostEqual(model["512"]["paired_wall_seconds"]["center"], .11)
        self.assertAlmostEqual(model["1024"]["paired_wall_seconds"]["center"], .20)
        heldout = {96: [trial(.11, .045, 56000, 9_250_000)] * SAMPLES,
                   256: [trial(.19, .075, 61000, 12_000_000)] * SAMPLES,
                   448: [trial(.21, .085, 63000, 12_000_000)] * SAMPLES}
        result = score(model, heldout)
        self.assertTrue(result["all_diagnostic_gates_pass"])
        self.assertEqual(set(result["diagnostic_gates"]), set(LIMITS))
        self.assertEqual(result["cases"]["448"]["padded_qm31_rows"], 1024)
        with self.assertRaisesRegex(ValueError, "complete train"):
            calibration({32: train[32]})
        with self.assertRaisesRegex(ValueError, "complete held-out"):
            score(model, {96: heldout[96]})
        too_slow = {**heldout, 448: [trial(.50, .30, 63000, 12_000_000)] * SAMPLES}
        failed = score(model, too_slow)
        self.assertFalse(failed["all_diagnostic_gates_pass"])
        self.assertFalse(failed["diagnostic_gates"]["paired_wall_seconds"])


if __name__ == "__main__":
    unittest.main()
