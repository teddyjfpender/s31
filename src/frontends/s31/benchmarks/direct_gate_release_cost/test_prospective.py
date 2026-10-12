"""Fast protocol and accounting checks; no native package build."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from prospective import (HELDOUT, METRICS, SAMPLES, TRAIN, calibration,
                         planned_sources, score, target)


def trial(wall: float, proof_bytes: int = 54000, rss: int = 9_000_000) -> dict:
    return {"prove_seconds": wall - .02, "verify_seconds": .02,
            "proof_bytes": proof_bytes, "prover_peak_rss_bytes": rss,
            "prover_stages": {"fri_pow_seconds": .01,
                              "interaction_pow_seconds": .001}}


class ProspectiveCostTests(unittest.TestCase):
    def test_fixed_program_and_witness_roster_is_disjoint(self) -> None:
        self.assertEqual(TRAIN, (1, 4, 16))
        self.assertEqual(HELDOUT, (2, 8, 12))
        self.assertFalse(set(TRAIN) & set(HELDOUT))
        sources = planned_sources()
        self.assertEqual(set(sources), {str(value) for value in (*TRAIN, *HELDOUT)})
        self.assertEqual(len({item["source_sha256"] for item in sources.values()}), 6)
        assignment_digests = [digest for item in sources.values()
                              for digest in item["assignment_sha256"]]
        self.assertEqual(len(assignment_digests), 6 * SAMPLES)
        self.assertEqual(len(set(assignment_digests)), len(assignment_digests))

    def test_process_wall_and_pow_accounting(self) -> None:
        observed = trial(.08)
        self.assertAlmostEqual(target(observed, "paired_wall_seconds"), .08)
        self.assertAlmostEqual(target(observed, "pow_seconds"), .011)
        self.assertAlmostEqual(target(observed, "paired_after_pow_seconds"), .069)
        self.assertEqual(target(observed, "proof_bytes"), 54000)
        self.assertEqual(target(observed, "prover_peak_rss_bytes"), 9_000_000)
        with self.assertRaisesRegex(ValueError, "PoW timers"):
            target({**observed, "prover_stages": {}}, "paired_after_pow_seconds")

    def test_sealed_constant_prediction_scores_only_holdout(self) -> None:
        training = {gates: [trial(.06 + gates * .001)] * SAMPLES for gates in TRAIN}
        predictions = calibration(training)
        self.assertEqual(set(predictions), set(METRICS))
        self.assertAlmostEqual(predictions["paired_wall_seconds"]["center"], .064)
        self.assertEqual(predictions["proof_bytes"]["center"], 54000)
        heldout = {gates: [trial(.065)] * SAMPLES for gates in HELDOUT}
        result = score(predictions, heldout)
        self.assertEqual(set(result["cases"]), {"2", "8", "12"})
        self.assertTrue(result["all_diagnostic_gates_pass"])
        with self.assertRaisesRegex(ValueError, "predeclared held-out"):
            score(predictions, {2: heldout[2]})


if __name__ == "__main__":
    unittest.main()
