"""Native-free operation-family source, model, and score checks."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
S31 = HERE.parents[1]
sys.path[:0] = [str(HERE), str(S31 / "python")]

from independent_score import measurement as independent_measurement  # noqa: E402
from oracle import evaluate_relation  # noqa: E402
from study import (COUNTS, LIMITS, METRICS, OPERATIONS, P, ROWS, SAMPLES,
                   assignment_for, inventory, metric, prior_calibration,
                   score, source_for)  # noqa: E402
from text_frontend import compile_text  # noqa: E402


def trial(wall: float, after_pow: float, proof: int, rss: int) -> dict:
    return {"native_verifier_accepted": True,
            "changed_public_statement_rejected": "public_outputs.p1[0]",
            "independent_value_oracle": {"status": "passed"},
            "prove_seconds": wall - .01, "verify_seconds": .01,
            "prover_stages": {"fri_pow_seconds": wall - after_pow,
                              "interaction_pow_seconds": 0.0},
            "proof_bytes": proof, "prover_peak_rss_bytes": rss}


class OperationMixTransferTests(unittest.TestCase):
    def test_sources_have_distinct_hashes_and_correct_field_semantics(self) -> None:
        self.assertEqual(COUNTS, (96, 256, 448))
        self.assertEqual(OPERATIONS, ("add", "mul"))
        self.assertEqual({ROWS[n] for n in COUNTS}, {512, 1024})
        entries = inventory()
        self.assertEqual(len(entries), 6)
        self.assertEqual(len({v["source_sha256"] for v in entries.values()}), 6)
        assignments = [digest for v in entries.values()
                       for digest in v["assignment_sha256"]]
        self.assertEqual(len(assignments), 6 * SAMPLES)
        self.assertEqual(len(set(assignments)), len(assignments))
        for op in OPERATIONS:
            for count in COUNTS:
                relation, _ = compile_text(source_for(op, count))
                self.assertEqual(len(relation["nodes"]), count)
                self.assertEqual({node["op"] for node in relation["nodes"]}, {op})
                for sample in (0, 1, 11):
                    assignment = assignment_for(op, count, sample)
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"])
                self.assertEqual(assignment_for(op, count, 0)["public_inputs"]["x"],
                                 [P - 2, P - 1, 0, 1])

    def test_prior_calibration_is_complete_and_test_score_can_fail(self) -> None:
        _, calibration, _ = prior_calibration()
        model = calibration["model"]
        self.assertEqual(set(model), {"512", "1024"})
        self.assertEqual(set(model["512"]), set(METRICS))
        cases = {f"{op}-{count}": [trial(.1, .04, 60000, 10_000_000)] * SAMPLES
                 for op in OPERATIONS for count in COUNTS}
        result = score(model, cases)
        self.assertEqual(set(result["diagnostic_gates"]), set(LIMITS))
        self.assertEqual(set(result["operation_family_gates"]), set(OPERATIONS))
        with self.assertRaisesRegex(ValueError, "complete"):
            score(model, {"add-96": cases["add-96"]})
        self.assertAlmostEqual(metric(cases["add-96"][0], "paired_wall_seconds"), .1)
        self.assertAlmostEqual(independent_measurement(cases["add-96"][0],
                                                       "paired_after_pow_seconds"), .04)


if __name__ == "__main__":
    unittest.main()
