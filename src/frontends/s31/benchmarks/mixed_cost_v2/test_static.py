"""Native-free checks of prospective claim independence and model arithmetic."""

from __future__ import annotations

import unittest

import study


class ProspectiveStudyTests(unittest.TestCase):
    def test_all_claims_are_fresh_and_splits_disjoint(self) -> None:
        prior = study.prior_claim_hashes()
        seen_assignments: set[str] = set()
        seen_statements: set[str] = set()
        sources: dict[str, set[str]] = {split: set() for split in study.SPLITS}
        for split, programs in study.SPLITS.items():
            for shape, count in programs:
                for index in range(study.ASSIGNMENTS):
                    source, assignment, statement = study.case(shape, count, index)
                    sources[split].add(study.sha(source))
                    assignment_sha, statement_sha = study.sha(assignment), study.sha(statement)
                    self.assertNotIn(assignment_sha, prior | seen_assignments)
                    self.assertNotIn(statement_sha, prior | seen_statements)
                    seen_assignments.add(assignment_sha)
                    seen_statements.add(statement_sha)
        self.assertEqual(len(seen_assignments), 160)
        self.assertEqual(len(seen_statements), 160)
        self.assertEqual(len(sources["train"]), 4)
        self.assertEqual(len(sources["heldout"]), 4)
        self.assertFalse(sources["train"] & sources["heldout"])

    def test_prediction_and_empirical_quantile(self) -> None:
        model = {"wall_constant_ns": 120., "proof_intercept_bytes": 100.,
                 "proof_slope_bytes_per_call": 7.}
        self.assertEqual(study.prediction(model, 4),
                         {"first_verified_process_wall_ns": 120., "proof_bytes": 128.})
        self.assertEqual(study.quantile([1., 3., 5., 7., 9.], .9), 8.2)


if __name__ == "__main__":
    unittest.main()
