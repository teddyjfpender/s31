"""Focused exact-arithmetic controls for the conditional P05 partition floor."""

import unittest
from fractions import Fraction

from scripts.release.pcs_fri_gate_batch_partition import ledger


class GateBatchPartitionTests(unittest.TestCase):
    def test_bcs_adjusted_width_boundary(self) -> None:
        report = ledger()
        parameters = report["candidate_paper_parameters"]
        field = parameters["field_cardinality_QM31"]
        d0 = parameters["D0_assumed_N_times_B_squared"]
        t = parameters["T_hash_queries"]
        target = Fraction(1, 1 << parameters["work_factor_target_bits_at_T_2_to_64"])

        def isolated(m: int) -> Fraction:
            return Fraction((t + 1) * (m - 1) * d0, t * field)

        self.assertEqual(report["largest_integer_M_passing_isolated_factor"], 64)
        self.assertLessEqual(isolated(64), target)
        self.assertGreater(isolated(65), target)
        self.assertIsNone(report["native_to_paper_batch_width_M"])
        self.assertFalse(report["proven_release_admissible"])

    def test_conditional_partition_counts(self) -> None:
        cases = {case["label"]: case for case in ledger()["cases"]}
        originals = cases["originals_only"]
        paired = cases["one_original_and_one_own_quotient_per_column_same_batch"]
        self.assertEqual(originals["conditional_total_functions"], 193)
        self.assertEqual(originals["minimum_groups_if_only_each_group_max_term_is_checked"], 4)
        self.assertEqual(originals["minimum_groups_if_group_batch_terms_are_additive"], 130)
        self.assertEqual(paired["conditional_total_functions"], 386)
        self.assertEqual(paired["minimum_groups_if_only_each_group_max_term_is_checked"], 7)
        self.assertEqual(paired["minimum_groups_if_group_batch_terms_are_additive"], 323)
        self.assertTrue(originals["unpartitioned_lower_term_over_target"]["exceeds_one"])
        self.assertTrue(paired["unpartitioned_lower_term_over_target"]["exceeds_one"])


if __name__ == "__main__":
    unittest.main()
