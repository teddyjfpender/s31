"""Exact support conditioning and deliberately closed native admission."""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from scripts.release.pcs_fri_paired_ood_bridge import (
    ACCEPTED_OOD_SEEDS, F, PAPER_OOD_POINTS, Q, main, sensitivity,
)
from scripts.tests.test_pcs_fri_stwo_udr import one_table_scenario


class PairedOodBridgeTests(unittest.TestCase):
    def test_exact_support_and_conditional_sensitivity(self) -> None:
        result = sensitivity(one_table_scenario(), 96, candidate_height_count=8)
        support = result["support"]
        self.assertEqual(ACCEPTED_OOD_SEEDS, F - 2 - (2 * Q * Q - 3))
        self.assertEqual(ACCEPTED_OOD_SEEDS, (Q * Q - 1) ** 2)
        self.assertEqual(PAPER_OOD_POINTS - ACCEPTED_OOD_SEEDS,
                         2 * Q * Q - Q - 3)
        self.assertEqual(Fraction(support["paper_to_accepted_bad_event_mass_factor"]),
                         Fraction(PAPER_OOD_POINTS, ACCEPTED_OOD_SEEDS))
        self.assertTrue(support["factor_less_than_one_plus_2pow_minus_60"])
        candidate = result["candidate_same_bad_set_numerator_only"]
        self.assertGreater(Fraction(candidate["accepted_support_ood_expression"]),
                           Fraction(candidate["published_ood_upper_bound_expression"]))
        self.assertTrue(candidate["substituted_work_factor_expression_meets_target"])
        self.assertFalse(candidate["substituted_absolute_expression_meets_target"])
        self.assertFalse(result["proven_release_admissible"])
        self.assertIsNone(result["native_proven_security_bits"])
        geometry = result["hypothetical_cas05_geometry"]
        self.assertEqual(geometry["initial_domain_rows"], 1 << 22)
        self.assertEqual(geometry["terminal_domain_rows"], 1 << 14)
        self.assertEqual(geometry["terminal_QM31_coefficient_words"], 1 << 13)
        self.assertEqual(geometry["published_protocol3_n"], 21)
        self.assertEqual(geometry["published_protocol3_r"], 7)
        self.assertTrue(geometry["published_protocol3_variable_r_hypothesis_satisfied"])
        self.assertEqual(geometry["published_short_fold_domain_sizes"],
                         [1 << exponent for exponent in range(21, 13, -1)])
        self.assertEqual(geometry["published_short_fold_error_bounds_unique_decoding"],
                         [str(Fraction(3 * (1 << exponent), F))
                          for exponent in range(21, 13, -1)])
        self.assertEqual(geometry["minimum_idealized_BCS_round_count"], 13)
        caps = geometry["native_draft_source_caps_at_commit_9cd3f2989"]
        self.assertTrue(caps["sparse_verifier_visible_log_height_query_caps_pass"])
        self.assertFalse(caps["dense_host_prover_visible_log_height_query_caps_pass"])
        self.assertFalse(caps["full_profile_or_proof_admissible"])
        self.assertEqual(geometry["paper_full_single_fold_rounds"], 21)
        self.assertEqual(geometry["full_roster_folds_elided_by_early_terminal"], 13)
        self.assertFalse(geometry["native_protocol3_refinement_established"])
        short = result["hypothetical_short_protocol3_formula"]
        self.assertEqual(len(short["fold_error_roster"]), 8)
        self.assertEqual(short["minimum_idealized_R"], 13)
        self.assertEqual(short["explicit_scenario_R_used"], 26)
        self.assertIsNone(short["native_security_bits"])

    def test_rejects_invalid_paper_inputs_and_require_proven(self) -> None:
        changed = copy.deepcopy(one_table_scenario())
        changed["paper_protocol_variant"] = "native_CAS05"
        with self.assertRaises(ValueError):
            sensitivity(changed)
        with self.assertRaises(ValueError):
            sensitivity(one_table_scenario(), candidate_height_count=9)
        # A smaller paper domain crosses the dense host's height cap without
        # changing the published variable-r terminal geometry.
        small = copy.deepcopy(one_table_scenario())
        small["N"] = 1 << 14
        small["tables"][0]["rows"] = small["N"]
        small["fri_fold_domain_sizes"] = [1 << exponent
                                         for exponent in range(15, 0, -1)]
        small_geometry = sensitivity(small, candidate_height_count=8)[
            "hypothetical_cas05_geometry"]
        self.assertEqual(small_geometry["terminal_QM31_coefficient_words"], 128)
        self.assertEqual(small_geometry["terminal_domain_rows"], 256)
        self.assertTrue(small_geometry["native_draft_source_caps_at_commit_9cd3f2989"]
                        ["dense_host_prover_visible_log_height_query_caps_pass"])
        with tempfile.TemporaryDirectory() as directory:
            scenario = Path(directory) / "scenario.json"
            scenario.write_text(json.dumps(one_table_scenario()))
            with patch("sys.stdout"):
                self.assertEqual(main([str(scenario), "--require-proven"]), 2)


if __name__ == "__main__":
    unittest.main()
