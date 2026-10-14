"""Hand-calculated UDR error terms, tradeoffs, and closed native admission."""

from __future__ import annotations

import copy
import unittest
from fractions import Fraction
from unittest.mock import patch

from scripts.release.pcs_fri_stwo_udr import (
    F, PAPER_OOD_POINTS, circle_fold_sizes, gate_udr_ledger, main,
    necessary_tradeoffs, scenario_arithmetic,
)
from scripts.tests.test_pcs_fri_gate_error_ledger import reviewed_shape


def one_table_scenario(t: int = 1 << 32, queries: int = 232) -> dict:
    n = 1 << 20
    return {
        "paper_protocol_variant": "idealized_protocols_1_3_4_degree_corrected",
        "grinding_bits": 0,
        "N": n, "B": 2,
        "theta_numerator": 16383, "theta_denominator": 65536,
        "queries": queries, "T": t, "R": 26, "lambda_bits": 256,
        "air_degree": 3, "max_message_dimension": 1,
        "public_input_messages": 0, "public_output_messages": 0,
        "fri_batch_max_width": 2,
        "tables": [{"rows": n, "air_constraints": 1, "uses": 1,
                    "yields": 1, "max_use_multiplicity": 1}],
        "fri_fold_domain_sizes": circle_fold_sizes(n, 2),
    }


class StwoUDRTests(unittest.TestCase):
    def test_full_composition_domain_and_both_published_formulas(self) -> None:
        result = scenario_arithmetic(one_table_scenario(), 64)
        errors = result["published_round_error_bounds"]
        alternatives = result["published_formula_discrepancy_bounds"]
        n = 1 << 20
        self.assertEqual(errors["air_logup"], f"{2 * n}/{F}")
        self.assertEqual(alternatives["air_composition_theorem3_displayed"], f"5/{F}")
        self.assertEqual(alternatives["air_composition_appendix_lemma6_table4"], f"3/{F}")
        self.assertEqual(errors["air_composition"], f"5/{F}")
        self.assertEqual(alternatives["air_ood_theorem3_displayed"],
                         f"{1 + 3 * n}/{PAPER_OOD_POINTS}")
        self.assertEqual(alternatives["air_ood_appendix_lemma7"],
                         f"{1 + 4 * n}/{PAPER_OOD_POINTS}")
        self.assertEqual(errors["air_ood"], f"{1 + 4 * n}/{PAPER_OOD_POINTS}")
        self.assertEqual(result["paper_inputs"]["D0_with_composition_quotient"], 4 * n)
        self.assertEqual(result["paper_inputs"]["fri_fold_domain_sizes"][0], 2 * n)
        self.assertEqual(result["paper_inputs"]["fri_fold_domain_sizes"][-1], 2)
        self.assertEqual(result["paper_inputs"]["R"], 26)
        self.assertEqual(errors["fri_cross_domain_batching"], f"{4 * n}/{F}")
        self.assertEqual(errors["fri_fold_0"], f"{6 * n}/{F}")
        self.assertEqual(len([name for name in errors if name.startswith("fri_fold_")]), 21)
        self.assertEqual(Fraction(errors["fri_query"]), Fraction(49153, 65536) ** 232)
        self.assertTrue(result["conditional_absolute_error_meets_target"])
        self.assertTrue(result["other_rounds_fit_absolute_target"])
        self.assertEqual(result["minimum_queries_for_absolute_target_if_other_rounds_fit"], 232)
        self.assertFalse(result["proven_release_admissible"])
        self.assertIsNone(result["native_proven_security_bits"])
        just_short = scenario_arithmetic(one_table_scenario(queries=231), 64)
        self.assertFalse(just_short["conditional_absolute_error_meets_target"])

        paper_convention = scenario_arithmetic(one_table_scenario(), 96)
        self.assertFalse(paper_convention["conditional_absolute_error_meets_target"])
        self.assertTrue(paper_convention["conditional_paper_work_factor_meets_target"])
        self.assertEqual(Fraction(paper_convention["BCS_total_over_T_paper_security_measure"]),
                         Fraction(paper_convention["BCS_total_formula"]) / (1 << 32))
        self.assertEqual(paper_convention[
            "minimum_queries_for_paper_work_factor_target_if_other_rounds_fit"], 232)
        self.assertFalse(scenario_arithmetic(one_table_scenario(queries=231), 96)[
            "conditional_paper_work_factor_meets_target"])

        masked = paper_convention["conditional_ideal_m31_masked_query_adaptation"]
        alpha = Fraction(49153, 65536)
        self.assertEqual(Fraction(masked["max_positive_set_bias"]), Fraction(2, 1 << 32))
        self.assertEqual(Fraction(masked["one_draw_good_set_mass_upper"]),
                         alpha + Fraction(2, 1 << 32))
        self.assertEqual(Fraction(masked["query_round_bound"]),
                         (alpha + Fraction(2, 1 << 32)) ** 232)
        self.assertGreater(Fraction(masked["query_round_bound"]),
                           Fraction(errors["fri_query"]))
        self.assertTrue(masked["work_factor_meets_target_if_other_rounds_apply"])
        self.assertEqual(masked["minimum_queries_for_work_factor_if_other_rounds_fit"], 232)
        self.assertFalse(scenario_arithmetic(one_table_scenario(queries=231), 96)[
            "conditional_ideal_m31_masked_query_adaptation"][
                "work_factor_meets_target_if_other_rounds_apply"])
        self.assertFalse(scenario_arithmetic(one_table_scenario(queries=70), 96)[
            "conditional_ideal_m31_masked_query_adaptation"][
                "work_factor_meets_target_if_other_rounds_apply"])
        self.assertTrue(scenario_arithmetic(one_table_scenario(t=1 << 64), 96)[
            "conditional_ideal_m31_masked_query_adaptation"][
                "work_factor_meets_target_if_other_rounds_apply"])

        two_tables = one_table_scenario()
        two_tables["tables"].append({"rows": n // 2, "air_constraints": 1,
                                     "uses": 1, "yields": 1, "max_use_multiplicity": 1})
        two = scenario_arithmetic(two_tables, 64)
        self.assertEqual(two["published_formula_discrepancy_bounds"][
            "air_composition_theorem3_displayed"], f"5/{F}")
        self.assertEqual(two["published_formula_discrepancy_bounds"][
            "air_composition_appendix_lemma6_table4"], f"6/{F}")
        self.assertEqual(two["published_round_error_bounds"]["air_composition"], f"6/{F}")

    def test_96_bit_tradeoff_and_universal_qm31_obstruction(self) -> None:
        row = gate_udr_ledger(reviewed_shape(), 96, 1 << 32)
        self.assertEqual(row["native_source_observations"]["configured_raw_queries"], 70)
        self.assertTrue(row["QM31_universal_absolute_OOD_floor_exceeds_target"])
        self.assertFalse(row["QM31_universal_paper_work_factor_OOD_floor_exceeds_target"])
        self.assertTrue(row["native_geometry_necessary_row"][
            "nonquery_envelope_exceeds_absolute_target"])
        self.assertFalse(row["native_geometry_necessary_row"][
            "nonquery_envelope_exceeds_paper_work_factor_target"])
        self.assertIsNone(row["unbound_native_theorem_terms"]["air_ood"])
        self.assertFalse(row["proven_release_admissible"])
        self.assertGreater(Fraction(1 << 28, F), Fraction(1, 1 << 96))
        self.assertLess(Fraction((1 << 28) - 1, F), Fraction(1, 1 << 96))
        self.assertGreater(Fraction(1, F), Fraction(1, 1 << 124))
        self.assertLess(Fraction(1, F), Fraction(1, 1 << 96))
        small_budget = necessary_tradeoffs(1 << 20, 96, 1)
        self.assertEqual([r["hypothetical_B"] for r in small_budget], [2, 4, 8, 16, 32])
        self.assertEqual([r["candidate_D0"] for r in small_budget],
                         [1 << 22, 1 << 24, 1 << 26, 1 << 28, 1 << 30])
        self.assertEqual([r["nonquery_envelope_exceeds_absolute_target"]
                          for r in small_budget],
                         [False, True, True, True, True])
        hypothetical = one_table_scenario(t=1, queries=243)
        self.assertTrue(scenario_arithmetic(hypothetical, 96)[
            "conditional_absolute_error_meets_target"])
        self.assertFalse(scenario_arithmetic(one_table_scenario(t=1, queries=242), 96)
                         ["conditional_absolute_error_meets_target"])

    def test_closed_admission_and_invalid_theorem_inputs(self) -> None:
        baseline = one_table_scenario()
        mutations = (
            lambda x: x.__setitem__("paper_protocol_variant", "native"),
            lambda x: x.__setitem__("grinding_bits", 26),
            lambda x: x.__setitem__("theta_numerator", 1 << 14),
            lambda x: x.__setitem__("R", 25),
            lambda x: x.__setitem__("air_degree", 4),
            lambda x: x["tables"][0].__setitem__("max_use_multiplicity", 2**31 - 1),
            lambda x: x["tables"][0].__setitem__("air_constraints", 0),
            lambda x: x["fri_fold_domain_sizes"].pop(),
            lambda x: x.__setitem__("B", 64),
        )
        for mutation in mutations:
            candidate = copy.deepcopy(baseline)
            mutation(candidate)
            with self.assertRaises(ValueError):
                scenario_arithmetic(candidate, 64)
        with patch("scripts.release.pcs_fri_stwo_udr.extract_gate",
                   return_value=reviewed_shape()), patch("sys.stdout"):
            self.assertEqual(main(["/trusted-by-test", "--require-proven"]), 2)


if __name__ == "__main__":
    unittest.main()
