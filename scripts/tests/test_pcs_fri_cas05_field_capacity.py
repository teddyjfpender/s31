"""Exact short-cascade field capacity, with no native security claim."""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch

from scripts.release.pcs_fri_cas05_field_capacity import field_rows, main
from scripts.release.pcs_fri_stwo_udr import Q
from scripts.tests.test_pcs_fri_stwo_udr import one_table_scenario


class Cas05FieldCapacityTests(unittest.TestCase):
    def test_published_fixture_matches_handwritten_scenario(self) -> None:
        fixture = Path(__file__).resolve().parents[1] / "release/fixtures/cas05_one_table_paper.json"
        self.assertEqual(json.loads(fixture.read_text()), one_table_scenario())

    def test_absolute_vs_work_factor_and_field_degree(self) -> None:
        result = field_rows(one_table_scenario(), 8, 96, 13)
        rows = {row["extension_degree_over_M31"]: row
                for row in result["field_rows"]}
        self.assertEqual(result["hypothetical_inputs"]["short_R"], 13)
        self.assertEqual(result["hypothetical_inputs"]["minimum_idealized_short_R"], 13)
        self.assertFalse(rows[4]["nonquery_fits_absolute_target"])
        self.assertEqual(rows[4]["largest_nonquery_paper_round"], "fri_fold_0")
        self.assertEqual(Fraction(rows[4]["largest_nonquery_paper_bound"]),
                         Fraction(3 * (1 << 21), Q ** 4))
        self.assertIsNone(rows[4]["minimum_queries_for_absolute_target_if_nonquery_fits"])
        self.assertTrue(rows[4]["nonquery_fits_paper_work_factor_target"])
        self.assertEqual(rows[4]["minimum_queries_for_paper_work_factor_target_if_nonquery_fits"], 232)
        self.assertTrue(rows[6]["nonquery_fits_absolute_target"])
        self.assertEqual(Fraction(rows[6]["largest_nonquery_paper_bound"]),
                         Fraction(3 * (1 << 21), Q ** 6))
        self.assertEqual(rows[6]["minimum_queries_for_absolute_target_if_nonquery_fits"], 309)
        self.assertFalse(rows[6]["given_scenario_fits_absolute_target"])
        self.assertTrue(rows[6]["given_scenario_fits_paper_work_factor_target"])
        self.assertLess(Fraction(rows[6]["largest_nonquery_paper_bound"]),
                        Fraction(1, 1 << 128))
        self.assertFalse(result["proven_release_admissible"])
        self.assertIsNone(result["native_proven_security_bits"])

        at_threshold = field_rows(one_table_scenario(queries=309), 8, 96, 13)
        just_below = field_rows(one_table_scenario(queries=308), 8, 96, 13)
        self.assertTrue(at_threshold["field_rows"][2]["given_scenario_fits_absolute_target"])
        self.assertFalse(just_below["field_rows"][2]["given_scenario_fits_absolute_target"])
        self.assertFalse(at_threshold["field_rows"][1]["given_scenario_fits_absolute_target"])

    def test_rejects_bad_rounds_field_degrees_and_paper_inputs(self) -> None:
        scenario = one_table_scenario()
        with self.assertRaisesRegex(ValueError, "short R undercounts"):
            field_rows(scenario, 8, 96, 12)
        with self.assertRaisesRegex(ValueError, "field degrees"):
            field_rows(scenario, 8, 96, 13, (4, 5, 6))
        changed = copy.deepcopy(scenario)
        changed["grinding_bits"] = 26
        with self.assertRaisesRegex(ValueError, "zero grinding credit"):
            field_rows(changed, 8, 96, 13)
        with tempfile.TemporaryDirectory() as directory:
            file = Path(directory) / "paper.json"
            file.write_text(json.dumps(scenario))
            with patch("sys.stdout"):
                self.assertEqual(main([str(file), "--height-count", "8",
                                       "--short-rounds", "13", "--require-proven"]), 2)


if __name__ == "__main__":
    unittest.main()
