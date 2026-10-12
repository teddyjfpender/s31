"""Static paired-forecast controls using previously recorded native timing rows."""

from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

import lifecycle

ROOT = Path(__file__).resolve().parents[5]
LANGUAGE = ROOT / "design/s31/measurements/language"


def fixture() -> tuple[dict, dict, dict]:
    historical = json.loads((LANGUAGE / "mixed-cost-v23-n8-holdout-result.json").read_text())
    rows = historical["record"]["trials"]
    paired = rows[:2]
    for row in rows[2:]:
        paired.append(row)
        again = copy.deepcopy(row)
        again["repeat"] = 1
        paired.append(again)
    record = {**historical["record"], "trials": paired}
    center = 150_345_958
    forecast = {
        "repeat_nonpow_center_ns": center,
        "build_wall_ns": record["build_wall_ns"],
        "first_post_build_verified_wall_ns": rows[0]["first_verified_process_wall_ns"],
        "build_plus_42_verified_proofs_sum_ns": record["build_wall_ns"] + sum(
            row["first_verified_process_wall_ns"] for row in paired),
    }
    gates = {
        "build_wall_relative_error_max": 1,
        "first_post_build_verified_relative_error_max": 1,
        "build_plus_42_proofs_relative_error_max": 1,
        "paired_repeat_median_relative_error_max": 1,
        "paired_repeat_relative_error_within_35pct_min": 0,
        "repeat_nonpow_median_relative_error_max": 1,
    }
    return record, forecast, gates


class PairedForecastTests(unittest.TestCase):
    def test_first_claim_pow_conditions_repeat_without_using_repeat_pow(self) -> None:
        record, forecast, gates = fixture()
        first = lifecycle.score(record, forecast, gates)
        shift = 10_000_000
        record["trials"][0]["native_phases_ns"]["fri_pow_ns"] += shift
        changed = lifecycle.score(record, forecast, gates)
        self.assertEqual(changed["repeat_predicted_wall_ns"][0] -
                         first["repeat_predicted_wall_ns"][0], shift)
        self.assertEqual(changed["repeat_observed_wall_ns"],
                         first["repeat_observed_wall_ns"])

    def test_pair_identity_and_roster_are_mandatory(self) -> None:
        record, forecast, gates = fixture()
        record["trials"][3]["proof_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "identity"):
            lifecycle.score(record, forecast, gates)
        record, forecast, gates = fixture()
        record["trials"][3]["claim_index"] = 0
        with self.assertRaisesRegex(ValueError, "identity"):
            lifecycle.score(record, forecast, gates)

    def test_first_pow_must_fit_first_process_wall(self) -> None:
        record, forecast, gates = fixture()
        record["trials"][0]["native_phases_ns"]["fri_pow_ns"] = record[
            "trials"][0]["first_verified_process_wall_ns"]
        with self.assertRaisesRegex(ValueError, "nonpositive paired timing"):
            lifecycle.score(record, forecast, gates)


if __name__ == "__main__":
    unittest.main()
