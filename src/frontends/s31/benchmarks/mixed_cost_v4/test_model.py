"""Native-free tests of the predeclared v4 distributional fit."""

from __future__ import annotations

import math
import unittest

import model


def rows(per_program: int) -> list[dict]:
    result = []
    for name, count in model.PROGRAMS.items():
        for index in range(per_program):
            fri = 8_000_000 + (index * 257_119) % 12_000_000
            interaction = 400_000 + (index * 71_113) % 700_000
            base = 20_000_000 + count * 1_000_000 + (index % 5 - 2) * 50_000
            result.append({"program": name, "call_count": count,
                           "wall_ns": base + fri + interaction,
                           "fri_pow_ns": fri, "interaction_pow_ns": interaction,
                           "proof_bytes": 50_000 + count * 10_000 +
                               (index % 7 - 3) * 100})
    return result


class V4ModelTests(unittest.TestCase):
    def test_fit_and_distribution_quantiles(self) -> None:
        value = model.fit(rows(model.FIT_ROWS_PER_PROGRAM),
                          rows(model.CAL_ROWS_PER_PROGRAM))
        self.assertAlmostEqual(value["base_intercept_ns"], 20_000_000, delta=100_000)
        self.assertAlmostEqual(value["base_slope_ns_per_call"], 1_000_000, delta=100_000)
        self.assertAlmostEqual(value["proof_intercept_bytes"], 50_000, delta=300)
        self.assertAlmostEqual(value["proof_slope_bytes_per_call"], 10_000, delta=300)
        self.assertEqual(value["proof_calibration_rank_1_based"],
                         math.ceil((4 * model.CAL_ROWS_PER_PROGRAM + 1) * .9))
        predicted = model.prediction(value, 5)
        quantiles = predicted["warm_wall_quantile_ns"]
        self.assertLess(quantiles["0.05"], quantiles["0.5"])
        self.assertLess(quantiles["0.5"], quantiles["0.95"])
        for probability in model.TARGET_QUANTILES:
            at = quantiles[str(probability)]
            self.assertAlmostEqual(model.wall_cdf(value, 5, at), probability, places=10)
        self.assertLess(predicted["proof_bytes_interval"][0],
                        predicted["proof_bytes_center"])
        self.assertGreater(predicted["proof_bytes_interval"][1],
                           predicted["proof_bytes_center"])

    def test_equal_scale_limit_and_invalid_rows(self) -> None:
        self.assertAlmostEqual(model._pow_sum_cdf(20.0, 10.0, 10.0),
                               1 - 3 * math.exp(-2))
        with self.assertRaises(ValueError):
            model.fit(rows(model.FIT_ROWS_PER_PROGRAM)[:-1],
                      rows(model.CAL_ROWS_PER_PROGRAM))


if __name__ == "__main__":
    unittest.main()
