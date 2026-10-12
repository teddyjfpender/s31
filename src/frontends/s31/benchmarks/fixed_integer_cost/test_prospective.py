"""Native-free tests for frozen split, stage accounting, and honest scoring."""

from __future__ import annotations

import copy
import tempfile
import unittest
from pathlib import Path

from prospective import check_plan, plan, validate
from prospective_model import (CALIBRATION_WIDTH, FIT_WIDTHS, HOLDOUT_WIDTH,
                               LOWERINGS, OPS, fit, score, stage_trial)


def sample(operation: str, lowering: str, width: int, scale: float = 1.0) -> dict:
    rows = width * (5 if operation == "mul" else 2)
    padded = 1 << (rows - 1).bit_length()
    geometry = {"raw": {"qm31_ops": rows},
                "padded": {"qm31_ops": padded},
                "preprocessed_cells": padded * 8,
                "visible_fri": {"pow_bits": 12}}
    trials = []
    for index in range(8):
        stages = {"witness": .001 * width * scale,
                  "setup": .002 * width * scale,
                  "prove_non_pow": .004 * width * scale,
                  "interaction_pow": .001 + index * .0001,
                  "fri_pow": .002 + index * .0001,
                  "runtime_other": .001, "process_residual": .003,
                  "verify": .005 * width * scale}
        trials.append({"stages": stages, "whole": sum(stages.values()),
                       "proof_bytes": 1000 + padded * 9 * scale,
                       "prover_rss": 1_000_000 + padded * 80 * scale})
    return {"operation": operation, "lowering": lowering, "width": width,
            "source_sha256": f"{operation}-{width}",
            "geometry": geometry, "build_seconds": width * .01 * scale,
            "trials": trials}


class ProspectiveModelTests(unittest.TestCase):
    def training(self) -> list[dict]:
        return [sample(op, lowering, width)
                for op in OPS for lowering in LOWERINGS
                for width in (*FIT_WIDTHS, CALIBRATION_WIDTH)]

    def test_fit_excludes_holdout_and_scores_all_four_profiles(self) -> None:
        model = fit(self.training())
        self.assertEqual(model["holdout_width"], 128)
        self.assertEqual(set(model["groups"]),
                         {f"{op}/{lowering}" for op in OPS for lowering in LOWERINGS})
        holdout = [sample(op, lowering, HOLDOUT_WIDTH)
                   for op in OPS for lowering in LOWERINGS]
        scored = score(model, holdout)
        self.assertEqual(len(scored["cases"]), 4)
        self.assertTrue(scored["local_diagnostic_gate_pass"])
        for row in scored["cases"].values():
            self.assertAlmostEqual(sum(row["predicted_stages"].values()),
                                   row["targets"]["whole"]["predicted_center"])

    def test_training_roster_and_holdout_contamination_rejected(self) -> None:
        training = self.training()
        with self.assertRaisesRegex(ValueError, "exact"):
            fit(training[:-1])
        model = fit(training)
        holdout = [sample(op, lowering, HOLDOUT_WIDTH)
                   for op in OPS for lowering in LOWERINGS]
        holdout[0]["source_sha256"] = model["groups"][
            f"{holdout[0]['operation']}/{holdout[0]['lowering']}"]["fit_source_sha256"][0]
        with self.assertRaisesRegex(ValueError, "training"):
            score(model, holdout)

    def test_stage_error_and_missed_cost_gate_remain_visible(self) -> None:
        model = fit(self.training())
        holdout = [sample(op, lowering, HOLDOUT_WIDTH, scale=8)
                   for op in OPS for lowering in LOWERINGS]
        scored = score(model, holdout)
        self.assertFalse(scored["local_diagnostic_gate_pass"])
        self.assertFalse(scored["gates"]["whole_program_median_p90_error_max"])
        bad = copy.deepcopy(holdout[0]["trials"][0])
        bad["stages"]["setup"] = -1
        with self.assertRaisesRegex(ValueError, "negative"):
            stage_trial(bad)
        bad = copy.deepcopy(holdout[0]["trials"][0])
        bad["whole"] += .1
        with self.assertRaisesRegex(ValueError, "account"):
            stage_trial(bad)


class ProspectivePlanTests(unittest.TestCase):
    def test_plan_validates_and_detects_source_mutation(self) -> None:
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            frozen = plan(root)
            self.assertEqual(len(frozen["cases"]), 8)
            self.assertEqual(set(validate(root)["cases"].values()), {"pending"})
            source = root / "inputs" / "add-u128" / "u128_checked_add.s31"
            source.write_text(source.read_text() + "\n")
            with self.assertRaisesRegex(ValueError, "source"):
                check_plan(root)


if __name__ == "__main__":
    unittest.main()
