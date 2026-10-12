"""Native-free checks of v3 claim identity, timing partitions and chronology."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import accounting
import study


def sample() -> tuple[dict, dict]:
    stages = {"profile_rebuild_ns": 2, "semantic_evaluation_ns": 3,
              "topology_compile_ns": 5, "witness_compile_ns": 7,
              "native_prove_including_setup_ns": 59,
              "envelope_and_serialization_ns": 11, "package_total_ns": 87}
    stage = {"schema": "s31-mixed-general-prover-stages-v1",
             "source_sha256": "a" * 64, "circuit_identity_sha256": "b" * 64,
             "stages_ns": stages}
    phase = {"schema": "s31-mixed-native-phase-v1",
             "source_sha256": "a" * 64, "circuit_identity_sha256": "b" * 64,
             "native_prove_including_setup_ns": 59, "prove_body_ns": 50,
             "interaction_pow_ns": 4, "pcs_prove_ns": 30, "fri_pow_ns": 6,
             "pcs_without_fri_pow_ns": 24, "native_without_reported_pow_ns": 49}
    return stage, phase


class CostV3Tests(unittest.TestCase):
    def test_disjoint_accounting_and_nested_mutations(self) -> None:
        stage, phase = sample()
        result = accounting.project(stage, phase, 100, 20)
        self.assertEqual(sum(result.values()), 120)
        self.assertEqual(result["prover_unattributed_process_wall_ns"], 13)
        self.assertEqual(result["native_outer_minus_body_ns"], 9)
        self.assertEqual(result["body_other_than_pow_or_pcs_ns"], 16)
        self.assertEqual(result["pcs_without_fri_pow_ns"], 24)
        self.assertEqual(result["fri_pow_ns"], 6)
        for field, bad in (("pcs_without_fri_pow_ns", 25),
                           ("native_without_reported_pow_ns", 48),
                           ("pcs_prove_ns", 48),
                           ("source_sha256", "c" * 64)):
            altered = dict(phase)
            altered[field] = bad
            with self.subTest(field=field), self.assertRaises(ValueError):
                accounting.project(stage, altered, 100, 20)
        with self.assertRaises(ValueError):
            accounting.project(stage, phase, 86, 20)

    def test_first_process_and_same_claim_repeat_are_explicit(self) -> None:
        base = {"prover_process_wall_ns": 100,
                "external_verifier_process_wall_ns": 20,
                "first_verified_process_wall_ns": 120,
                "prover_unattributed_process_wall_ns": 13,
                "native_prove_including_setup_ns": 59,
                "native_outer_minus_body_ns": 9, "interaction_pow_ns": 4,
                "pcs_without_fri_pow_ns": 24, "fri_pow_ns": 6}
        trials = [{**base, "ordinal": i, "claim_index": i // 2}
                  for i in range(4)]
        trials[0]["first_verified_process_wall_ns"] = 200
        result = accounting.cold_warm(trials)
        self.assertEqual(result["first_verified_process_wall_ns"],
                         {"first": 200, "same_claim_repeat": 120,
                          "warm_median": 120, "first_minus_same_claim_repeat": 80})
        trials[1]["claim_index"] = 1
        with self.assertRaises(ValueError):
            accounting.cold_warm(trials)

    def test_all_unique_claims_and_v2_independence(self) -> None:
        prospective = study.roster()
        self.assertEqual([len(group) for group in prospective.values()], [4, 4])
        train = prospective["train"]
        heldout = prospective["heldout"]
        self.assertFalse({row["source_sha256"] for row in train.values()} &
                         {row["source_sha256"] for row in heldout.values()})
        hashes = [item for group in prospective.values() for row in group.values()
                  for key in ("assignment_sha256", "statement_sha256") for item in row[key]]
        self.assertEqual(len(hashes), 8 * study.CLAIMS * 2)
        self.assertEqual(len(set(hashes)), len(hashes))

    def test_heldout_model_anchor_checked_before_raw_directory(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            out = Path(temp)
            with patch.object(study, "frozen", return_value=({"split": {}}, "p" * 64)), \
                    patch.object(study, "anchor_required",
                                 side_effect=ValueError("missing committed model")):
                with self.assertRaisesRegex(ValueError, "missing committed model"):
                    study.run("heldout", out, "m" * 64, "c" * 40)
            self.assertFalse((out / "heldout").exists())

    def test_fit_uses_only_warm_trials_and_exact_linear_proof_rule(self) -> None:
        records = []
        for index, count in enumerate((2, 6, 2, 6)):
            trials = [{"assignment_sha256": f"a{index}{i}",
                       "statement_sha256": f"s{index}{i}",
                       "first_verified_process_wall_ns":
                           100_000 if i == 0 else 1_000 + index * 100,
                       "proof_bytes": 1_000_000 if i == 0 else 100 + 10 * count}
                      for i in range(study.CLAIMS * study.REPEATS)]
            records.append({"call_count": count, "source_sha256": f"source{index}",
                            "trials": trials})
        model = study.model_from_training({"records": records}, "p" * 64, b"train\n")
        self.assertEqual(model["warm_wall_constant_ns"], 1_150)
        self.assertEqual(model["proof_intercept_bytes"], 100)
        self.assertEqual(model["proof_slope_bytes_per_call"], 10)
        self.assertEqual(study.prediction(model, 4),
                         {"warm_first_verified_wall_ns": 1_150,
                          "proof_bytes": 140})


if __name__ == "__main__":
    unittest.main()
