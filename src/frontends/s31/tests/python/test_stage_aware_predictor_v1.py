"""Prospective model split, stage accounting, and leakage controls."""

import copy
import hashlib
import json
import sys
import unittest
from pathlib import Path

S31_ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31_ROOT / "benchmarks"))
from benchmark_whole_prover_stage_v1 import quotient_source, signed_assignment, signed_words, workload_cases
from stage_aware_predictor_v1 import PROTOCOL, evaluate, fit_model, predict_case


def digest(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def synthetic_corpus(split: str, protocol: dict) -> dict:
    spec = protocol["splits"][split]
    names = ([(f"arithmetic_{rounds}", "arithmetic", rounds) for rounds in spec["arithmetic_rounds"]] +
             [(f"hash_{depth}", "hash", 128 * depth) for depth in spec["hash_depths"]] +
             [(f"signed_{'quotient' if split == 'validation' else 'div_rem'}_{width}",
               "fixed_width", width * 16) for width in spec["signed_widths"]])
    cases = {}
    for name, family, scale in names:
        trials = []
        for index in range(protocol["samples_per_program"]):
            factor = 0.5 + (index % 5) * 0.25
            witness = .0001 * scale
            setup = .0002 * scale
            non_pow = .0003 * scale
            interaction = .00004 * scale * factor
            fri = .0006 * scale * factor
            opaque = non_pow + interaction + fri
            runtime_other = .00001 * scale
            native_total = witness + setup + opaque + runtime_other
            stages = {"witness_seconds": witness, "setup_seconds": setup,
                      "prove_seconds": opaque, "runtime_other_seconds": runtime_other,
                      "total_through_verification_seconds": native_total}
            if family != "hash":
                stages.update({"prove_excluding_pow_seconds": non_pow,
                               "interaction_pow_seconds": interaction,
                               "fri_pow_seconds": fri})
            trials.append({
                "native_verifier_accepted": True,
                "changed_public_statement_rejected": "public_outputs.result[0]",
                "independent_value_oracle": {"status": "passed"},
                "prover_stages": stages,
                "prove_seconds": native_total + .00005 * scale,
                "verify_seconds": .0002 * scale,
                "proof_bytes": 200 * scale,
                "prover_peak_rss_bytes": 100_000 * scale,
            })
        cases[name] = {
            "family": family, "source_sha256": digest(f"{split}:{name}"),
            "compiler_sha256": "c" * 64,
            "lowering": protocol["profiles"][family],
            "profile": "synthetic-hash" if family == "hash" else "synthetic-direct",
            "visible_fri": {"pow_bits": 26},
            "raw": {"blake_g" if family == "hash" else "qm31_ops": scale},
            "padded": {"blake_g" if family == "hash" else "qm31_ops": 2 * scale},
            "preprocessed_cells": 16 * scale,
            "package_build": {"package_build_wall_seconds": 1.0,
                              "package_reused": False,
                              "zig_compiler_cache": "synthetic"},
            "assignment_sha256": [digest(f"{split}:{name}:{i}")
                                  for i in range(protocol["samples_per_program"])],
            "trials": trials,
        }
    return {
        "schema": "s31-stage-aware-cost-corpus-v1", "split": split,
        "protocol_sha256": hashlib.sha256(PROTOCOL.read_bytes()).hexdigest(),
        "samples_per_program": protocol["samples_per_program"],
        "host": {"machine": "synthetic"}, "cases": cases,
    }


class StageAwareModelTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.protocol = json.loads(PROTOCOL.read_text())

    def test_stage_fit_and_new_program_evaluation(self) -> None:
        train = synthetic_corpus("train", self.protocol)
        validation = synthetic_corpus("validation", self.protocol)
        model = fit_model(train, self.protocol)
        self.assertEqual(len(model["training_source_sha256"]), 13)
        self.assertIn("runtime_fri_pow_seconds", model["families"]["arithmetic"]["stages"])
        self.assertNotIn("runtime_fri_pow_seconds", model["families"]["hash"]["stages"])
        result = evaluate(model, validation, self.protocol)
        self.assertEqual(len(result["programs"]), 12)
        self.assertTrue(result["local_accuracy_gate_pass"])
        self.assertFalse(result["automatic_lowering_selection_enabled"])
        first = result["programs"][0]
        interval = first["targets"]["paired_prove_and_verify_wall_seconds"]["predicted"]
        self.assertLess(interval["lower"], interval["center"])
        self.assertGreater(interval["upper"], interval["center"])

    def test_rejects_cross_split_source_assignment_and_policy_leakage(self) -> None:
        train = synthetic_corpus("train", self.protocol)
        validation = synthetic_corpus("validation", self.protocol)
        model = fit_model(train, self.protocol)
        first = next(iter(validation["cases"].values()))
        first["source_sha256"] = model["training_source_sha256"][0]
        with self.assertRaisesRegex(ValueError, "source leaked"):
            evaluate(model, validation, self.protocol)
        first["source_sha256"] = digest("restored")
        first["assignment_sha256"][0] = model["training_assignment_sha256"][0]
        with self.assertRaisesRegex(ValueError, "assignment leaked"):
            evaluate(model, validation, self.protocol)
        first["assignment_sha256"][0] = digest("restored-assignment")
        first["visible_fri"] = {"pow_bits": 27}
        with self.assertRaisesRegex(ValueError, "mixed visible_fri|profile/FRI policy changed"):
            evaluate(model, validation, self.protocol)
        first["visible_fri"] = {"pow_bits": 26}
        first["trials"][0]["changed_public_statement_rejected"] = "false"
        with self.assertRaisesRegex(ValueError, "changed-claim control"):
            evaluate(model, validation, self.protocol)

    def test_generator_has_disjoint_programs_and_signed_oracle_values(self) -> None:
        from tempfile import TemporaryDirectory
        with TemporaryDirectory() as directory:
            root = Path(directory)
            train = workload_cases("train", root / "train", 3, self.protocol)
            validation = workload_cases("validation", root / "validation", 3, self.protocol)
            self.assertFalse({case["name"] for case in train} &
                             {case["name"] for case in validation})
            sys.path.insert(0, str(S31_ROOT / "python"))
            from package.context import lower_text
            from oracle import evaluate_relation
            for case in validation:
                if case["source"].suffix == ".json":
                    relation = json.loads(case["source"].read_text())
                else:
                    relation, _, _ = lower_text(case["source"])
                for assignment in case["assignments"]:
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"])
                if case["family"] == "fixed_width":
                    self.assertEqual(set(case["assignments"][0]["public_outputs"]),
                                     set(relation["public_outputs"]))
        for width in (8, 16, 32, 64):
            assignment = signed_assignment(width, 50001, True)
            words = assignment["public_outputs"]["result"]
            self.assertEqual(len(words), (width + 15) // 16)
            self.assertEqual(signed_words(-2, width)[0], (1 << min(width, 16)) - 2)
            self.assertIn("let result = std::int::limbs(quotient);", quotient_source(width))
        with TemporaryDirectory() as directory:
            for width in (8, 16, 32, 64):
                source = Path(directory) / f"i{width}.s31"
                source.write_text(quotient_source(width))
                relation, _, _ = lower_text(source)
                self.assertEqual(len(relation["public_outputs"]), 1)
                output = relation["public_outputs"][0]
                self.assertEqual(len(signed_assignment(width, 50001, True, output)
                                     ["public_outputs"][output]), (width + 15) // 16)


if __name__ == "__main__":
    unittest.main()
