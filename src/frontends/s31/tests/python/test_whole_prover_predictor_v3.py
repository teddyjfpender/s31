"""Prospective v3 split, chip-manifest gate and PoW uncertainty checks."""

import hashlib
import json
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch

S31_ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(S31_ROOT / "benchmarks"), str(S31_ROOT / "python")]

from benchmark_whole_prover_cost_v3 import host_identity, workload_cases
from publish_whole_prover_cost_v3 import publish
from whole_prover_predictor_v3 import PROTOCOL, evaluate, fit_model
sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_publish_stage_aware_cost_v1 import materialize_corpus, write_json


def digest(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()


def synthetic_corpus(split: str, protocol: dict) -> dict:
    spec = protocol["splits"][split]
    names = ([(f"arithmetic_{r}", "arithmetic", r) for r in spec["arithmetic_rounds"]] +
             [(f"chip_{r}", "chip", r) for r in spec["chip_rounds"]] +
             [(f"hash_{d}", "hash", 128 * d) for d in spec["hash_depths"]] +
             [(f"signed_{'quotient' if split == 'validation' else 'div_rem'}_{w}",
               "fixed_width", w * 16) for w in spec["signed_widths"]])
    cases = {}
    for name, family, scale in names:
        padded = 512 if family == "chip" else 1 << (scale - 1).bit_length()
        chip_cells = 10240 + 17 * scale if family == "chip" else 0
        chip_domain = max(512, scale) if family == "chip" else 0
        trials = []
        for index in range(protocol["samples_per_program"]):
            pow_factor = 0.1 + index / 10
            witness = .0001 * (chip_cells / 10000 if family == "chip" else scale)
            setup = .001 if family == "chip" else .0002 * padded
            non_pow = .0003 * (chip_cells / 10000 if family == "chip" else scale)
            interaction = (.001 if family == "chip" else .00004 * padded) * pow_factor
            fri = (.02 if family == "chip" else .0006 * padded) * pow_factor
            opaque = non_pow + interaction + fri
            other = .001 if family == "chip" else .00001 * padded
            stages = {"witness_seconds": witness, "setup_seconds": setup,
                      "prove_seconds": opaque, "runtime_other_seconds": other,
                      "total_through_verification_seconds": witness + setup + opaque + other}
            if family != "hash":
                stages.update({"prove_excluding_pow_seconds": non_pow,
                               "interaction_pow_seconds": interaction,
                               "fri_pow_seconds": fri})
            trials.append({
                "native_verifier_accepted": True,
                "changed_public_statement_rejected": "public_outputs.result[0]",
                "independent_value_oracle": {"status": "passed"},
                "prover_stages": stages,
                "prove_seconds": stages["total_through_verification_seconds"] +
                                 (.001 if family == "chip" else .00005 * scale),
                "verify_seconds": .005 * chip_domain / 512 if family == "chip" else .0002 * padded,
                "proof_bytes": 60000 * chip_domain // 512 if family == "chip" else 200 * padded,
                "prover_peak_rss_bytes": (8_000_000 + 1300 * padded if family == "arithmetic"
                                          else 8_000_000 + 100 * chip_cells if family == "chip"
                                          else 100_000 * padded),
            })
        cases[name] = {
            "family": family, "source_sha256": digest(f"source:{split}:{name}"),
            "compiler_sha256": "c" * 64, "lowering": protocol["profiles"][family],
            "profile": f"synthetic-{family}", "visible_fri": {"pow_bits": 26},
            "raw": {"blake_g" if family == "hash" else "qm31_ops": 292 if family == "chip" else scale},
            "padded": {"blake_g" if family == "hash" else "qm31_ops": padded},
            "preprocessed_cells": 8 * padded,
            "package_build": {"package_build_wall_seconds": 1.0, "package_reused": False},
            "chip_manifest_binding": ({"schema": "s31-component-manifest-direct-chip-v2",
                                       "chip_call": {"call_id": 0, "rounds": scale},
                                       "component_geometry": [
                                           {"name": "qm31_ops", "trace_log_size": 9,
                                            "base_trace_columns": 12, "interaction_trace_columns": 8},
                                           {"name": "repeated_step_chip", "trace_log_size": scale.bit_length() - 1,
                                            "base_trace_columns": 9, "interaction_trace_columns": 8}],
                                       "chip_trace_cells": chip_cells,
                                       "chip_fri_domain_rows": chip_domain,
                                       "manifest_precommitment_sha256": digest(f"pre:{name}"),
                                       "component_manifest_sha256": digest(f"manifest:{name}")}
                                      if family == "chip" else None),
            "assignment_sha256": [digest(f"assignment:{split}:{name}:{i}")
                                  for i in range(protocol["samples_per_program"])],
            "trials": trials,
        }
    return {"schema": "s31-whole-prover-cost-corpus-v3.1", "split": split,
            "protocol_sha256": hashlib.sha256(PROTOCOL.read_bytes()).hexdigest(),
            "samples_per_program": protocol["samples_per_program"],
            "host": {"machine": "synthetic"}, "compiler_sha256": "c" * 64,
            "cases": cases}


class WholeProverV3Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.protocol = json.loads(PROTOCOL.read_text())

    def test_host_identity_is_stable_and_pseudonymous(self) -> None:
        from platform import node
        identity = host_identity()
        self.assertEqual(identity, host_identity())
        self.assertEqual(identity["host_id_sha256"], hashlib.sha256(node().encode()).hexdigest())
        self.assertNotIn(node(), json.dumps(identity))
        self.assertTrue(identity["cpu_model"])

    def test_new_split_and_independent_oracles(self) -> None:
        from package.context import lower_text
        from oracle import evaluate_relation
        with TemporaryDirectory() as directory:
            train = workload_cases("train", Path(directory) / "train", 20, self.protocol)
            validation = workload_cases("validation", Path(directory) / "validation", 20, self.protocol)
            self.assertEqual((len(train), len(validation)), (18, 16))
            self.assertFalse({item["name"] for item in train} &
                             {item["name"] for item in validation})
            self.assertEqual(sum(item["family"] == "chip" for item in train + validation), 9)
            for item in train + validation:
                source = item["source"]
                relation = lower_text(source)[0] if source.suffix == ".s31" else json.loads(source.read_text())
                for assignment in item["assignments"]:
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"])

    def test_affine_rss_and_pow_variance_are_predeclared(self) -> None:
        train = synthetic_corpus("train", self.protocol)
        validation = synthetic_corpus("validation", self.protocol)
        model = fit_model(train, self.protocol)
        self.assertEqual(model["families"]["arithmetic"]["stages"]["prover_peak_rss_bytes"]["fit_kind"],
                         "positive_affine_rss")
        self.assertIn("stochastic_trial_ratio_max",
                      model["families"]["chip"]["stages"]["runtime_fri_pow_seconds"])
        self.assertNotIn("runtime_fri_pow_seconds", model["families"]["hash"]["stages"])
        result = evaluate(model, validation, self.protocol)
        self.assertTrue(result["local_accuracy_gate_pass"])
        self.assertFalse(result["automatic_lowering_selection_enabled"])
        self.assertEqual(len(result["programs"]), 16)
        self.assertGreater(result["programs"][0]["stages"]["runtime_fri_pow_seconds"]
                           ["coefficient_of_variation"], 0)

    def test_rejects_manifest_leakage_and_failed_controls(self) -> None:
        train = synthetic_corpus("train", self.protocol)
        model = fit_model(train, self.protocol)
        validation = synthetic_corpus("validation", self.protocol)
        validation["cases"]["chip_32"]["chip_manifest_binding"] = None
        with self.assertRaisesRegex(ValueError, "chip manifest"):
            evaluate(model, validation, self.protocol)
        validation = synthetic_corpus("validation", self.protocol)
        validation["cases"]["chip_32"]["source_sha256"] = model["training_source_sha256"][0]
        with self.assertRaisesRegex(ValueError, "source leaked"):
            evaluate(model, validation, self.protocol)
        validation = synthetic_corpus("validation", self.protocol)
        validation["cases"]["chip_32"]["trials"][0]["changed_public_statement_rejected"] = "false"
        with self.assertRaisesRegex(ValueError, "changed-claim control"):
            evaluate(model, validation, self.protocol)
        validation = synthetic_corpus("validation", self.protocol)
        for trial in validation["cases"]["chip_32"]["trials"]:
            trial["prover_peak_rss_bytes"] *= 100
        self.assertFalse(evaluate(model, validation, self.protocol)["local_accuracy_gate_pass"])

    def test_publisher_replays_frozen_model_and_binds_chip_inventory(self) -> None:
        with TemporaryDirectory() as directory:
            root = Path(directory)
            train = synthetic_corpus("train", self.protocol)
            train_path = materialize_corpus(root / "train", train)
            model = fit_model(train, self.protocol)
            model["training_corpus_sha256"] = hashlib.sha256(train_path.read_bytes()).hexdigest()
            model_path = root / "model.json"
            write_json(model_path, model)
            validation = synthetic_corpus("validation", self.protocol)
            validation["frozen_model_sha256"] = hashlib.sha256(model_path.read_bytes()).hexdigest()
            validation_path = materialize_corpus(root / "validation", validation)
            evaluation = evaluate(model, validation, self.protocol)
            evaluation["frozen_model_sha256"] = hashlib.sha256(model_path.read_bytes()).hexdigest()
            evaluation["validation_corpus_sha256"] = hashlib.sha256(validation_path.read_bytes()).hexdigest()
            evaluation_path = root / "evaluation.json"
            write_json(evaluation_path, evaluation)

            def binding(package: Path) -> dict:
                split = package.parent.parent.name
                name = package.parent.name
                return {"train": train, "validation": validation}[split]["cases"][name]["chip_manifest_binding"]

            with patch("publish_whole_prover_cost_v3.s31.verify_package",
                       return_value={"compiler_sha256": "c" * 64}), patch(
                           "publish_whole_prover_cost_v3.chip_manifest_binding", side_effect=binding):
                report = publish(train_path, model_path, validation_path, evaluation_path)
            self.assertEqual(report["training_controls"]["saved_proof_digest_matched"], 360)
            self.assertEqual(report["validation_controls"]["saved_proof_digest_matched"], 320)
            self.assertEqual(report["program_inventory"]["validation"]["chip_32"]
                             ["chip_manifest_binding"], binding(root / "validation/chip_32/package"))
            self.assertFalse(report["automatic_lowering_selection_enabled"])


if __name__ == "__main__":
    unittest.main()
