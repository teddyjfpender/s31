"""Static V7 source disjointness, semantics, and startup gate controls."""

import json
import hashlib
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "benchmarks"))
sys.path.insert(0, str(S31 / "benchmarks" / "cost"))
sys.path.insert(0, str(S31 / "python"))

import v7_protocol as v7
from oracle import evaluate_relation
from package.context import lower_text
import whole_prover_predictor_v7 as predictor
from whole_prover_predictor_v7 import process_stage_gate


class CostV7ProtocolTests(unittest.TestCase):
    def test_complete_tool_pin_includes_transitive_predictor_and_oracles(self):
        names = {path.name for path in v7.tool_paths()}
        self.assertTrue({"v7_protocol.py", "benchmark_whole_prover_cost_v7.py",
                         "whole_prover_predictor_v7.py", "publish_whole_prover_cost_v7.py",
                         "arithmetic_rss_predictor_v2.py", "oracle.py",
                         "poseidon2_oracle.py"} <= names)
        self.assertEqual(len(v7.tool_paths()), len(set(v7.tool_paths())))
        self.assertEqual(len(v7.tool_digest(v7.tool_paths())), 64)

    def test_both_splits_are_disjoint_and_examples_match_independent_oracle(self):
        with tempfile.TemporaryDirectory() as directory:
            inventory = v7.inventory(Path(directory), {
                "samples_per_program": v7.SAMPLES, "splits": v7.SPLITS,
            })
            self.assertEqual({split: len(items) for split, items in inventory.items()},
                             {"train": 20, "validation": 20})
            source_hashes = [item["source_sha256"] for items in inventory.values()
                             for item in items.values()]
            assignment_hashes = [digest for items in inventory.values()
                                 for item in items.values()
                                 for digest in item["assignment_sha256"]]
            self.assertEqual(len(source_hashes), len(set(source_hashes)))
            self.assertEqual(len(assignment_hashes), 4_000)
            self.assertEqual(len(assignment_hashes), len(set(assignment_hashes)))
            for split, items in inventory.items():
                self.assertEqual({family: sum(row["family"] == family
                                              for row in items.values()) for family in
                                  ("arithmetic", "chip", "hash", "fixed_width")},
                                 {family: 5 for family in
                                  ("arithmetic", "chip", "hash", "fixed_width")})
                for name in items:
                    source = next(path for path in (
                        Path(directory) / split / "generated-sources" / f"{name}.s31",
                        Path(directory) / split / "generated-sources" / f"{name}.s31.json")
                                  if path.exists())
                    relation = (lower_text(source)[0] if source.suffix == ".s31" else
                                json.loads(source.read_bytes()))
                    assignment = json.loads((Path(directory) / split / name /
                                             "assignments" / "00.json").read_bytes())
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"], name)

    def test_historical_overlap_is_rejected_before_native_work(self):
        with tempfile.TemporaryDirectory() as directory:
            sample = v7.workloads("train", Path(directory) / "sample", v7.SAMPLES,
                                  v7.SPLITS["train"])[0]
            duplicated = v7.s31.file_hash(sample["source"])
            with patch.object(v7, "historical_digests", return_value=({duplicated}, set())):
                with self.assertRaisesRegex(ValueError, "source overlaps"):
                    v7.inventory(Path(directory) / "study", {
                        "samples_per_program": v7.SAMPLES, "splits": v7.SPLITS,
                    })

    def test_process_stage_gate_catches_transfer_sized_startup_miss(self):
        okay = {name: {"relative_mean_error": .10,
                       "absolute_mean_error_seconds": .005} for name in
                ("prover_process_unattributed_seconds",
                 "native_verify_process_wall_seconds")}
        self.assertTrue(process_stage_gate(okay, v7.GATES))
        missed = {name: dict(values) for name, values in okay.items()}
        missed["native_verify_process_wall_seconds"] = {
            "relative_mean_error": .40, "absolute_mean_error_seconds": .033,
        }
        self.assertFalse(process_stage_gate(missed, v7.GATES))

    def test_validation_requires_full_committed_model_identity(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(ValueError, "canonical model artifact"):
                v7.require_model(Path(directory) / "unfrozen.json", "0" * 64,
                                 "1" * 40, "2" * 64, "3" * 40)

    def test_fitted_model_rejects_program_specific_verifier_startup_miss(self):
        def digest(value):
            return hashlib.sha256(value.encode()).hexdigest()

        def specimen(split, names, protocol):
            cases = {}
            for size in names:
                name = f"arithmetic_{size}"
                source_sha = digest(f"{split}/{name}/source")
                assignments = [digest(f"{split}/{name}/{i}") for i in range(100)]
                protocol["inventory"][split][name] = {
                    "family": "arithmetic", "lowering": "direct-gate",
                    "source_sha256": source_sha, "assignment_sha256": assignments,
                }
                trials = []
                for _ in range(100):
                    trials.append({
                        "native_verifier_accepted": True,
                        "changed_public_statement_rejected": "public_outputs.result[0]",
                        "independent_value_oracle": {"status": "passed"},
                        "prove_seconds": .055,
                        "verify_seconds": .030,
                        "prover_stages": {
                            "witness_seconds": .005, "setup_seconds": .005,
                            "prove_seconds": .030, "prove_excluding_pow_seconds": .020,
                            "interaction_pow_seconds": .005, "fri_pow_seconds": .005,
                            "runtime_other_seconds": .005,
                            "total_through_verification_seconds": .045,
                        },
                        "proof_bytes": 1000 + size * 10,
                        "prover_peak_rss_bytes": 10_000_000 + size * 1_000,
                    })
                cases[name] = {
                    "family": "arithmetic", "source_sha256": source_sha,
                    "assignment_sha256": assignments,
                    "lowering": "direct-gate", "profile": "direct-m31-v4",
                    "visible_fri": v7.VISIBLE_FRI,
                    "package_build": {"package_build_wall_seconds": 1.0,
                                      "package_reused": False},
                    "chip_manifest_binding": None,
                    "raw": {"qm31_ops": size}, "padded": {"qm31_ops": size},
                    "preprocessed_cells": 8 * size, "trials": trials,
                    "compiler_sha256": "a" * 64,
                }
            return cases

        with tempfile.TemporaryDirectory() as directory:
            protocol = {
                "schema": v7.SCHEMA, "profiles": {"arithmetic": "direct-gate"},
                "profile_by_family": {"arithmetic": "direct-m31-v4"},
                "visible_fri": v7.VISIBLE_FRI, "pow_bits_required": 26,
                "samples_per_program": 100, "accuracy_gate": v7.GATES,
                "stage_features": {
                    "runtime_witness_seconds": "raw_rows",
                    "runtime_setup_seconds": "preprocessed_cells",
                    "runtime_prove_excluding_pow_seconds": "raw_rows",
                    "runtime_interaction_pow_seconds": "constant",
                    "runtime_fri_pow_seconds": "constant",
                    "runtime_runtime_other_seconds": "padded_rows",
                    "prover_process_unattributed_seconds": "constant",
                    "native_verify_process_wall_seconds": "padded_rows",
                    "proof_bytes": "padded_rows",
                    "prover_peak_rss_bytes": "padded_rows",
                },
                "splits": {split: {"arithmetic_rounds": sizes, "chip_rounds": [],
                                   "hash_depths": [], "signed_widths": []}
                           for split, sizes in (("train", [16, 32, 64, 128, 256]),
                                                ("validation", [24, 48, 96, 192, 384]))},
                "inventory": {"train": {}, "validation": {}},
                "selection_policy": "disabled",
            }
            train_cases = specimen("train", protocol["splits"]["train"]["arithmetic_rounds"],
                                   protocol)
            validation_cases = specimen(
                "validation", protocol["splits"]["validation"]["arithmetic_rounds"], protocol)
            protocol_path = Path(directory) / "protocol.json"
            protocol_path.write_text(json.dumps(protocol, sort_keys=True))
            protocol_sha = v7.sha(protocol_path.read_bytes())
            common = {"measurement_tool_sha256": "b" * 64,
                      "protocol_sha256": protocol_sha, "host": {"test": "same-host"},
                      "samples_per_program": 100}
            train = {**common, "schema": predictor.CORPUS_SCHEMA, "split": "train",
                     "cases": train_cases}
            validation = {**common, "schema": predictor.CORPUS_SCHEMA,
                          "split": "validation", "cases": validation_cases}
            with patch.object(predictor, "PROTOCOL", protocol_path):
                model = predictor.fit_model(train, protocol)
                clean = predictor.evaluate(model, validation, protocol)
                self.assertTrue(all(row["process_stage_gate_pass"]
                                    for row in clean["programs"]))
                validation_cases["arithmetic_96"]["trials"] = [
                    {**trial, "verify_seconds": .063}
                    for trial in validation_cases["arithmetic_96"]["trials"]]
                missed = predictor.evaluate(model, validation, protocol)
                self.assertFalse(missed["local_accuracy_gate_pass"])
                self.assertFalse(next(row for row in missed["programs"]
                                      if row["program"] == "arithmetic_96")
                                 ["process_stage_gate_pass"])


if __name__ == "__main__":
    unittest.main()
