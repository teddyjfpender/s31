"""Fast preparation checks for coherent false one-call chip keys.

The native acceptance case then checks these keys against the source-derived
verifier. These tests keep the negative control from regressing to a stale
precommitment or circuit hash that would fail for an unrelated reason.
"""

from __future__ import annotations

import copy
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "tests" / "acceptance"))

from acceptance_component_manifest_chip import (  # noqa: E402
    bound_circuit_hash, reseal_false_manifest,
)
from package.manifest_digest import direct_chip_v2_digest  # noqa: E402


def fixture_key() -> dict:
    def component(name: str, index: int) -> dict:
        return {
            "name": name, "source_index": 1 if index == 0 else 0,
            "proof_index": index, "trace_log_size": 7,
            "evaluation_log_size": 8, "base_trace_columns": 4,
            "interaction_trace_columns": 2, "n_constraints": 3,
            "random_coefficient_offset": index * 3,
            "trace_spans": [], "preprocessed_indices": [],
            "program_binding_sha256": f"{index + 1:02x}" * 32,
            "claimed_sum_index": index, "main_trace_span": None,
            "interaction_trace_span": None,
            "max_constraint_log_degree_bound": 8,
            "lookup_relation_ids": [index + 1],
        }

    boundary = {"input": [1, 2, 3, 4], "output": [5, 6, 7, 8]}
    manifest = {
        "schema": "s31-component-manifest-direct-chip-v2",
        "profile": "direct-m31-private-v5",
        "program_sha256": "11" * 32,
        "canonical_ir_sha256": "22" * 32,
        "air_bundle_sha256": "33" * 32,
        "preprocessed_root": "44" * 32,
        "circuit_hash": "00" * 32,
        "composition_plan_hash": 17,
        "claimed_sums": 3,
        "components": [component(name, index) for index, name in enumerate((
            "qm31_ops", "repeated_step_chip", "private_boundary_bridge"))],
        "preprocessed_columns": [{"id": "fixed", "commitment_index": 0,
                                  "log_size": 7, "rows": 128,
                                  "values_sha256": "55" * 32}],
        "chip_call": {"call_id": 0, "relation_id": 9, "rounds": 16,
                      "constant": 13, "private_boundary": boundary},
    }
    key = {
        "program_sha256": manifest["program_sha256"],
        "preprocessed_root": manifest["preprocessed_root"],
        "trace_log_size": 7,
        "chip": {"relation_id": 9, "rounds": 16, "constant": 13},
        "private_boundary": copy.deepcopy(boundary),
        "component_manifest": manifest,
    }
    key["manifest_precommitment_sha256"] = direct_chip_v2_digest(manifest)
    key["circuit_hash"] = bound_circuit_hash(key)
    manifest["circuit_hash"] = key["circuit_hash"]
    return key


class ChipResealPreparationTest(unittest.TestCase):
    def check_reseal(self, mutate) -> None:
        honest = fixture_key()
        forged = reseal_false_manifest(honest, mutate)
        self.assertNotEqual(forged["manifest_precommitment_sha256"],
                            honest["manifest_precommitment_sha256"])
        self.assertNotEqual(forged["circuit_hash"], honest["circuit_hash"])
        self.assertEqual(forged["manifest_precommitment_sha256"],
                         direct_chip_v2_digest(forged["component_manifest"]))
        self.assertEqual(forged["circuit_hash"], bound_circuit_hash(forged))
        self.assertEqual(forged["component_manifest"]["circuit_hash"],
                         forged["circuit_hash"])
        self.assertEqual(honest, fixture_key())

    def test_bridge_program_binding_resealed(self) -> None:
        self.check_reseal(lambda m: m["components"][2].__setitem__(
            "program_binding_sha256", "00" * 32))

    def test_private_output_address_resealed(self) -> None:
        self.check_reseal(lambda m: m["chip_call"]["private_boundary"]["output"]
                          .__setitem__(0, 99))

    def test_fixed_column_values_resealed(self) -> None:
        self.check_reseal(lambda m: m["preprocessed_columns"][0].__setitem__(
            "values_sha256", "00" * 32))


if __name__ == "__main__":
    unittest.main()
