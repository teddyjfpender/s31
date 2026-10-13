"""Adversarial controls for the relation-pruning soundness boundary."""

from __future__ import annotations

import copy
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from language.prune_certificate import PruneCertificateError, verify_pruning
from text_frontend import _certified_prune


def relation() -> dict:
    return {
        "version": 1, "name": "p",
        "inputs": [{"name": "x", "kind": "m31", "length": 1, "visibility": "private"}],
        "nodes": [
            {"name": "dead", "op": "mul", "lhs": "x", "rhs": "x"},
            {"name": "live", "op": "add", "lhs": "x", "rhs": "x"},
            {"name": "partial", "op": "inv", "lhs": "x"},
        ],
        "assertions": [], "public_outputs": ["live"],
    }


class PruneCertificateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.before = relation()
        self.after = copy.deepcopy(self.before)
        self.after["nodes"] = self.after["nodes"][1:]
        self.before_map = {name: {"line": line, "column": 1}
                           for line, name in enumerate(("dead", "live", "partial"), 1)}
        self.after_map = {name: span for name, span in self.before_map.items() if name != "dead"}

    def check_rejects(self, message: str, after: dict, after_map: dict | None = None) -> None:
        with self.assertRaisesRegex(PruneCertificateError, message):
            verify_pruning(self.before, self.before_map, after,
                           self.after_map if after_map is None else after_map)

    def test_total_dead_node_can_be_removed_but_partial_node_remains(self) -> None:
        self.assertEqual(verify_pruning(self.before, self.before_map,
                                        self.after, self.after_map), ("dead",))

    def test_changed_live_arithmetic_is_not_pruning(self) -> None:
        after = copy.deepcopy(self.after)
        after["nodes"][0]["rhs"] = "partial"
        self.check_rejects("exact proper subsequence", after)

    def test_partial_operation_cannot_be_removed(self) -> None:
        after = copy.deepcopy(self.after)
        after["nodes"] = after["nodes"][:1]
        self.check_rejects("non-total", after)

    def test_public_observation_cannot_be_removed(self) -> None:
        after = copy.deepcopy(self.before)
        after["nodes"] = [after["nodes"][0], after["nodes"][2]]
        self.check_rejects("public, assertion, or ABI root", after)

    def test_assertion_operand_cannot_be_removed(self) -> None:
        self.before["assertions"] = [{"lhs": "dead", "rhs": "x"}]
        self.after["assertions"] = copy.deepcopy(self.before["assertions"])
        self.check_rejects("public, assertion, or ABI root", self.after)

    def test_retained_node_cannot_read_removed_dependency(self) -> None:
        self.before["nodes"][1]["lhs"] = "dead"
        self.after["nodes"][0]["lhs"] = "dead"
        self.check_rejects("missing dependency", self.after)

    def test_public_abi_leaf_is_an_observable_root(self) -> None:
        self.before["version"] = 2
        self.before["public_abi"] = {
            "inputs": [{"leaves": [{"wire": "dead"}]}],
            "result": {"leaves": [{"wire": "live"}]},
        }
        self.after["version"] = 2
        self.after["public_abi"] = copy.deepcopy(self.before["public_abi"])
        self.check_rejects("public, assertion, or ABI root", self.after)

    def test_source_locations_must_follow_retained_nodes(self) -> None:
        self.check_rejects("source locations", self.after, self.before_map)

    def test_unknown_metadata_cannot_be_pruned_across(self) -> None:
        self.before["nodes"][1]["future_wire"] = "dead"
        self.after["nodes"][0]["future_wire"] = "dead"
        self.check_rejects("unreviewed node shape", self.after)

    def test_unchanged_future_relation_is_safe_to_keep(self) -> None:
        self.before["future_field"] = {"unknown": "wire"}
        self.assertEqual(verify_pruning(self.before, self.before_map,
                                        self.before, self.before_map), ())

    def test_in_place_optimizer_rewrite_cannot_erase_its_own_evidence(self) -> None:
        def corrupt(relation: dict, locations: dict) -> tuple[dict, dict]:
            relation["nodes"][1]["op"] = "mul"
            return relation, locations

        with patch("text_frontend.prune_total_dead_nodes", side_effect=corrupt):
            with self.assertRaises(PruneCertificateError):
                _certified_prune(self.before, self.before_map)


if __name__ == "__main__":
    unittest.main()
