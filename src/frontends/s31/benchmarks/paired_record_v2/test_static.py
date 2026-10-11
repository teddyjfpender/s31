"""Static admission checks; native acceptance runs only after exclusive slot release."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path

from design import case, design, inventory
from protocol import check
from runner import changed_claim, materialize, paired_summary, require_static_case


class PairedRecordDesign(unittest.TestCase):
    def test_all_source_assignment_statement_bytes_are_unique_and_balanced(self) -> None:
        cfg = design()
        frozen = inventory(cfg)
        self.assertEqual(set(frozen["train"]), {"1", "2", "4", "6"})
        self.assertEqual(set(frozen["heldout"]), {"3", "5", "7", "8"})
        sources = []
        assignments = []
        statements = []
        for split in frozen.values():
            for count, entry in split.items():
                sources.append(entry["source_sha256"])
                assignments.extend(entry["assignment_sha256"])
                statements.extend(entry["statement_sha256"])
                self.assertEqual(entry["order"].count("generic-first"), 50)
                self.assertEqual(entry["order"].count("mixed-first"), 50)
                self.assertEqual(len(entry["assignment_sha256"]), 100)
                self.assertEqual(len(entry["statement_sha256"]), 100)
        self.assertEqual(len(set(sources)), 8)
        self.assertEqual(len(set(assignments)), 800)
        self.assertEqual(len(set(statements)), 800)

    def test_typed_claims_and_evaluation_are_bound_to_each_pair(self) -> None:
        cfg = design()
        for count in range(1, 9):
            source_bytes, assignment_bytes, typed = case(count, 0, cfg)
            source = json.loads(source_bytes)
            assignment = json.loads(assignment_bytes)
            statement = json.loads(typed)
            self.assertEqual(source["version"], 2)
            self.assertEqual(len([node for node in source["nodes"]
                                  if node["op"] == "repeat"]), count)
            self.assertEqual(statement["leaves"][0]["words"],
                             next(iter(assignment["public_inputs"].values())))
            self.assertEqual(statement["leaves"][1]["words"],
                             next(iter(assignment["public_outputs"].values())))
            self.assertNotEqual(typed, changed_claim(typed, 0))
            self.assertNotEqual(typed, changed_claim(typed, 1))

    def test_saved_source_witness_or_claim_mutation_fails_static_replay(self) -> None:
        cfg = design()
        expected = inventory(cfg)["train"]["1"]
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "n1"
            materialize(directory, 1, cfg, expected)
            assignment = directory / "assignments/00.json"
            old = assignment.read_bytes()
            assignment.write_bytes(old + b" ")
            with self.assertRaises(ValueError):
                require_static_case(directory, 1, 0, cfg, expected)
            assignment.write_bytes(old)
            statement = directory / "statements/00.json"
            statement.write_bytes(changed_claim(statement.read_bytes(), 0))
            with self.assertRaises(ValueError):
                require_static_case(directory, 1, 0, cfg, expected)

    def test_unfrozen_design_cannot_authorize_native_runner(self) -> None:
        with self.assertRaisesRegex(ValueError, "externally recorded"):
            check("0" * 64, "short")

    def test_summary_uses_paired_assignment_unit(self) -> None:
        cfg = design()
        cfg["assignments_per_call_count"] = 4
        cfg["bootstrap_resamples"] = 100
        rows = []
        for index, ratio in enumerate((2.0, 2.0, 2.0, 2.0)):
            generic = {name: ratio for name in (
                "first_verified_wall_seconds", "prove_wall_seconds",
                "verify_wall_seconds", "proof_bytes", "prover_peak_rss_bytes")}
            mixed = {name: 1.0 for name in generic}
            rows.append({"index": index, "generic": generic, "mixed": mixed})
        summary = paired_summary({"split": "heldout", "cases": {"1": rows}}, cfg)
        self.assertEqual(summary["per_call_count"]["1"]["first_verified_wall_seconds"]
                         ["median_ratio_generic_over_mixed"], 2.0)


if __name__ == "__main__":
    unittest.main()
