"""Static V8r1 prospective design: freshness, semantics, and freeze guards."""

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "benchmarks"))
sys.path.insert(0, str(S31 / "benchmarks" / "cost"))
sys.path.insert(0, str(S31 / "python"))

import v8r1_design as v8r1
from oracle import evaluate_relation
from package.context import lower_text


class CostV8r1DesignTests(unittest.TestCase):
    def test_design_is_prefreeze_and_never_exposes_native_entrypoint(self):
        design = v8r1.read_design()
        self.assertEqual(design["status"], "designed-not-frozen-no-native-observations")
        self.assertTrue(all(value is None for value in design["prefreeze_pins"].values()))
        self.assertFalse(design["automatic_lowering_selection_enabled"])
        self.assertEqual(design["rss_uncertainty"]["fixed_absolute_floor_bytes"], 2 * 1024**2)
        self.assertEqual(design["predictive_accuracy_gate"], v8r1.v7.GATES)
        self.assertEqual(design["paired_mixed_vs_generic"]["status"],
                         "blocked-until-general-mixed-profile-admitted-and-packaged")

    def test_mutated_pin_gate_or_split_is_rejected(self):
        design = v8r1.read_design()
        changes = (
            ("prefreeze_pins", "compiler_sha256", "0" * 64),
            ("predictive_accuracy_gate", "per_program_rss_trial_interval_coverage_min", 0),
            ("splits", "validation", {**design["splits"]["validation"],
                                      "chip_rounds": design["splits"]["train"]["chip_rounds"]}),
            ("paired_mixed_vs_generic", "status", "admitted"),
        )
        for section, key, value in changes:
            with self.subTest(section=section, key=key):
                changed = copy.deepcopy(design)
                changed[section][key] = value
                with self.assertRaises(ValueError):
                    v8r1.validate_design(changed)

    def test_full_inventory_is_fresh_and_small_examples_match_oracle(self):
        design = v8r1.read_design()
        with tempfile.TemporaryDirectory(prefix="s31-v8r1-design-") as directory:
            root = Path(directory)
            inventory = v8r1.inventory(root, design)
            self.assertEqual({split: len(rows) for split, rows in inventory.items()},
                             {"train": 23, "validation": 20})
            self.assertEqual({family: sum(item["family"] == family
                                          for item in inventory["train"].values())
                              for family in v8r1.FAMILIES},
                             {"arithmetic": 6, "chip": 6, "hash": 6, "fixed_width": 5})
            source_hashes = [item["source_sha256"] for rows in inventory.values()
                             for item in rows.values()]
            assignment_hashes = [digest for rows in inventory.values()
                                 for item in rows.values()
                                 for digest in item["assignment_sha256"]]
            self.assertEqual(len(source_hashes), len(set(source_hashes)))
            self.assertEqual(len(assignment_hashes), 4300)
            self.assertEqual(len(assignment_hashes), len(set(assignment_hashes)))
            self.assertEqual(len(v8r1.inventory_sha256(inventory)), 64)
            for split, names in (("train", ("arithmetic_16", "chip_16", "hash_2", "signed_div_rem_8")),
                                 ("validation", ("arithmetic_32", "chip_128", "hash_4", "signed_div_rem_8"))):
                for name in names:
                    source = next(path for path in (
                        root / split / "generated-sources" / f"{name}.s31",
                        root / split / "generated-sources" / f"{name}.s31.json") if path.exists())
                    relation = (lower_text(source)[0] if source.suffix == ".s31" else
                                json.loads(source.read_bytes()))
                    assignment = json.loads((root / split / name / "assignments" / "00.json").read_bytes())
                    self.assertEqual(evaluate_relation(relation, assignment),
                                     assignment["public_outputs"], (split, name))

    def test_historical_source_overlap_fails_before_any_native_work(self):
        design = v8r1.read_design()
        with tempfile.TemporaryDirectory(prefix="s31-v8r1-overlap-") as directory:
            sample = v8r1.workloads("train", Path(directory) / "probe", design)[0]
            old_source = v8r1.s31.file_hash(sample["source"])
            with patch.object(v8r1, "historical_digests", return_value=({old_source}, set())):
                with self.assertRaisesRegex(ValueError, "source overlap"):
                    v8r1.inventory(Path(directory) / "inventory", design)

    def test_historical_assignment_overlap_fails_before_any_native_work(self):
        design = v8r1.read_design()
        with tempfile.TemporaryDirectory(prefix="s31-v8r1-overlap-") as directory:
            sample = v8r1.workloads("train", Path(directory) / "probe", design)[0]
            assignment = Path(directory) / "first-assignment.json"
            v8r1.s31.write_json(assignment, sample["assignments"][0])
            old_assignment = v8r1.s31.assignment_digest(assignment)
            with patch.object(v8r1, "historical_digests", return_value=(set(), {old_assignment})):
                with self.assertRaisesRegex(ValueError, "assignment overlap"):
                    v8r1.inventory(Path(directory) / "inventory", design)


if __name__ == "__main__":
    unittest.main()
