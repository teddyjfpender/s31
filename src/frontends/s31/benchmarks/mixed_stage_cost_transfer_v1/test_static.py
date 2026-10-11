"""Native-free transfer source and freeze safety checks."""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import cohort
import protocol
import score
import study
from cohort import COUNTS, SHAPES, case, design, inventory, output_words, sha, source, trial_order


class TransferDesignTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.cfg = design()

    def test_all_shapes_have_distinct_sources_and_disjoint_evidence(self) -> None:
        rows = inventory(self.cfg)
        self.assertEqual(len(rows), 12)
        self.assertEqual({row["shape"] for row in rows.values()}, set(SHAPES))
        self.assertEqual({row["call_count"] for row in rows.values()}, set(COUNTS))
        self.assertEqual(len({row["source_sha256"] for row in rows.values()}), 12)
        self.assertEqual(len({value for row in rows.values()
                              for value in row["assignment_sha256"]}), 360)
        self.assertEqual(len({value for row in rows.values()
                              for value in row["typed_statement_sha256"]}), 360)

    def test_shape_changes_actual_operations_and_rounds(self) -> None:
        for count in COUNTS:
            sources = {shape: json.loads(source(shape, count, self.cfg))
                       for shape in SHAPES}
            self.assertEqual(sum(node["op"] == "repeat" for node in
                                 sources["fork"]["nodes"]), count)
            self.assertEqual(sum(node["op"] == "mul_const" for node in
                                 sources["feeder"]["nodes"]), count)
            self.assertEqual({node["rounds"] for node in
                              sources["deep32"]["nodes"] if node["op"] == "repeat"},
                             {32})
            self.assertNotEqual([node["op"] for node in sources["control"]["nodes"]],
                                [node["op"] for node in sources["feeder"]["nodes"]])
            self.assertEqual(len({sha(source(shape, count, self.cfg))
                                  for shape in SHAPES}), 4)

    def test_hand_oracle_rejects_wrong_output(self) -> None:
        for shape in SHAPES:
            _, assignment_bytes, statement = case(shape, 2, 0, self.cfg)
            assignment = json.loads(assignment_bytes)
            words = next(iter(assignment["public_inputs"].values()))
            self.assertEqual(next(iter(assignment["public_outputs"].values())),
                             output_words(shape, 2, words))
            self.assertEqual(json.loads(statement)["version"], 2)
        with patch.object(cohort, "output_words", return_value=[0, 0, 0, 0]):
            with self.assertRaisesRegex(ValueError, "does not match computed"):
                case("feeder", 2, 0, self.cfg)

    def test_rejects_leaked_prior_source_or_assignment(self) -> None:
        old = {kind: set() for kind in ("source", "assignment", "typed_statement")}
        old["source"].add(sha(source("fork", 2, self.cfg)))
        with patch.object(cohort, "reference_inventory", return_value=({}, old)):
            with self.assertRaisesRegex(ValueError, "source reused"):
                inventory(self.cfg)
        old["source"].clear()
        old["assignment"].add(sha(case("fork", 2, 0, self.cfg)[1]))
        with patch.object(cohort, "reference_inventory", return_value=({}, old)):
            with self.assertRaisesRegex(ValueError, "assignment reused"):
                inventory(self.cfg)

    def test_materialization_is_native_free_and_never_overwrites(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            target = Path(temporary) / "cohort"
            result = cohort.materialize(target, self.cfg)
            self.assertEqual((result["programs"], result["assignments"]), (12, 360))
            for name, row in inventory(self.cfg).items():
                directory = target / name
                self.assertEqual(sha((directory / "source.s31.json").read_bytes()),
                                 row["source_sha256"])
                self.assertEqual(sha((directory / "assignment-00.json").read_bytes()),
                                 row["assignment_sha256"][0])
                self.assertEqual(sha((directory / "statement-00.json").read_bytes()),
                                 row["typed_statement_sha256"][0])
            with self.assertRaisesRegex(ValueError, "fresh materialization"):
                cohort.materialize(target, self.cfg)

    def test_predeclared_schedule_interleaves_all_programs(self) -> None:
        expected = {f"{shape}_n{count}" for shape in SHAPES for count in COUNTS}
        for index in range(self.cfg["assignments_per_program"]):
            self.assertEqual(set(trial_order(index, self.cfg)), expected)
        self.assertNotEqual(trial_order(0, self.cfg), trial_order(1, self.cfg))

    def test_mutated_gate_or_reference_hash_is_rejected(self) -> None:
        changed = copy.deepcopy(self.cfg)
        changed["diagnostic_gates"]["transfer_wall_program_median_p90_relative_error_max"] = 1
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "design.json"
            path.write_text(json.dumps(changed))
            with patch.object(cohort, "DESIGN_PATH", path):
                with self.assertRaisesRegex(ValueError, "prospective roster"):
                    design()
            reference = Path(temporary) / "old.json"
            reference.write_text("{}")
            with patch.object(cohort, "REFERENCE_PATH", reference):
                with self.assertRaisesRegex(ValueError, "reference protocol changed"):
                    cohort.reference_inventory(self.cfg)

    def test_draft_refuses_uncommitted_design_or_existing_protocol(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            missing = Path(temporary) / "missing-protocol.json"
            with patch.object(protocol, "PROTOCOL", missing), \
                    patch.object(protocol, "clean_stack", side_effect=ValueError("uncommitted")):
                with self.assertRaisesRegex(ValueError, "uncommitted"):
                    protocol.draft()
            candidate = Path(temporary) / "protocol.json"
            candidate.write_text("{}")
            with patch.object(protocol, "PROTOCOL", candidate):
                with self.assertRaisesRegex(ValueError, "already exists"):
                    protocol.draft()

    def test_raw_phase_root_catches_mutation_and_ignores_derived_reports(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            out = Path(temporary)
            (out / "proof.bin").write_bytes(b"native proof")
            first = study.raw_root(out, "a" * 64)
            (out / "audit.json").write_text("{}")
            (out / "evaluation.json").write_text("{}")
            self.assertEqual(study.raw_root(out, "a" * 64), first)
            (out / "proof.bin").write_bytes(b"mutated proof")
            self.assertNotEqual(study.raw_root(out, "a" * 64), first)
            (out / "link").symlink_to(out / "proof.bin")
            with self.assertRaisesRegex(ValueError, "symlinks"):
                study.raw_root(out, "a" * 64)

    def test_changed_record_claim_mutates_exactly_one_public_leaf(self) -> None:
        statement = case("feeder", 2, 0, self.cfg)[2]
        original = json.loads(statement)
        for leaf in (0, 1):
            changed = json.loads(study.changed_claim(statement, leaf))
            self.assertEqual(changed["abi_sha256"], original["abi_sha256"])
            self.assertNotEqual(changed["leaves"][leaf]["words"][0],
                                original["leaves"][leaf]["words"][0])
            self.assertEqual(changed["leaves"][1 - leaf], original["leaves"][1 - leaf])

    def test_frozen_call_count_fit_exposes_round_depth_failure(self) -> None:
        features = {name: ("constant" if name in
                           ("prover_process_residual_ns",
                            "external_verifier_process_wall_ns") else "call_count")
                    for name in (*score.STAGES, "proof_bytes")}
        model = {"schema": "s31-mixed-stage-cost-v1-model",
                 "protocol_sha256": self.cfg["reference_protocol_sha256"],
                 "engine_gitlink_commit": "e" * 40,
                 "compiler_sha256": "c" * 64,
                 "automatic_lowering_selection_enabled": False,
                 "features": features,
                 "fits": {name: {"kind": kind,
                                  "intercept": 12.5 if name in score.STAGES else 100.0,
                                  "slope": 0.0} for name, kind in features.items()},
                 "predictive_ratio_bands": {name: {"lower_ratio": .9,
                                                    "upper_ratio": 1.1}
                                            for name in score.TARGETS}}
        roster = inventory(self.cfg)
        protocol_value = {"inventory_sha256": sha(cohort.canonical(roster)),
                          "host": {"test": True}, "compiler_sha256": "d" * 64,
                          "engine_gitlink_commit": "e" * 40}
        records = [{"name": name, "shape": row["shape"],
                    "call_count": row["call_count"],
                    "source_sha256": row["source_sha256"],
                    "build_wall_ns": 10_000,
                    "trials": [{"first_verified_process_wall_ns": 100,
                                "proof_bytes": 100}
                               for _ in range(30)]}
                   for name, row in roster.items()]
        corpus = {"schema": "s31-mixed-stage-cost-transfer-v1-audited-corpus",
                  "protocol_sha256": sha(cohort.canonical(protocol_value)),
                  "inventory_sha256": protocol_value["inventory_sha256"],
                  "host": protocol_value["host"],
                  "compiler_sha256": protocol_value["compiler_sha256"],
                  "engine_gitlink_commit": protocol_value["engine_gitlink_commit"],
                  "phase_root_sha256": "r" * 64, "records": records}
        passing = score.evaluate(model, corpus, protocol_value)
        self.assertTrue(passing["cross_shape_diagnostic_gate_pass"])
        self.assertFalse(passing["same_compiler_revision"])
        changed = copy.deepcopy(corpus)
        for record in changed["records"]:
            if record["shape"] == "deep32":
                for trial in record["trials"]:
                    trial["proof_bytes"] = 200
        failing = score.evaluate(model, changed, protocol_value)
        self.assertFalse(failing["cross_shape_diagnostic_gate_pass"])
        self.assertFalse(failing["gate_pass"][
            "transfer_proof_program_median_p90_relative_error"])


if __name__ == "__main__":
    unittest.main()
