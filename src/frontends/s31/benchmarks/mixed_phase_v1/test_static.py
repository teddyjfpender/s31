"""Native-free checks for the paired mixed phase protocol and accounting."""

from __future__ import annotations

import unittest
import json

from subprocess import CompletedProcess
from study import LANGUAGE

from study import (ASSIGNMENTS, COUNTS, case, changed_result, phase_check,
                   proof_layer_rejection, sha, statement_words)


class PhaseStudyTests(unittest.TestCase):
    def test_fresh_claims_are_distinct_and_public_mutation_changes_bytes(self) -> None:
        assignments, statements = set(), set()
        for count in COUNTS:
            source_hashes = set()
            for index in range(ASSIGNMENTS):
                source, assignment, statement = case(count, index)
                source_hashes.add(sha(source))
                assignments.add(sha(assignment))
                statements.add(sha(statement))
                changed = changed_result(source, statement)
                self.assertNotEqual(statement, changed)
                self.assertEqual(statement_words(source, statement)[:4],
                                 statement_words(source, changed)[:4])
            self.assertEqual(len(source_hashes), 1)
        self.assertEqual(len(assignments), 60)
        self.assertEqual(len(statements), 60)
        old = json.loads((LANGUAGE / "mixed-stage-cost-v1-protocol.json").read_bytes())
        prior = {digest for split in old["inventory"].values() for row in split.values()
                 for field in ("assignment_sha256", "typed_statement_sha256")
                 for digest in row[field]}
        self.assertFalse((assignments | statements) & prior)

    def test_rejection_must_reach_proof_binding(self) -> None:
        self.assertTrue(proof_layer_rejection(CompletedProcess([], 1, b"",
            b"error: InvalidMixedInteractionNonce\n")))
        self.assertFalse(proof_layer_rejection(CompletedProcess([], 1, b"",
            b"error: InvalidRecordStatement\n")))
        self.assertFalse(proof_layer_rejection(CompletedProcess([], 1, b"",
            b"error: InvalidMixedPublicStatement\n")))
        self.assertFalse(proof_layer_rejection(CompletedProcess([], 0, b"", b"")))

    def test_phase_accounting_rejects_wrong_identity_and_overflow(self) -> None:
        parts = {"profile_rebuild_ns": 2, "semantic_evaluation_ns": 3,
                 "topology_compile_ns": 4, "witness_compile_ns": 5,
                 "native_prove_including_setup_ns": 100,
                 "envelope_and_serialization_ns": 6, "package_total_ns": 120}
        stage = {"schema": "s31-mixed-general-prover-stages-v1",
                 "source_sha256": "a" * 64, "circuit_identity_sha256": "b" * 64,
                 "stages_ns": parts}
        phase = {"schema": "s31-mixed-native-phase-v1",
                 "source_sha256": "a" * 64, "circuit_identity_sha256": "b" * 64,
                 "native_prove_including_setup_ns": 100, "prove_body_ns": 80,
                 "interaction_pow_ns": 10, "pcs_prove_ns": 50, "fri_pow_ns": 20,
                 "pcs_without_fri_pow_ns": 30, "native_without_reported_pow_ns": 70}
        self.assertEqual(phase_check(stage, phase, 130)["fri_pow_ns"], 20)
        phase["circuit_identity_sha256"] = "c" * 64
        with self.assertRaisesRegex(ValueError, "identity"):
            phase_check(stage, phase, 130)
        phase["circuit_identity_sha256"] = "b" * 64
        phase["fri_pow_ns"] = 95
        with self.assertRaisesRegex(ValueError, "accounting"):
            phase_check(stage, phase, 130)


if __name__ == "__main__":
    unittest.main()
