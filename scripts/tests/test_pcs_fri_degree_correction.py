"""Mutation and gate controls for the pinned P05 protocol classification."""

from __future__ import annotations

import contextlib
import io
import unittest
from unittest.mock import patch

from scripts.release import pcs_fri_degree_correction as p05
from scripts.release import pcs_fri_v01_blockers as blockers


class DegreeCorrectionTests(unittest.TestCase):
    def test_pinned_quotient_only_path_is_not_the_published_ensemble(self) -> None:
        report = p05.audit()
        self.assertEqual(report["engine_gitlink_commit"], p05.ENGINE_GITLINK)
        self.assertEqual(report["source_sha256"], p05.SOURCE_SHA256)
        self.assertEqual(report["native_batch_fri_input"],
                         "one_accumulated_deep_quotient_word")
        self.assertFalse(report["native_nonquotient_degree_test_identified"])
        self.assertFalse(report["published_degree_corrected_nonquotient_premise_met"])
        self.assertFalse(report["p05_discharged"])
        self.assertEqual(
            [event["event"] for event in report["native_gate_epoch_trace"]],
            [name for name, _ in p05.GATE_EVENTS + p05.STARK_EVENTS + p05.PCS_EVENTS],
        )
        proposed = report["proposed_degree_corrected_profile"]
        self.assertFalse(proposed["selector_installed"])
        self.assertFalse(proposed["proof_admissible"])
        self.assertEqual(proposed["required_commitment_order"],
                         ["fixed", "main", "interaction", "composition"])
        self.assertEqual(proposed["requirements"]["original_word_degree_test"],
                         "absent_from_native_fri_input")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(p05.main(["--require-p05"]), 2)
        matrix = blockers.matrix()
        self.assertEqual(matrix["degree_correction"], report)
        self.assertFalse(matrix["proven_release_admissible"])

    def test_engine_or_source_mutation_requires_review(self) -> None:
        sources = {name: (p05.ROOT / name).read_bytes()
                   for name in p05.SOURCE_SHA256}
        with self.assertRaisesRegex(ValueError, "gitlink changed"):
            p05.classify(sources, "0" * 40)
        with self.assertRaisesRegex(ValueError, "roster changed"):
            p05.classify({p05.PROVER: sources[p05.PROVER]}, p05.ENGINE_GITLINK)
        for name in sources:
            with self.subTest(name=name):
                changed = dict(sources)
                changed[name] += b"\n// semantic review required\n"
                with self.assertRaisesRegex(ValueError, "source changed"):
                    p05.classify(changed, p05.ENGINE_GITLINK)

    def test_epoch_extractor_rejects_reordering_and_missing_composition(self) -> None:
        sources = {name: (p05.ROOT / name).read_bytes()
                   for name in p05.SOURCE_SHA256}
        gate = sources[p05.S31_GATE_VERIFIER].decode()
        first = p05.GATE_EVENTS[3][1]
        second = p05.GATE_EVENTS[4][1]
        prefix, body = gate.split("fn verifyDirectProfile(", 1)
        changed = dict(sources)
        changed[p05.S31_GATE_VERIFIER] = (prefix + "fn verifyDirectProfile(" +
            body.replace(first, "REORDER_HERE", 1).replace(
                second, first, 1).replace("REORDER_HERE", second, 1)).encode()
        with self.assertRaisesRegex(ValueError, "event reordered"):
            p05.native_gate_epoch_trace(changed)

        stark = sources[p05.STARK_VERIFIER].decode()
        changed = dict(sources)
        changed[p05.STARK_VERIFIER] = stark.replace(p05.STARK_EVENTS[1][1],
                                                  "composition commit removed", 1).encode()
        with self.assertRaisesRegex(ValueError, "event missing"):
            p05.native_gate_epoch_trace(changed)

    def test_release_matrix_rejects_unreviewed_positive_claim(self) -> None:
        forged = p05.audit()
        forged["p05_discharged"] = True
        with patch.object(blockers, "audit_degree_correction", return_value=forged):
            with self.assertRaisesRegex(ValueError, "theorem status changed"):
                blockers.matrix()
        forged = p05.audit()
        forged["proposed_degree_corrected_profile"]["proof_admissible"] = True
        with patch.object(blockers, "audit_degree_correction", return_value=forged):
            with self.assertRaisesRegex(ValueError, "theorem status changed"):
                blockers.matrix()


if __name__ == "__main__":
    unittest.main()
