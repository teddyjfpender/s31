"""Keep generated measurements inside the independently checked fragment."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(Path(__file__).resolve().parent), str(S31 / "python")]

from measure import P, assignment_for, output_for, source_for
from oracle import evaluate_relation
from package.correspondence import parse_source
from text_frontend import compile_text


class DirectGateReleaseCostSourceTests(unittest.TestCase):
    def test_every_size_has_exact_checked_gates_and_field_semantics(self) -> None:
        for gates in range(1, 17):
            with self.subTest(gates=gates):
                source = source_for(gates)
                produced, _ = compile_text(source)
                independently_checked, syntax = parse_source(source.encode())
                self.assertEqual(produced, independently_checked)
                self.assertEqual(len(syntax["instructions"]), gates)
                for sample in (0, 1, 2):
                    assignment = assignment_for(gates, sample)
                    self.assertEqual(evaluate_relation(produced, assignment),
                                     assignment["public_outputs"])
                near_boundary = [P - 2, P - 1, 0, 1]
                assignment = {"public_inputs": {"x": near_boundary},
                              "private_inputs": {},
                              "public_outputs": {f"p{gates}":
                                                 output_for(gates, near_boundary)}}
                self.assertEqual(evaluate_relation(produced, assignment),
                                 assignment["public_outputs"])


if __name__ == "__main__":
    unittest.main()
