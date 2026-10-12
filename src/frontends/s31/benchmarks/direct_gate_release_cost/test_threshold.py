"""Check the threshold benchmark's equations before running native trials."""

from __future__ import annotations

import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(Path(__file__).resolve().parent), str(S31 / "python")]

from oracle import evaluate_relation
from package.correspondence import UnsupportedFragment, parse_source
from text_frontend import compile_text
from threshold import P, assignment, chain_source, linear_source


class AdditionChainThresholdTests(unittest.TestCase):
    def test_helper_erases_and_both_programs_compute_194x(self) -> None:
        functional, syntax = parse_source(chain_source(helper=True).encode())
        flat, flat_syntax = parse_source(chain_source(helper=False).encode())
        self.assertEqual((functional, syntax), (flat, flat_syntax))
        self.assertEqual(functional, compile_text(chain_source(helper=True))[0])
        self.assertEqual(len(syntax["instructions"]), 9)
        linear = compile_text(linear_source())[0]
        self.assertEqual(len(linear["nodes"]), 193)
        with self.assertRaises(UnsupportedFragment):
            parse_source(linear_source().encode())
        for sample in range(40):
            for relation, output_name in ((functional, "out"), (linear, "v193")):
                with self.subTest(sample=sample, output=output_name):
                    claim = assignment(sample, output_name)
                    self.assertEqual(evaluate_relation(relation, claim),
                                     claim["public_outputs"])
        self.assertEqual(assignment(0, "out")["public_outputs"]["out"],
                         [0, 194, P - 194, P - 388])


if __name__ == "__main__":
    unittest.main()
