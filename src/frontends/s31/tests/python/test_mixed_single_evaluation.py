"""Guard the mixed prover against repeating its full source interpreter pass."""

from pathlib import Path
import re
import unittest


ROOT = Path(__file__).resolve().parents[2]
RUNTIME = ROOT / "runtime" / "mixed_boundary"


class MixedSingleEvaluationTests(unittest.TestCase):
    def test_cli_projects_claim_and_package_evaluates_once(self):
        cli = (RUNTIME / "general_prover_main.zig").read_text()
        package = (RUNTIME / "general_package.zig").read_text().split(
            '\ntest "mixed general sealed native proofs', 1
        )[0]
        evaluator_calls = re.compile(r"\brelation\.evaluate\s*\(")
        claim_calls = re.compile(r"\brelation\.claimedWords\s*\(")

        self.assertEqual(evaluator_calls.findall(cli), [])
        self.assertEqual(len(claim_calls.findall(cli)), 1)
        # Proving evaluates once; the separate optional verifier trace audit
        # evaluates its supplied witness once more for an independent check.
        prover = package.split("pub fn proveSealedAndInspectWithTiming(", 1)[1].split(
            "\npub fn verifyEmbedded(", 1
        )[0]
        verifier = package.split("\nfn verifySourceBoundWithWitness(", 1)[1]
        self.assertEqual(len(evaluator_calls.findall(prover)), 1)
        self.assertEqual(len(evaluator_calls.findall(verifier)), 1)
        self.assertEqual(len(evaluator_calls.findall(package)), 2)
        self.assertIn("try publicValues(words)", package)
        self.assertIn("proof.output_values", package)
        self.assertIn("InvalidMixedPublicStatement", package)


if __name__ == "__main__":
    unittest.main()
