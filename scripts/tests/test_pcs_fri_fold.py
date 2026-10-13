"""Mutation controls for the pinned FRI fold source contract."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_fold import check_sources


ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT / "deps/stwo-zig/src/core"


class FoldSourceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fft = (CORE / "fft.zig").read_text()
        cls.folding = (CORE / "fri/folding.zig").read_text()
        cls.fri = (CORE / "fri.zig").read_text()

    def test_pinned_source(self) -> None:
        check_sources(self.fft, self.folding, self.fri)

    def test_mutations_are_rejected(self) -> None:
        mutations = (
            ("fft", "subF(F, tmp, v1.*)", "addF(F, tmp, v1.*)"),
            ("folding", "domain.coset(), .x", "domain.coset(), .y"),
            ("folding", "current_alpha = current_alpha.square();",
             "current_alpha = alpha;"),
            ("folding", "const alpha_sq = alpha.square();",
             "const alpha_sq = alpha;"),
            ("folding", "src_domain.half_coset, .y", "src_domain.half_coset, .x"),
            ("folding", "fold_alpha.square(),", "fold_alpha,"),
            ("folding", "folded_values[i] = f0.add(alpha.mul(f1));",
             "folded_values[i] = f1.add(alpha.mul(f0));"),
            ("fri", "first_layer_sparse_eval.foldCircleSubsets(",
             "first_layer_sparse_eval.foldLineSubsetsN("),
            ("fri", "rebuilt.sparse_evaluation.foldLineSubsetsN(",
             "rebuilt.sparse_evaluation.foldCircleSubsets("),
        )
        for name, old, new in mutations:
            with self.subTest(name=name, old=old):
                sources = {"fft": self.fft, "folding": self.folding, "fri": self.fri}
                self.assertIn(old, sources[name])
                sources[name] = sources[name].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    check_sources(sources["fft"], sources["folding"], sources["fri"])


if __name__ == "__main__":
    unittest.main()
