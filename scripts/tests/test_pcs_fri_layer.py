"""Mutation controls for the pinned FRI acceptance chain."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_layer import check_sources


CORE = Path(__file__).resolve().parents[2] / "deps/stwo-zig/src/core"


class LayerSourceControls(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.fri = (CORE / "fri.zig").read_text()
        cls.folding = (CORE / "fri/folding.zig").read_text()
        cls.line = (CORE / "poly/line.zig").read_text()

    def test_pinned_source(self) -> None:
        check_sources(self.fri, self.folding, self.line)

    def test_mutations_are_rejected(self) -> None:
        mutations = (
            ("fri", "if (rebuilt.consumed_witness != self.proof.fri_witness.len)",
             "if (false)"),
            ("fri", "layer_query_evals = folded.evals;", "layer_query_evals = layer_query_evals;"),
            ("fri", "var folded_queries = try queries.fold(allocator, self.fold_step);",
             "var folded_queries = queries;"),
            ("fri", "if (!query_eval.eql(expected))", "if (false)"),
            ("fri", "if (last_layer_poly.len() > (@as(usize, 1) << @intCast(config.log_last_layer_degree_bound)))",
             "if (false)"),
            ("folding", "subset[subset_pos] = query_evals[subset_query_idx];",
             "subset[subset_pos] = witness_evals[witness_idx];"),
            ("folding", "subset[subset_pos] = witness_evals[witness_idx];",
             "subset[subset_pos] = query_evals[subset_query_idx];"),
            ("line", "return poly_utils.fold(QM31, self.coeffs, doublings_stack[0..self.log_size]);",
             "return QM31.zero();"),
        )
        for name, old, new in mutations:
            with self.subTest(name=name, old=old):
                sources = {"fri": self.fri, "folding": self.folding, "line": self.line}
                self.assertIn(old, sources[name])
                sources[name] = sources[name].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    check_sources(sources["fri"], sources["folding"], sources["line"])


if __name__ == "__main__":
    unittest.main()
