"""Mutation controls for the raw-slot FRI capture source anchors."""
from pathlib import Path
import unittest

from scripts.s31_formal_lib.pcs_fri_raw_refinement import check_sources


ROOT = Path(__file__).resolve().parents[2]
FRI = (ROOT / "deps/stwo-zig/src/core/fri.zig").read_text()
AUDIT = (ROOT / "formal/s31/tests/pcs_fri_raw_refinement_native.zig").read_text()


class RawRefinementSourceControls(unittest.TestCase):
    def test_pinned_sources(self) -> None:
        check_sources(FRI, AUDIT)

    def test_refinement_bypasses_are_rejected(self) -> None:
        mutations = (
            ("fri", "if (!std.mem.eql(usize, positions, sampled))", "if (false)"),
            ("fri", "layer_query_evals = folded.evals;", "layer_query_evals = layer_query_evals;"),
            ("fri", "sparse.subset_evals[subset_index],", "sparse.subset_evals[0],"),
            ("fri", "query,\n                    self.last_layer_domain.logSize(),",
             "query,\n                    0,"),
            ("fri", "const expected = try self.last_layer_poly.evalAtPoint(allocator, QM31.fromBase(x));",
             "const expected = QM31.zero();"),
            ("fri", "if (!query_eval.eql(expected)) {", "if (false) {"),
            ("audit", "if (!left.eql(right)) return error.InconsistentGroup;", "if (false) return error.InconsistentGroup;"),
            ("audit", "if (!subset[position % width].eql(current)) return error.BadCurrentValue;",
             "if (false) return error.BadCurrentValue;"),
            ("audit", "if (!current.eql(expected)) return error.BadTerminalValue;",
             "if (false) return error.BadTerminalValue;"),
        )
        for name, before, after in mutations:
            with self.subTest(name=name, before=before):
                source = FRI if name == "fri" else AUDIT
                self.assertEqual(source.count(before), 1)
                changed = source.replace(before, after, 1)
                with self.assertRaises(ValueError):
                    check_sources(changed, AUDIT) if name == "fri" else check_sources(FRI, changed)


if __name__ == "__main__":
    unittest.main()
