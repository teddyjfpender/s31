"""Mutation controls for the DEEP quotient arithmetic source contract."""

import unittest
from pathlib import Path

from scripts.s31_formal_lib.pcs_fri_quotient_algebra import check_sources


ROOT = Path(__file__).resolve().parents[2]
CORE = ROOT / "deps/stwo-zig/src/core"


@unittest.skipUnless((CORE / "pcs/quotients/row_evaluation.zig").is_file(),
                     "engine submodule not checked out")
class QuotientAlgebraSourceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = [
            (CORE / name).read_text() for name in (
                "constraints.zig", "pcs/quotients/row_evaluation.zig",
                "pcs/quotients/fri_answers.zig", "fields/mod.zig",
                "fields/cm31.zig")
        ]

    def test_pinned_native_formula(self):
        check_sources(*self.sources)

    def test_wrong_line_denominator_inverse_or_contribution_rejects(self):
        mutations = (
            (0, "const b = value.mul(c).sub(a.mul(point.y));",
             "const b = value.mul(c).add(a.mul(point.y));"),
            (1, "denominators[i] = prx.sub(domain_x).mul(piy).sub(pry.sub(domain_y).mul(pix));",
             "denominators[i] = prx.sub(domain_x).mul(piy).add(pry.sub(domain_y).mul(pix));"),
            (1, "fields.batchInverseInPlace(CM31, values, out) catch return error.DivisionByZero;",
             "fields.batchInverseInPlace(CM31, values, out) catch {};"),
            (1, "const numerator = numerator_sum.sub(linear_term.evalAt(domain_y));",
             "const numerator = numerator_sum.add(linear_term.evalAt(domain_y));"),
            (1, "return self.sum_a.mulM31(domain_y).add(self.sum_b);",
             "return self.sum_a.mulM31(domain_y).sub(self.sum_b);"),
            (1, "sample_data.random_coeff,", "QM31.one(),"),
            (2, ".value_coeff = line_coeffs[coeff_idx].c,",
             ".value_coeff = line_coeffs[coeff_idx].b,"),
            (2, "base_value.mul(contribution.value_coeff),",
             "base_value.add(contribution.value_coeff),"),
            (3, "try batchInverseClassic(cm31.CM31, &tail_products, &tail_inverses);",
             "batchInverseClassic(cm31.CM31, &tail_products, &tail_inverses) catch {};"),
            (4, "if (self.isZero()) return Error.DivisionByZero;",
             "if (self.isZero()) return CM31.zero();"),
        )
        for index, old, new in mutations:
            with self.subTest(index=index, old=old):
                sources = self.sources.copy()
                self.assertIn(old, sources[index])
                sources[index] = sources[index].replace(old, new, 1)
                with self.assertRaises(ValueError):
                    check_sources(*sources)


if __name__ == "__main__":
    unittest.main()
