"""Fail-closed controls for the pinned OOD seed geometry diagnostic."""

from __future__ import annotations

import unittest
from fractions import Fraction

from scripts.release.pcs_fri_ood_seed_geometry import (
    ENGINE_GITLINK, Q, ROOT, SOURCE_SHA256, audit, classify,
)


class OodSeedGeometryTests(unittest.TestCase):
    def test_pinned_source_and_exact_counts(self) -> None:
        report = audit()
        self.assertEqual(report["schema"], "s31-pcs-fri-ood-seed-geometry-v4")
        self.assertEqual(report["quadratic_subfield_nonexceptional_seed_count"], Q**2 - 2)
        self.assertEqual(Fraction(report["quadratic_subfield_nonexceptional_fraction_if_uniform"]),
                         Fraction(Q**2 - 2, Q**4))
        self.assertEqual(Fraction(report["base_field_seed_fraction_if_uniform"]),
                         Fraction(1, Q**3))
        self.assertEqual(report["y_c1_zero_regular_seed_count"], 2 * Q**2 - 3)
        self.assertEqual(Fraction(report["y_c1_zero_regular_fraction_if_uniform"]),
                         Fraction(2 * Q**2 - 3, Q**4))
        self.assertEqual(report["ideal_raw_u32_preimages_for_residues_zero_one"], 3)
        self.assertEqual(report["ideal_raw_u32_preimages_for_other_residues"], 2)
        self.assertEqual(Fraction(report["ideal_raw_m31_coordinate_tv_from_uniform"]),
                         Fraction(Q - 2, Q * (Q + 1)))
        self.assertEqual(Fraction(report["ideal_independent_raw_words_qm31_max_point_mass"]),
                         Fraction(3**4, 2**128))
        self.assertEqual(Fraction(report["ideal_independent_raw_words_qm31_max_density_ratio_to_uniform"]),
                         Fraction(3**4 * Q**4, 2**128))
        self.assertEqual(Fraction(report["selected_post_reduction_eight_word_block_acceptance_fraction"]),
                         Fraction(1))
        self.assertFalse(report["rom_uniform_qm31_seed_conditional_on_success"])
        self.assertFalse(report["native_blake2s_rom_and_adaptive_bcs_reduction_proven"])
        self.assertFalse(report["published_ood_distribution_instantiated"])
        self.assertIsNone(report["native_proven_security_bits"])

    def test_source_and_gitlink_mutations_require_new_review(self) -> None:
        sources = {name: (ROOT / name).read_bytes() for name in SOURCE_SHA256}
        with self.assertRaisesRegex(ValueError, "gitlink changed"):
            classify(sources, "0" * 40)
        for name in SOURCE_SHA256:
            changed = dict(sources)
            changed[name] += b"\n"
            with self.subTest(name=name), self.assertRaisesRegex(ValueError, "source changed"):
                classify(changed, ENGINE_GITLINK)
        with self.assertRaisesRegex(ValueError, "roster changed"):
            classify({name: data for name, data in sources.items()
                      if name != next(iter(SOURCE_SHA256))}, ENGINE_GITLINK)

    def test_small_quadratic_towers_check_norm_count(self) -> None:
        # Independent finite-field enumeration of a²-(2+i)b²=1 over F_q[i]
        # for two small primes with the same tower structure as M31/CM31.
        for q in (3, 7):
            with self.subTest(q=q):
                elements = [(a, b) for a in range(q) for b in range(q)]
                def add(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
                    return ((a[0] + b[0]) % q, (a[1] + b[1]) % q)
                def mul(a: tuple[int, int], b: tuple[int, int]) -> tuple[int, int]:
                    return ((a[0] * b[0] - a[1] * b[1]) % q,
                            (a[0] * b[1] + a[1] * b[0]) % q)
                norm_one = [(a, b) for a in elements for b in elements
                            if add(mul(a, a),
                                   tuple(-x % q for x in mul((2, 1), mul(b, b)))) == (1, 0)]
                self.assertEqual(len(norm_one), q**2 + 1)
                self.assertEqual(sum(b == (0, 0) for _, b in norm_one), 2)
                regular_y_imag_zero = q**2 - 2 + sum(b != (0, 0) for _, b in norm_one)
                self.assertEqual(regular_y_imag_zero, 2 * q**2 - 3)

                zero = (0, 0)
                one = (1, 0)
                r = (2, 1)
                def mul_l(a: tuple[tuple[int, int], tuple[int, int]],
                          b: tuple[tuple[int, int], tuple[int, int]]) -> tuple[tuple[int, int], tuple[int, int]]:
                    return (add(mul(a[0], b[0]), mul(r, mul(a[1], b[1]))),
                            add(mul(a[0], b[1]), mul(a[1], b[0])))
                def pow_l(a: tuple[tuple[int, int], tuple[int, int]], exponent: int
                          ) -> tuple[tuple[int, int], tuple[int, int]]:
                    result = (one, zero)
                    while exponent:
                        if exponent & 1:
                            result = mul_l(result, a)
                        a = mul_l(a, a)
                        exponent >>= 1
                    return result
                actual_y_imag_zero = 0
                exceptional = 0
                for a in elements:
                    for b in elements:
                        t = (a, b)
                        t2 = mul_l(t, t)
                        denominator = (add(one, t2[0]), t2[1])
                        if denominator == (zero, zero):
                            exceptional += 1
                            continue
                        inverse = pow_l(denominator, q**4 - 2)
                        numerator = (add(a, a), add(b, b))
                        y = mul_l(numerator, inverse)
                        actual_y_imag_zero += y[1] == zero
                self.assertEqual(exceptional, 2)
                self.assertEqual(actual_y_imag_zero, 2 * q**2 - 3)

    def test_small_reduce_then_filter_sampler_is_biased(self) -> None:
        # q=7, raw u32 analogue [0,16): 16=2q+2. As in the selected
        # channel, reduce before the later >=2q check.
        q, word_space = 7, 16
        counts = {r: 0 for r in range(q)}
        rejected = 0
        for x in range(word_space):
            reduced = x % q
            if reduced >= 2 * q:
                rejected += 1
                continue
            counts[reduced] += 1
        self.assertEqual(rejected, 0)
        self.assertEqual([counts[r] for r in range(q)], [3, 3, 2, 2, 2, 2, 2])
        self.assertEqual(sum(counts.values()), word_space)
        total_variation = sum(abs(Fraction(count, word_space) - Fraction(1, q))
                              for count in counts.values()) / 2
        self.assertEqual(total_variation, Fraction(q - 2, q * (q + 1)))
        self.assertEqual(max(counts.values())**4, 3**4)


if __name__ == "__main__":
    unittest.main()
