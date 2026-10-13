import Mathlib.Tactic
import S31.Gadgets.PcsFri.OodGuardFiniteCount

/-!
Exact cardinality arithmetic for the experimental paired verifier's early
`y.c1 != 0` OOD guard. `OodGuardFiniteCount` proves the excluded regular
seed count `2*q^2-3` over a qualifying quadratic tower. This file
specializes that count to a lower field of size `q²`, then proves the
support and conditioning arithmetic. It
does not prove that a native transcript seed is uniform, or instantiate a
published OOD soundness theorem.
-/

namespace S31.Gadgets.PcsFri.OodAcceptedSupport

def q : ℕ := 2 ^ 31 - 1

/-- The paper samples outside the base-field circle: `(q^4-1)-(q+1)`. -/
def paperSupport (p : ℕ) : ℕ := p ^ 4 - p - 2

/-- The two-point conjugate construction described in Section 4.5 instead
samples outside the intermediate-field circle. Its affine support has size
`(q^4-1)-(q^2-1)`. This definition is cardinality arithmetic; applying a
two-point OOD soundness bound still requires a separate theorem. -/
def twoPointSupport (p : ℕ) : ℕ := p ^ 4 - p ^ 2

/-- Regular rational-map seeds whose image has nonzero `y.c1`. -/
def acceptedSupport (p : ℕ) : ℕ := p ^ 4 - (2 * p ^ 2 - 3) - 2

theorem accepted_support_square :
    acceptedSupport q = (q ^ 2 - 1) ^ 2 := by
  norm_num [acceptedSupport, q]

section FieldCount

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [NeZero (2 : K)]

/-- The support arithmetic is the exact cardinality of the modeled native
guard when the lower field has M31-squared size, `R` is nonsquare, and the
lower field contains a square root of `-1`. The concrete CM31 refinement
and transcript distribution are independent obligations. -/
theorem accepted_support_from_field (R i : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (hi : i ^ 2 = -1)
    (hcard : Fintype.card K = q ^ 2) :
    (OodGuardFiniteCount.acceptedGuard R).card = acceptedSupport q := by
  rw [OodGuardFiniteCount.accepted_guard_card R i hR hi,
    hcard, accepted_support_square]

theorem excluded_regular_from_field (R i : K)
    (hR : ∀ v : K, v ^ 2 ≠ R) (hi : i ^ 2 = -1)
    (hcard : Fintype.card K = q ^ 2) :
    (OodGuardFiniteCount.excludedRegular R).card = 2 * q ^ 2 - 3 := by
  rw [OodGuardFiniteCount.excluded_regular_card R i hR hi, hcard]

end FieldCount

theorem paper_support_minus_accepted :
    paperSupport q - acceptedSupport q = 2 * q ^ 2 - q - 3 := by
  norm_num [paperSupport, acceptedSupport, q]

theorem two_point_support_minus_accepted :
    twoPointSupport q - acceptedSupport q = q ^ 2 - 1 := by
  norm_num [twoPointSupport, acceptedSupport, q]

theorem accepted_support_lt_two_point_support :
    acceptedSupport q < twoPointSupport q := by
  norm_num [twoPointSupport, acceptedSupport, q]

/-- Exact uniform-conditioning ratio for the two-point universe. The native
Fiat–Shamir draw has not been proved uniform on either support. -/
def twoPointConditioningFactor : ℚ :=
  (twoPointSupport q : ℚ) / (acceptedSupport q : ℚ)

theorem two_point_conditioning_factor_eq :
    twoPointConditioningFactor =
      (q ^ 2 : ℚ) / ((q ^ 2 - 1 : ℕ) : ℚ) := by
  norm_num [twoPointConditioningFactor, twoPointSupport, acceptedSupport, q]

/-- A fixed bad-set bound over the two-point universe transfers to the
guarded support with this exact conditioning factor. This theorem supplies
only the finite mass step, not the bad-set bound or adaptive sampler law. -/
theorem conditional_two_point_bad_mass_le (a b : ℕ) (hab : a ≤ b) :
    (a : ℚ) / (acceptedSupport q : ℚ) ≤
      ((b : ℚ) / (twoPointSupport q : ℚ)) * twoPointConditioningFactor := by
  have ha : (a : ℚ) ≤ b := by exact_mod_cast hab
  have hden : (0 : ℚ) < acceptedSupport q := by
    norm_num [acceptedSupport, q]
  have htwo : (twoPointSupport q : ℚ) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le hden (by
      exact_mod_cast (le_of_lt accepted_support_lt_two_point_support)))
  unfold twoPointConditioningFactor
  rw [div_mul_div_cancel₀ htwo]
  exact div_le_div_of_nonneg_right ha (le_of_lt hden)

theorem accepted_support_positive : 0 < acceptedSupport q := by
  norm_num [acceptedSupport, q]

theorem accepted_support_strictly_smaller :
    acceptedSupport q < paperSupport q := by
  norm_num [acceptedSupport, paperSupport, q]

/-- The exact inflation factor of a fixed bad-set probability when one
conditions the paper's uniform OOD sample on the native accepted support. -/
def conditioningFactor : ℚ :=
  (paperSupport q : ℚ) / (acceptedSupport q : ℚ)

theorem conditioning_factor_eq :
    conditioningFactor =
      1 + ((2 * q ^ 2 - q - 3 : ℕ) : ℚ) / (acceptedSupport q : ℚ) := by
  norm_num [conditioningFactor, paperSupport, acceptedSupport, q]

theorem conditioning_factor_gt_one : 1 < conditioningFactor := by
  norm_num [conditioningFactor, paperSupport, acceptedSupport, q]

/-- The support correction is less than one part in `2^60`, though it is
strictly nonzero.  This is arithmetic, not a claim about native sampling. -/
theorem conditioning_factor_lt_one_plus_2pow_neg60 :
    conditioningFactor < 1 + (1 : ℚ) / 2 ^ 60 := by
  norm_num [conditioningFactor, paperSupport, acceptedSupport, q]

/-- If a bad event has at most `b` paper-support points and at most `a <= b`
accepted-support points, its conditional uniform probability is bounded by
the paper probability times the exact support inflation factor. -/
theorem conditional_bad_mass_le (a b : ℕ) (hab : a ≤ b) :
    (a : ℚ) / (acceptedSupport q : ℚ) ≤
      ((b : ℚ) / (paperSupport q : ℚ)) * conditioningFactor := by
  have ha : (a : ℚ) ≤ b := by exact_mod_cast hab
  have hden : (0 : ℚ) < acceptedSupport q := by
    exact_mod_cast accepted_support_positive
  have hpaper : (paperSupport q : ℚ) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le hden (by
      exact_mod_cast (le_of_lt accepted_support_strictly_smaller)))
  unfold conditioningFactor
  rw [div_mul_div_cancel₀ hpaper]
  exact div_le_div_of_nonneg_right ha (le_of_lt hden)

end S31.Gadgets.PcsFri.OodAcceptedSupport
