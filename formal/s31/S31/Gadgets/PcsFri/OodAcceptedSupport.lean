import Mathlib.Tactic

/-!
Exact cardinality arithmetic for the experimental paired verifier's early
`y.c1 != 0` OOD guard.  The count of excluded regular seeds, `2*q^2-3`,
comes from the separate quadratic-tower field argument in the source audit;
this file proves the subsequent support and conditioning arithmetic.  It
does not prove that a native transcript seed is uniform, or instantiate a
published OOD soundness theorem.
-/

namespace S31.Gadgets.PcsFri.OodAcceptedSupport

def q : ℕ := 2 ^ 31 - 1

/-- The paper samples outside the base-field circle: `(q^4-1)-(q+1)`. -/
def paperSupport (p : ℕ) : ℕ := p ^ 4 - p - 2

/-- Regular rational-map seeds whose image has nonzero `y.c1`. -/
def acceptedSupport (p : ℕ) : ℕ := p ^ 4 - (2 * p ^ 2 - 3) - 2

theorem accepted_support_square :
    acceptedSupport q = (q ^ 2 - 1) ^ 2 := by
  norm_num [acceptedSupport, q]

theorem paper_support_minus_accepted :
    paperSupport q - acceptedSupport q = 2 * q ^ 2 - q - 3 := by
  norm_num [paperSupport, acceptedSupport, q]

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
