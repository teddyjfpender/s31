import S31.Gadgets.PcsFri.OodGuardFieldCount
import Mathlib.Tactic

/-!
The native raw `y.c1 != 0` guard is not inherited by lower-height sampled
points. A circle point with both coordinates purely upper in QM31 can pass
that guard, while one circle doubling makes its `y` coordinate lower.

This is an algebraic implication about the native tower formulas. It does
not count such points, model a Fiat–Shamir distribution, or prove a PCS bound.
-/

namespace S31.Gadgets.PcsFri.ProjectedOodGuard

open OodGuardFieldCount

abbrev QM31 := ConcreteCircleCount.QM31

theorem double_c1_general (z : QM31) :
    (2 * z).c1 = 2 * z.c1 := by
  obtain ⟨a, b⟩ := z
  exact double_c1 a b

/-- The circle group's doubled `y` coordinate is `2*x*y`. Pure-upper
coordinates make this coordinate fixed by complex conjugation. -/
theorem pure_upper_doubled_y_lower (x y : QM31)
    (hx : x.c0 = 0) (hy : y.c0 = 0) :
    (2 * x * y).c1 = 0 := by
  rw [qm_mul_c1]
  rw [double_c1_general]
  have h2x0 : (2 * x).c0 = 0 := by
    obtain ⟨a, b⟩ := x
    simp only at hx
    rw [double_c0, hx]
    ring
  rw [h2x0, hy]
  ring

def q : ℕ := 2 ^ 31 - 1

/-- The quotient of the QM31 circle by its CM31 subcircle has size
`q²+1`, whose 2-part is exactly two. The native witness pins the relevant
nonlower coset separately; this arithmetic alone is not a cyclic-group
classification theorem. -/
theorem quotient_size_two_part : (q ^ 2 + 1) % 4 = 2 := by
  norm_num [q]

end S31.Gadgets.PcsFri.ProjectedOodGuard
