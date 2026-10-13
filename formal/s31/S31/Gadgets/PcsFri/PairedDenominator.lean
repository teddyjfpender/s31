import S31.Gadgets.Field
import Mathlib.Tactic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
The CAS05 paired quotient divides by the determinant of the displacement
from a base-circle row and the quadratic-extension component of the sampled
point. This lemma isolates the algebra that makes that determinant nonzero.
The quadratic-extension parameter must be nonsquare in the intermediate
field. The native field representation and OOD sampler are separate joins.
-/

namespace S31.Gadgets.PcsFri.PairedDenominator

variable {K : Type*} [Field K]

/-- For a quadratic tower whose lower-level imaginary unit squares to `-1`,
the norm of `2+i` is `5`. Any square root `(a+b*i)` would make `5` a square
in the base field. This isolates the one M31 nonresidue fact needed to
discharge the theorem's `d` premise for the native tower. -/
theorem no_square_root_two_plus_i_of_five_nonsquare
    (hfive : ∀ t : K, t ^ 2 ≠ 5) (a b : K) :
    ¬(a ^ 2 - b ^ 2 = 2 ∧ 2 * a * b = 1) := by
  rintro ⟨hreal, himag⟩
  have hnorm : (a ^ 2 + b ^ 2) ^ 2 = 5 := by
    calc
      (a ^ 2 + b ^ 2) ^ 2 = (a ^ 2 - b ^ 2) ^ 2 + (2 * a * b) ^ 2 := by ring
      _ = 5 := by rw [hreal, himag]; norm_num
  exact hfive _ hnorm

/-- `5` is a nonresidue modulo the actual M31 prime. Reciprocity reduces it
to the five-element field, where the finite check is exhaustive. -/
theorem five_nonsquare_m31 : ∀ t : S31.Field.F, t ^ 2 ≠ 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hreciprocity := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one
    (p := 5) (q := 2147483647) (by decide) (by decide)
  have htwo : ¬ IsSquare (2147483647 : ZMod 5) := by decide
  intro t ht
  apply htwo
  apply hreciprocity.mpr
  exact ⟨t, by simpa [pow_two] using ht.symm⟩

/-- No pair of M31 coordinates can square to the native CM31 tower element
`2+i`, provided its pair multiplication uses `i²=-1`. -/
theorem tower_parameter_no_pair_square_root :
    ¬ ∃ a b : S31.Field.F, a ^ 2 - b ^ 2 = 2 ∧ 2 * a * b = 1 := by
  rintro ⟨a, b, h⟩
  exact no_square_root_two_plus_i_of_five_nonsquare five_nonsquare_m31 a b h

/-- `x₀ + u*x₁, y₀ + u*y₁` lies on the circle for `u²=d`; the base point
`(a,b)` lies on the base circle. If `y₁` is nonzero and `d` is nonsquare,
the native quotient denominator cannot vanish at `(a,b)`. -/
theorem circle_denominator_ne_zero
    (d x₀ y₀ x₁ y₁ a b : K)
    (hd : ∀ t : K, t ^ 2 ≠ d)
    (hcircle₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (hcircle₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hbase : a ^ 2 + b ^ 2 = 1)
    (hy₁ : y₁ ≠ 0) :
    (x₀ - a) * y₁ - (y₀ - b) * x₁ ≠ 0 := by
  intro hden
  let t : K := (y₀ - b) / y₁
  have hy : y₀ - b = t * y₁ := by
    dsimp [t]
    field_simp [hy₁]
  have hxy : (x₀ - a - t * x₁) * y₁ = 0 := by
    calc
      (x₀ - a - t * x₁) * y₁ =
          (x₀ - a) * y₁ - (y₀ - b) * x₁ := by rw [hy]; ring
      _ = 0 := hden
  have hx : x₀ = a + t * x₁ := by
    rcases mul_eq_zero.mp hxy with h | h
    · linear_combination h
    · exact False.elim (hy₁ h)
  have hy' : y₀ = b + t * y₁ := by linear_combination hy
  have hdot : a * x₁ + b * y₁ + t * (x₁ ^ 2 + y₁ ^ 2) = 0 := by
    rw [hx, hy'] at hcircle₁
    linear_combination hcircle₁
  have hnorm : 2 * t * (a * x₁ + b * y₁) +
      (t ^ 2 + d) * (x₁ ^ 2 + y₁ ^ 2) = 0 := by
    rw [hx, hy'] at hcircle₀
    linear_combination hcircle₀ - hbase
  have hfactor : (d - t ^ 2) * (x₁ ^ 2 + y₁ ^ 2) = 0 := by
    calc
      (d - t ^ 2) * (x₁ ^ 2 + y₁ ^ 2) =
          (2 * t * (a * x₁ + b * y₁) +
            (t ^ 2 + d) * (x₁ ^ 2 + y₁ ^ 2)) -
            2 * t * (a * x₁ + b * y₁ + t * (x₁ ^ 2 + y₁ ^ 2)) := by ring
      _ = 0 := by rw [hnorm, hdot]; ring
  have hdifference : d - t ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm (hd t))
  have hsum : x₁ ^ 2 + y₁ ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hdifference
  have hdot' : a * x₁ + b * y₁ = 0 := by rw [hsum] at hdot; simpa using hdot
  have hzero : y₁ ^ 2 = 0 := by
    calc
      y₁ ^ 2 = (a ^ 2 + b ^ 2) * y₁ ^ 2 := by rw [hbase]; ring
      _ = a ^ 2 * (x₁ ^ 2 + y₁ ^ 2) -
            (a * x₁ + b * y₁) * (a * x₁ - b * y₁) := by ring
      _ = 0 := by rw [hsum, hdot']; ring
  exact hy₁ (eq_zero_of_pow_eq_zero hzero)

/-- If the extension parameter is square, all other circle and guard
equations can hold while the denominator is zero. This makes the nonsquare
premise material rather than a convenient proof assumption. -/
example :
    let d : ℚ := 1
    let x₀ : ℚ := 1 / 2
    let y₀ : ℚ := 1 / 2
    let x₁ : ℚ := -1 / 2
    let y₁ : ℚ := 1 / 2
    let a : ℚ := 1
    let b : ℚ := 0
    x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1 ∧
    x₀ * x₁ + y₀ * y₁ = 0 ∧
    a ^ 2 + b ^ 2 = 1 ∧ y₁ ≠ 0 ∧
    (x₀ - a) * y₁ - (y₀ - b) * x₁ = 0 := by
  norm_num

/-- The native `y.c1 != 0` guard is also necessary: with a base-field OOD
point identical to the opened row, the denominator vanishes. -/
example :
    let d : ℚ := 2
    let x₀ : ℚ := 1
    let y₀ : ℚ := 0
    let x₁ : ℚ := 0
    let y₁ : ℚ := 0
    let a : ℚ := 1
    let b : ℚ := 0
    x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1 ∧
    x₀ * x₁ + y₀ * y₁ = 0 ∧
    a ^ 2 + b ^ 2 = 1 ∧
    (x₀ - a) * y₁ - (y₀ - b) * x₁ = 0 := by
  norm_num

end S31.Gadgets.PcsFri.PairedDenominator
