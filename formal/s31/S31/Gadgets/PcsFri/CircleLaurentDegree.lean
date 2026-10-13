import S31.Gadgets.PcsFri.CircleVanishingLine
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic

/-!
Finite Laurent polynomials are an explicit model of circle-coordinate
polynomials after choosing a square root of `-1`: `T = x + i*y`,
`T⁻¹ = x - i*y`. The circle filtration used here is finite support in
`[-n,n]`. This file does not identify native evaluation rows with a Laurent
polynomial, or with the published circle-polynomial basis.
-/

namespace S31.Gadgets.PcsFri.CircleLaurentDegree

open LaurentPolynomial AddMonoidAlgebra

variable {F : Type*} [Field F]

/-- The concrete finite-support circle-polynomial coefficient model. -/
abbrev CirclePoly (F : Type*) [Field F] := LaurentPolynomial F

/-- The two-sided Laurent support filtration. -/
def InCircleBand (n : ℕ) (f : CirclePoly F) : Prop :=
  ∀ k : ℤ, f k ≠ 0 → -(n : ℤ) ≤ k ∧ k ≤ n

/-- Native CAS05's line becomes this three-term Laurent polynomial under
`x=(T+T⁻¹)/2`, `y=(T-T⁻¹)/(2i)`. -/
noncomputable def nativeLineLaurent (i x₀ y₀ x₁ y₁ : F) : CirclePoly F :=
  C ((-y₁ - i * x₁) / 2) * T 1 +
    C (x₀ * y₁ - y₀ * x₁) +
    C ((-y₁ + i * x₁) / 2) * T (-1)

/-- The exact Fourier substitution used to interpret a Laurent coefficient
model as a circle polynomial. When `z*w=1`, the coordinates are on the
circle; the line identity itself needs only `i²=-1`. -/
def fourierX (z w : F) : F := (z + w) / 2
def fourierY (i z w : F) : F := (z - w) / (2 * i)

theorem nativeLine_fourier (i x₀ y₀ x₁ y₁ z w : F)
    (hi : i ^ 2 = -1) :
    CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
      (fourierX z w) (fourierY i z w) =
      ((-y₁ - i * x₁) / 2) * z +
      (x₀ * y₁ - y₀ * x₁) +
      ((-y₁ + i * x₁) / 2) * w := by
  have hi0 : i ≠ 0 := by
    intro hz
    simp [hz] at hi
  have hy : fourierY i z w = -(i * (z - w)) / 2 := by
    dsimp [fourierY]
    field_simp [hi0]
    rw [hi]
    ring
  rw [hy]
  dsimp [CircleVanishingLine.nativeLine, fourierX]
  ring

/-- Evaluating the coefficient model at an invertible Fourier coordinate
recovers exactly the native CAS05 circle line at the corresponding row. -/
theorem eval_nativeLineLaurent (i x₀ y₀ x₁ y₁ : F)
    (hi : i ^ 2 = -1) (t : Fˣ) :
    eval₂ (RingHom.id F) t (nativeLineLaurent i x₀ y₀ x₁ y₁) =
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) := by
  rw [nativeLine_fourier i x₀ y₀ x₁ y₁ t.val t⁻¹.val hi]
  simp [nativeLineLaurent, LaurentPolynomial.eval₂_C]

private theorem single_shift_apply (r : F) (q : CirclePoly F) (a k : ℤ) :
    ((C r * T a * q : CirclePoly F) k) = r * q (k - a) := by
  rw [← single_eq_C_mul_T, AddMonoidAlgebra.single_mul_apply]
  rw [show -a + k = k - a by omega]

theorem nativeLineLaurent_apply (i x₀ y₀ x₁ y₁ : F) (q : CirclePoly F) (k : ℤ) :
    (nativeLineLaurent i x₀ y₀ x₁ y₁ * q) k =
      ((-y₁ - i * x₁) / 2) * q (k - 1) +
      (x₀ * y₁ - y₀ * x₁) * q k +
      ((-y₁ + i * x₁) / 2) * q (k + 1) := by
  simp only [nativeLineLaurent, add_mul]
  change ((C ((-y₁ - i * x₁) / 2) * T 1 * q : CirclePoly F) k) +
      ((C (x₀ * y₁ - y₀ * x₁) * q : CirclePoly F) k) +
      ((C ((-y₁ + i * x₁) / 2) * T (-1) * q : CirclePoly F) k) = _
  rw [single_shift_apply]
  have hmid : ((C (x₀ * y₁ - y₀ * x₁) * q : CirclePoly F) k) =
      (x₀ * y₁ - y₀ * x₁) * q k := by
    conv_lhs => rw [← mul_one (C (x₀ * y₁ - y₀ * x₁)), ← T_zero]
    simpa using single_shift_apply (x₀ * y₁ - y₀ * x₁) q 0 k
  rw [hmid, single_shift_apply]
  simp only [sub_neg_eq_add]

theorem line_coeff_pos (i x₀ y₀ x₁ y₁ : F) :
    (nativeLineLaurent i x₀ y₀ x₁ y₁) 1 = (-y₁ - i * x₁) / 2 := by
  simp [nativeLineLaurent, ← single_eq_C_mul_T]
  have hconst : (C x₀ * C y₁ - C y₀ * C x₁ : CirclePoly F) =
      C (x₀ * y₁ - y₀ * x₁) := by simp
  rw [hconst]
  simp only [LaurentPolynomial.C_apply]
  norm_num

theorem line_coeff_neg (i x₀ y₀ x₁ y₁ : F) :
    (nativeLineLaurent i x₀ y₀ x₁ y₁) (-1) = (-y₁ + i * x₁) / 2 := by
  simp [nativeLineLaurent, ← single_eq_C_mul_T]
  have hconst : (C x₀ * C y₁ - C y₀ * C x₁ : CirclePoly F) =
      C (x₀ * y₁ - y₀ * x₁) := by simp
  rw [hconst]
  simp only [LaurentPolynomial.C_apply]
  norm_num

theorem line_in_band_one (i x₀ y₀ x₁ y₁ : F) :
    InCircleBand 1 (nativeLineLaurent i x₀ y₀ x₁ y₁) := by
  intro k hk
  by_contra hband
  have hk_ne : k ≠ -1 ∧ k ≠ 0 ∧ k ≠ 1 := by omega
  have hz : (nativeLineLaurent i x₀ y₀ x₁ y₁) k = 0 := by
    simp [nativeLineLaurent, ← single_eq_C_mul_T, hk_ne.1, hk_ne.2.2]
    have hconst : (C x₀ * C y₁ - C y₀ * C x₁ : CirclePoly F) =
        C (x₀ * y₁ - y₀ * x₁) := by simp
    rw [hconst]
    simp only [LaurentPolynomial.C_apply]
    simp [hk_ne.2.1]
  exact hk hz

/-- A three-term native line raises the two-sided support radius by at most
one. This is the forward degree implication needed for a paired original and
own-quotient oracle, assuming a quotient polynomial really exists. -/
theorem line_mul_band (i x₀ y₀ x₁ y₁ : F) (n : ℕ) (q : CirclePoly F)
    (hq : InCircleBand n q) :
    InCircleBand (n + 1) (nativeLineLaurent i x₀ y₀ x₁ y₁ * q) := by
  intro k hk
  by_contra hband
  have hqleft : q (k - 1) = 0 := by
    by_contra hz
    obtain ⟨hl, hr⟩ := hq (k - 1) hz
    apply hband
    constructor <;> omega
  have hqmid : q k = 0 := by
    by_contra hz
    obtain ⟨hl, hr⟩ := hq k hz
    apply hband
    constructor <;> omega
  have hqright : q (k + 1) = 0 := by
    by_contra hz
    obtain ⟨hl, hr⟩ := hq (k + 1) hz
    apply hband
    constructor <;> omega
  rw [nativeLineLaurent_apply, hqleft, hqmid, hqright] at hk
  simp at hk

theorem band_add (n : ℕ) (f g : CirclePoly F)
    (hf : InCircleBand n f) (hg : InCircleBand n g) :
    InCircleBand n (f + g) := by
  intro k hsum
  by_cases hfk : f k = 0
  · have hgk : g k ≠ 0 := by
      intro hzero
      apply hsum
      change f k + g k = 0
      rw [hfk, hzero, add_zero]
    exact hg k hgk
  · exact hf k hfk

theorem band_mono (n m : ℕ) (f : CirclePoly F) (hnm : n ≤ m)
    (hf : InCircleBand n f) : InCircleBand m f := by
  intro k hk
  obtain ⟨hl, hr⟩ := hf k hk
  constructor <;> omega

/-- Exact paired reconstruction, with the CAS05 native line as divisor.
Both the original and its own quotient are required as polynomial objects.
For `n≥1`, a degree-`n−1` quotient and degree-one interpolation polynomial
give an original of degree at most `n`. -/
theorem paired_original_band (i x₀ y₀ x₁ y₁ : F) (n : ℕ)
    (f interpolation q : CirclePoly F) (hn : 1 ≤ n)
    (hrelation : f = interpolation + nativeLineLaurent i x₀ y₀ x₁ y₁ * q)
    (hinterpolation : InCircleBand 1 interpolation)
    (hquotient : InCircleBand (n - 1) q) :
    InCircleBand n f := by
  rw [hrelation]
  apply band_add
  · exact band_mono 1 n interpolation hn hinterpolation
  · have h := line_mul_band i x₀ y₀ x₁ y₁ (n - 1) q hquotient
    simpa [Nat.sub_add_cancel hn] using h

/-- An exact paired polynomial identity specializes to the native CAS05
row-quotient formula wherever the native line is nonzero. This is a
polynomial-to-value implication, not a reconstruction from opened rows. -/
theorem paired_row_quotient_eq (i x₀ y₀ x₁ y₁ : F)
    (hi : i ^ 2 = -1) (t : Fˣ)
    (f interpolation q : CirclePoly F)
    (hrelation : f = interpolation + nativeLineLaurent i x₀ y₀ x₁ y₁ * q)
    (hden : CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
      (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) ≠ 0) :
    eval₂ (RingHom.id F) t q =
      (eval₂ (RingHom.id F) t f - eval₂ (RingHom.id F) t interpolation) /
        CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
          (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) := by
  let E := eval₂ (RingHom.id F) t
  have he : E f = E interpolation +
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) * E q := by
    have h := congrArg E hrelation
    simpa only [E, map_add, map_mul, eval_nativeLineLaurent i x₀ y₀ x₁ y₁ hi t]
      using h
  apply (eq_div_iff hden).2
  linear_combination -he

/-- The positive edge cannot cancel against either lower line term. -/
theorem line_mul_upper_edge (i x₀ y₀ x₁ y₁ : F) (n : ℕ)
    (q : CirclePoly F) (hq : InCircleBand n q) :
    (nativeLineLaurent i x₀ y₀ x₁ y₁ * q) ((n : ℤ) + 1) =
      ((-y₁ - i * x₁) / 2) * q n := by
  have hnext : q ((n : ℤ) + 1) = 0 := by
    by_contra hz
    have := (hq _ hz).2
    omega
  have hnext2 : q ((n : ℤ) + 2) = 0 := by
    by_contra hz
    have := (hq _ hz).2
    omega
  rw [nativeLineLaurent_apply]
  have hk1 : (n : ℤ) + 1 - 1 = n := by omega
  have hk2 : (n : ℤ) + 1 + 1 = (n : ℤ) + 2 := by omega
  rw [hk1, hnext, hk2, hnext2]
  ring

/-- The negative edge also survives; the native nondegeneracy guard makes
both edge coefficients nonzero. -/
theorem line_mul_lower_edge (i x₀ y₀ x₁ y₁ : F) (n : ℕ)
    (q : CirclePoly F) (hq : InCircleBand n q) :
    (nativeLineLaurent i x₀ y₀ x₁ y₁ * q) (-((n : ℤ) + 1)) =
      ((-y₁ + i * x₁) / 2) * q (-(n : ℤ)) := by
  have hprev : q (-((n : ℤ) + 1) - 1) = 0 := by
    by_contra hz
    have := (hq _ hz).1
    omega
  have hprev2 : q (-((n : ℤ) + 1)) = 0 := by
    by_contra hz
    have := (hq _ hz).1
    omega
  rw [nativeLineLaurent_apply, hprev, hprev2]
  have hk : -((n : ℤ) + 1) + 1 = -(n : ℤ) := by omega
  rw [hk]
  ring

/-- Under the modeled CAS05 OOD circle and `y.c1` guard, any nonzero
extreme quotient coefficient produces a nonzero extreme residual coefficient.
This shows the forward `+1` filtration bound is sharp in both directions. -/
theorem paired_edge_nonzero [NeZero (2 : F)]
    (d i x₀ y₀ x₁ y₁ : F) (hi : i ^ 2 = -1)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0) (n : ℕ) (q : CirclePoly F)
    (hq : InCircleBand n q) (hpos : q n ≠ 0)
    (hneg : q (-(n : ℤ)) ≠ 0) :
    (nativeLineLaurent i x₀ y₀ x₁ y₁ * q) ((n : ℤ) + 1) ≠ 0 ∧
      (nativeLineLaurent i x₀ y₀ x₁ y₁ * q) (-((n : ℤ) + 1)) ≠ 0 := by
  obtain ⟨hplus, hminus⟩ := CircleVanishingLine.fourier_edges_ne_zero
    d i x₀ y₀ x₁ y₁ hi h₀ h₁ hy
  constructor
  · rw [line_mul_upper_edge i x₀ y₀ x₁ y₁ n q hq]
    exact mul_ne_zero hplus hpos
  · rw [line_mul_lower_edge i x₀ y₀ x₁ y₁ n q hq]
    exact mul_ne_zero hminus hneg

end S31.Gadgets.PcsFri.CircleLaurentDegree
