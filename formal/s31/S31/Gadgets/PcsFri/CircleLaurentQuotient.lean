import S31.Gadgets.PcsFri.CircleLaurentDegree
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Tactic

/-!
The exact CAS05 circle-line quotient in a finite Laurent coefficient model.
This file reasons about polynomial coefficients. It does not identify native
committed evaluation rows with these coefficients or identify the filtration
with the paper's circle basis `L_n'`.
-/

namespace S31.Gadgets.PcsFri.CircleLaurentQuotient

open LaurentPolynomial AddMonoidAlgebra Polynomial
open S31.Gadgets.PcsFri.CircleLaurentDegree

variable {F : Type*} [Field F]

/-- Shifting an ordinary polynomial of degree at most `2n` down by `n`
produces a circle Laurent polynomial supported in `[-n,n]`. -/
theorem shifted_polynomial_in_band (p : F[X]) (n : ℕ)
    (hp : p.natDegree ≤ 2 * n) :
    InCircleBand n (p.toLaurent * T (-(n : ℤ))) := by
  intro k hk
  have hcoeff : p.toLaurent (k + n) ≠ 0 := by
    simpa only [LaurentPolynomial.T, AddMonoidAlgebra.mul_single_apply,
      neg_neg, mul_one] using hk
  have hmem : k + n ∈ p.toLaurent.support := Finsupp.mem_support_iff.mpr hcoeff
  rw [LaurentPolynomial.toLaurent_support] at hmem
  obtain ⟨j, hj, hjk⟩ := Finset.mem_map.mp hmem
  have hjle : j ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero
    (Polynomial.mem_support_iff.mp hj)
  have hjk' : (j : ℤ) = k + n := by simpa using hjk
  have hjle' : (j : ℤ) ≤ (p.natDegree : ℤ) := by exact_mod_cast hjle
  have hp' : (p.natDegree : ℤ) ≤ 2 * (n : ℤ) := by exact_mod_cast hp
  constructor <;> omega

private theorem trunc_coeff (g : CirclePoly F) (j : ℕ) :
    (LaurentPolynomial.trunc g).coeff j = g (j : ℤ) := by
  rfl

private theorem toLaurent_trunc_of_nonnegative (g : CirclePoly F)
    (hg : ∀ k : ℤ, k < 0 → g k = 0) :
    (LaurentPolynomial.trunc g).toLaurent = g := by
  ext k
  by_cases hk : 0 ≤ k
  · lift k to ℕ using hk
    rw [Polynomial.toLaurent_apply]
    change (Finsupp.mapDomain (fun j : ℕ => (j : ℤ))
      (LaurentPolynomial.trunc g).toFinsupp) (k : ℤ) = g (k : ℤ)
    have hinj : Function.Injective (fun j : ℕ => (j : ℤ)) := by
      intro a b h
      change (a : ℤ) = (b : ℤ) at h
      exact_mod_cast h
    rw [Finsupp.mapDomain_apply hinj]
    exact trunc_coeff g k
  · rw [Polynomial.toLaurent_apply, Finsupp.mapDomain_notin_range]
    · exact (hg k (by omega)).symm
    · rintro ⟨j, hj⟩
      omega

/-- Every circle Laurent polynomial in `[-n,n]` has a canonical ordinary
polynomial representation after shifting by `T^n`, with degree at most `2n`.
This discharges the source representation certificate used by the quotient
construction without assuming a quotient exists. -/
theorem band_has_shifted_polynomial (f : CirclePoly F) (n : ℕ)
    (hf : InCircleBand n f) :
    ∃ p : F[X], p.natDegree ≤ 2 * n ∧
      f = p.toLaurent * T (-(n : ℤ)) := by
  let g : CirclePoly F := f * T n
  let p : F[X] := LaurentPolynomial.trunc g
  have hg_nonnegative : ∀ k : ℤ, k < 0 → g k = 0 := by
    intro k hk
    have hfzero : f (k - n) = 0 := by
      by_contra hnon
      have := (hf (k - n) hnon).1
      omega
    dsimp [g]
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.mul_single_apply]
    simpa only [sub_eq_add_neg, zero_mul] using congrArg (fun x : F => x * 1) hfzero
  have hp_toLaurent : p.toLaurent = g :=
    toLaurent_trunc_of_nonnegative g hg_nonnegative
  have hp_degree : p.natDegree ≤ 2 * n := by
    apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    change (LaurentPolynomial.trunc g).coeff j = 0
    rw [trunc_coeff]
    have hfzero : f ((j : ℤ) - n) = 0 := by
      by_contra hnon
      have := (hf ((j : ℤ) - n) hnon).2
      have hj' : 2 * (n : ℤ) < (j : ℤ) := by exact_mod_cast hj
      omega
    dsimp [g]
    simp only [LaurentPolynomial.T, AddMonoidAlgebra.mul_single_apply]
    simpa only [sub_eq_add_neg, zero_mul] using congrArg (fun x : F => x * 1) hfzero
  refine ⟨p, hp_degree, ?_⟩
  have hundo : f = f * T n * T (-(n : ℤ)) := by
    rw [mul_assoc, ← LaurentPolynomial.T_add]
    norm_num
  rw [hundo]
  change g * T (-(n : ℤ)) = p.toLaurent * T (-(n : ℤ))
  rw [hp_toLaurent]

private theorem scale_preserves_band (c : F) (n : ℕ) (q : CirclePoly F)
    (hq : InCircleBand n q) : InCircleBand n (LaurentPolynomial.C c * q) := by
  intro k hk
  rw [← LaurentPolynomial.smul_eq_C_mul] at hk
  have hqk : q k ≠ 0 := by
    intro hz
    apply hk
    simp [hz]
  exact hq k hqk

/-- The Laurent OOD evaluation of a shifted source polynomial vanishes
exactly when the ordinary polynomial evaluation vanishes. The Fourier
coordinate is a unit on the circle, so the shift cannot create a root. -/
theorem aeval_zero_of_shifted_eval_zero
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (p : F[X]) (n : ℕ)
    (h : LaurentPolynomial.eval₂ (algebraMap F E) z
      (p.toLaurent * T (-(n : ℤ))) = 0) :
    Polynomial.aeval z.val p = 0 := by
  rw [map_mul, LaurentPolynomial.eval₂_toLaurent,
    LaurentPolynomial.eval₂_T_neg_n] at h
  have hz : (z⁻¹ : Eˣ).val ^ n ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  exact (mul_eq_zero.mp h).resolve_right hz

/-- Multiplying the three Laurent terms of a circle line by `T` gives an
ordinary quadratic with the same two extension roots. -/
theorem three_term_shift (a b c : F) :
    (LaurentPolynomial.C a * T 1 + LaurentPolynomial.C b +
        LaurentPolynomial.C c * T (-1)) * T 1 =
      (Polynomial.C a * Polynomial.X ^ 2 +
        Polynomial.C b * Polynomial.X + Polynomial.C c).toLaurent := by
  simp only [add_mul, map_add, map_mul, Polynomial.toLaurent_C,
    Polynomial.toLaurent_X, map_pow]
  have hneg : (T (-1) * T 1 : CirclePoly F) = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  simp only [mul_assoc, hneg, mul_one]
  ring

/-- A nondegenerate three-term circle line that vanishes at an OOD Fourier
coordinate is the scaled minimal polynomial of that coordinate, provided
the coordinate has quadratic minimal polynomial. The proof uses one root
over an extension field; no split-field factorization is assumed. -/
theorem three_term_scaled_minpoly
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (a b c : F) (ha : a ≠ 0)
    (hminpoly : (minpoly F z.val).Monic)
    (hdegree : (minpoly F z.val).natDegree = 2)
    (hroot : LaurentPolynomial.eval₂ (algebraMap F E) z
      (LaurentPolynomial.C a * T 1 + LaurentPolynomial.C b +
        LaurentPolynomial.C c * T (-1)) = 0) :
    LaurentPolynomial.C a * T 1 + LaurentPolynomial.C b +
        LaurentPolynomial.C c * T (-1) =
      LaurentPolynomial.C a * (minpoly F z.val).toLaurent * T (-1) := by
  let P : F[X] := Polynomial.C a * Polynomial.X ^ 2 +
    Polynomial.C b * Polynomial.X + Polynomial.C c
  have hPdeg : P.natDegree = 2 := Polynomial.natDegree_quadratic ha
  have hPlead : P.leadingCoeff = a := Polynomial.leadingCoeff_quadratic ha
  have hPzero : Polynomial.aeval z.val P = 0 := by
    have he := congrArg (LaurentPolynomial.eval₂ (algebraMap F E) z)
      (three_term_shift a b c)
    rw [map_mul, hroot, zero_mul, LaurentPolynomial.eval₂_toLaurent] at he
    exact he.symm
  have hPdvd : minpoly F z.val ∣ P := minpoly.dvd F z.val hPzero
  have hP : P = minpoly F z.val * Polynomial.C a := by
    have h := Polynomial.eq_mul_leadingCoeff_of_monic_of_dvd_of_natDegree_le
      hminpoly hPdvd (by omega)
    simpa only [hPlead] using h
  have hshift := three_term_shift a b c
  change _ = P.toLaurent at hshift
  rw [hP, map_mul, Polynomial.toLaurent_C] at hshift
  have hundo : (LaurentPolynomial.C a * T 1 + LaurentPolynomial.C b +
      LaurentPolynomial.C c * T (-1)) =
      (LaurentPolynomial.C a * T 1 + LaurentPolynomial.C b +
        LaurentPolynomial.C c * T (-1)) * T 1 * T (-1) := by
    rw [mul_assoc, ← LaurentPolynomial.T_add]
    norm_num
  rw [hundo, hshift]
  ring

/-- A quadratic minimal polynomial supplies the *own* circle-line quotient.
The input is a bounded ordinary polynomial shifted into Laurent coordinates;
`hline` identifies the actual three-term native line with the scaled minimal
polynomial. The OOD root is over an extension field, while the quotient stays
over the coefficient field `F`. -/
theorem quotient_of_ood_root
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (n : ℕ) (hn : 1 ≤ n)
    (p : F[X]) (hp : p.natDegree ≤ 2 * n)
    (i x₀ y₀ x₁ y₁ c : F) (hc : c ≠ 0)
    (hline : nativeLineLaurent i x₀ y₀ x₁ y₁ =
      LaurentPolynomial.C c * (minpoly F z.val).toLaurent * T (-1))
    (hdegree : (minpoly F z.val).natDegree = 2)
    (hroot : Polynomial.aeval z.val p = 0) :
    ∃ q : CirclePoly F,
      InCircleBand (n - 1) q ∧
        p.toLaurent * T (-(n : ℤ)) = nativeLineLaurent i x₀ y₀ x₁ y₁ * q := by
  let m : F[X] := minpoly F z.val
  obtain ⟨s, hs⟩ : m ∣ p := minpoly.dvd F z.val hroot
  have hsdegree : s.natDegree ≤ 2 * (n - 1) := by
    by_cases hsz : s = 0
    · simp [hsz]
    · have hmz : m ≠ 0 := by
        intro hm
        simp [m, hm] at hdegree
      have hmul : (m * s).natDegree = m.natDegree + s.natDegree := by
        apply Polynomial.natDegree_mul'
        exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hmz)
          (Polynomial.leadingCoeff_ne_zero.mpr hsz)
      rw [hs, hmul] at hp
      dsimp [m] at hp
      omega
  let q : CirclePoly F := LaurentPolynomial.C c⁻¹ *
    (s.toLaurent * T (-((n - 1 : ℕ) : ℤ)))
  refine ⟨q, scale_preserves_band c⁻¹ (n - 1) _
    (shifted_polynomial_in_band s (n - 1) hsdegree), ?_⟩
  rw [hs, hline]
  dsimp [q]
  simp only [map_mul]
  have hshift : (-1 : ℤ) + -((n - 1 : ℕ) : ℤ) = -(n : ℤ) := by omega
  have hcunit : (LaurentPolynomial.C c * LaurentPolynomial.C c⁻¹ : CirclePoly F) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  calc
    (m.toLaurent * s.toLaurent) * T (-(n : ℤ)) =
        (m.toLaurent * s.toLaurent) *
          (T (-1) * T (-((n - 1 : ℕ) : ℤ))) := by
        rw [← LaurentPolynomial.T_add, hshift]
    _ = (LaurentPolynomial.C c * LaurentPolynomial.C c⁻¹) *
          (m.toLaurent * s.toLaurent * T (-1) * T (-((n - 1 : ℕ) : ℤ))) := by
        rw [hcunit, one_mul]
        ring
    _ =
        (LaurentPolynomial.C c * m.toLaurent * T (-1)) *
          (LaurentPolynomial.C c⁻¹ * (s.toLaurent * T (-((n - 1 : ℕ) : ℤ)))) := by
        ring

/-- Specialization of the generic quadratic divisor lemma to the actual
native CAS05 Fourier coefficients. The leading-edge condition follows from
the modeled OOD circle equation and native `y.c1 != 0` guard. -/
theorem native_line_scaled_minpoly
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (d i x₀ y₀ x₁ y₁ : F)
    (hi : i ^ 2 = -1)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hminpoly : (minpoly F z.val).Monic)
    (hdegree : (minpoly F z.val).natDegree = 2)
    (hlineRoot : LaurentPolynomial.eval₂ (algebraMap F E) z
      (nativeLineLaurent i x₀ y₀ x₁ y₁) = 0) :
    nativeLineLaurent i x₀ y₀ x₁ y₁ =
      LaurentPolynomial.C ((-y₁ - i * x₁) / 2) *
        (minpoly F z.val).toLaurent * T (-1) := by
  have hlead := (CircleVanishingLine.fourier_edges_ne_zero
    d i x₀ y₀ x₁ y₁ hi h₀ h₁ hy).1
  simpa only [nativeLineLaurent] using
    three_term_scaled_minpoly z ((-y₁ - i * x₁) / 2)
      (x₀ * y₁ - y₀ * x₁) ((-y₁ + i * x₁) / 2)
      hlead hminpoly hdegree hlineRoot

/-- For an original and an OOD interpolation agreeing at the extension point,
this theorem
constructs the missing *own* quotient and its `[-(n-1),n-1]` support bound.
The source certificate `hshift` states the residual as a degree-`≤2n`
ordinary polynomial shifted by `-n`; a separate refinement must derive that
certificate from native committed circle rows. -/
theorem quotient_of_correct_ood_claim
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (n : ℕ) (hn : 1 ≤ n)
    (d i x₀ y₀ x₁ y₁ : F)
    (hi : i ^ 2 = -1)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hminpoly : (minpoly F z.val).Monic)
    (hdegree : (minpoly F z.val).natDegree = 2)
    (hlineRoot : LaurentPolynomial.eval₂ (algebraMap F E) z
      (nativeLineLaurent i x₀ y₀ x₁ y₁) = 0)
    (f interpolation : CirclePoly F)
    (p : F[X]) (hp : p.natDegree ≤ 2 * n)
    (hshift : f - interpolation = p.toLaurent * T (-(n : ℤ)))
    (hclaim : LaurentPolynomial.eval₂ (algebraMap F E) z f =
      LaurentPolynomial.eval₂ (algebraMap F E) z interpolation) :
    ∃ q : CirclePoly F,
      InCircleBand (n - 1) q ∧
        f = interpolation + nativeLineLaurent i x₀ y₀ x₁ y₁ * q := by
  let a := (-y₁ - i * x₁) / 2
  have ha : a ≠ 0 := (CircleVanishingLine.fourier_edges_ne_zero
    d i x₀ y₀ x₁ y₁ hi h₀ h₁ hy).1
  have hline := native_line_scaled_minpoly z d i x₀ y₀ x₁ y₁
    hi h₀ h₁ hy hminpoly hdegree hlineRoot
  have hresidualZero : LaurentPolynomial.eval₂ (algebraMap F E) z
      (p.toLaurent * T (-(n : ℤ))) = 0 := by
    rw [← hshift, (LaurentPolynomial.eval₂ (algebraMap F E) z).map_sub]
    exact sub_eq_zero.mpr hclaim
  obtain ⟨q, hqband, hqrel⟩ := quotient_of_ood_root z n hn p hp
    i x₀ y₀ x₁ y₁ a ha hline hdegree
    (aeval_zero_of_shifted_eval_zero z p n hresidualZero)
  refine ⟨q, hqband, ?_⟩
  have hrem : f - interpolation = nativeLineLaurent i x₀ y₀ x₁ y₁ * q :=
    hshift.trans hqrel
  calc
    f = (f - interpolation) + interpolation := by ring
    _ = interpolation + nativeLineLaurent i x₀ y₀ x₁ y₁ * q := by
      rw [hrem]
      ring

/-- The quotient existence theorem from the actual two-sided Laurent band.
The interpolation polynomial has band one and agrees with the original at
the OOD Fourier coordinate. Quadratic minimal-polynomial data and the exact
native-line OOD root remain explicit hypotheses. The quotient is constructed
over `F` and has one less Laurent band radius. -/
theorem native_circle_quotient_exists
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (n : ℕ) (hn : 1 ≤ n)
    (d i x₀ y₀ x₁ y₁ : F)
    (hi : i ^ 2 = -1)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hminpoly : (minpoly F z.val).Monic)
    (hdegree : (minpoly F z.val).natDegree = 2)
    (hlineRoot : LaurentPolynomial.eval₂ (algebraMap F E) z
      (nativeLineLaurent i x₀ y₀ x₁ y₁) = 0)
    (f interpolation : CirclePoly F)
    (hf : InCircleBand n f)
    (hinterpolation : InCircleBand 1 interpolation)
    (hclaim : LaurentPolynomial.eval₂ (algebraMap F E) z f =
      LaurentPolynomial.eval₂ (algebraMap F E) z interpolation) :
    ∃ q : CirclePoly F,
      InCircleBand (n - 1) q ∧
        f = interpolation + nativeLineLaurent i x₀ y₀ x₁ y₁ * q := by
  have hinterpolation_n : InCircleBand n interpolation :=
    band_mono 1 n interpolation hn hinterpolation
  have hresidualBand : InCircleBand n (f - interpolation) := by
    intro k hk
    by_cases hfk : f k = 0
    · have hik : interpolation k ≠ 0 := by
        intro hi0
        apply hk
        change f k - interpolation k = 0
        rw [hfk, hi0]
        ring
      exact hinterpolation_n k hik
    · exact hf k hfk
  obtain ⟨p, hp, hshift⟩ :=
    band_has_shifted_polynomial (f - interpolation) n hresidualBand
  exact quotient_of_correct_ood_claim z n hn d i x₀ y₀ x₁ y₁
    hi h₀ h₁ hy hminpoly hdegree hlineRoot
    f interpolation p hp hshift hclaim

end S31.Gadgets.PcsFri.CircleLaurentQuotient
