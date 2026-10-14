import S31.Gadgets.PcsFri.CircleLaurentQuotient
import Mathlib.Tactic

/-!
Finite-domain uniqueness for the CAS05 circle Laurent coefficient model.
An `L_n` word is a Laurent polynomial supported in `[-n,n]`; multiplying by
`T^n` makes an ordinary polynomial of degree at most `2n`. Thus more than
`2n` distinct nonzero Fourier coordinates determine the whole word. This is
the algebraic uniqueness premise, not an identification of native committed
rows with the coefficient model or with the paper's circle code.
-/

namespace S31.Gadgets.PcsFri.CircleLaurentUniqueness

open Polynomial LaurentPolynomial AddMonoidAlgebra
open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.CircleLaurentQuotient

variable {F : Type*} [Field F]

theorem band_sub (f g : CirclePoly F) (n : ℕ)
    (hf : InCircleBand n f) (hg : InCircleBand n g) :
    InCircleBand n (f - g) := by
  intro k hk
  by_cases hfk : f k = 0
  · have hgk : g k ≠ 0 := by
      intro hzero
      apply hk
      change f k - g k = 0
      rw [hfk, hzero]
      ring
    exact hg k hgk
  · exact hf k hfk

/-- At a unit Fourier coordinate, vanishing of a bounded Laurent word gives
a root of its shifted ordinary polynomial. The shift is invertible. -/
theorem shifted_root (f : CirclePoly F) (n : ℕ)
    (p : F[X]) (hshift : f = p.toLaurent * T (-(n : ℤ)))
    (t : Fˣ) (hzero : eval₂ (RingHom.id F) t f = 0) :
    p.eval t.val = 0 := by
  rw [hshift, map_mul, LaurentPolynomial.eval₂_toLaurent,
    LaurentPolynomial.eval₂_T_neg_n] at hzero
  have hunit : (t⁻¹ : Fˣ).val ^ n ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
  have hp : p.eval₂ (RingHom.id F) t.val = 0 :=
    (mul_eq_zero.mp hzero).resolve_right hunit
  simpa using hp

/-- A nonzero radius-`n` circle Laurent word has at most `2n` zeros among
any finite set of distinct unit Fourier coordinates. -/
theorem band_zero_count [DecidableEq F] (f : CirclePoly F) (n : ℕ)
    (hf : InCircleBand n f) (hneq : f ≠ 0) (samples : Finset Fˣ) :
    (samples.filter fun t => eval₂ (RingHom.id F) t f = 0).card ≤ 2 * n := by
  classical
  obtain ⟨p, hpdegree, hshift⟩ := band_has_shifted_polynomial f n hf
  have hpne : p ≠ 0 := by
    intro hz
    apply hneq
    rw [hshift, hz]
    simp
  let zeros := samples.filter fun t => eval₂ (RingHom.id F) t f = 0
  have hinj : Function.Injective (fun t : Fˣ => t.val) := Units.val_injective
  have hcard : zeros.card = (zeros.image fun t : Fˣ => t.val).card :=
    (Finset.card_image_iff.mpr fun _ _ _ _ h => hinj h).symm
  have hsubset : (zeros.image fun t : Fˣ => t.val).val ⊆ p.roots := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (Polynomial.mem_roots hpne).2
      (shifted_root f n p hshift t (Finset.mem_filter.mp ht).2)
  rw [hcard]
  exact (Polynomial.card_le_degree_of_subset_roots hsubset).trans hpdegree

/-- More than `2n` matching distinct circle rows determine an `L_n`
polynomial uniquely. The coordinates must be units and genuinely distinct;
CAS05's native canonical-domain map is a separate refinement. -/
theorem band_eq_of_agreement [DecidableEq F] (f g : CirclePoly F) (n : ℕ)
    (hf : InCircleBand n f) (hg : InCircleBand n g)
    (samples : Finset Fˣ) (hmany : 2 * n < samples.card)
    (hagree : ∀ t ∈ samples,
      eval₂ (RingHom.id F) t f = eval₂ (RingHom.id F) t g) : f = g := by
  by_contra hne
  have hsub : f - g ≠ 0 := sub_ne_zero.mpr hne
  have hcard := band_zero_count (f - g) n
    (band_sub f g n hf hg) hsub samples
  have hall : (samples.filter fun t =>
      eval₂ (RingHom.id F) t (f - g) = 0) = samples := by
    apply Finset.filter_eq_self.mpr
    intro t ht
    rw [_root_.map_sub]
    exact sub_eq_zero.mpr (hagree t ht)
  rw [hall] at hcard
  omega

/-- If enough distinct rows of two already bounded oracles satisfy CAS05's
own-quotient equation, then the whole polynomial relation holds. This is the
exact full-table uniqueness lemma. Sparse sampled acceptance requires a
separate correlated-agreement and query theorem. -/
theorem paired_relation_of_row_agreement [DecidableEq F]
    (i x₀ y₀ x₁ y₁ : F) (hi : i ^ 2 = -1)
    (n : ℕ) (hn : 1 ≤ n)
    (f interpolation q : CirclePoly F)
    (hf : InCircleBand n f)
    (hinterpolation : InCircleBand 1 interpolation)
    (hq : InCircleBand (n - 1) q)
    (samples : Finset Fˣ) (hmany : 2 * n < samples.card)
    (hden : ∀ t ∈ samples,
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) ≠ 0)
    (hrows : ∀ t ∈ samples,
      eval₂ (RingHom.id F) t q =
        (eval₂ (RingHom.id F) t f -
          eval₂ (RingHom.id F) t interpolation) /
        CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
          (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val)) :
    f = interpolation + nativeLineLaurent i x₀ y₀ x₁ y₁ * q := by
  let reconstructed := interpolation + nativeLineLaurent i x₀ y₀ x₁ y₁ * q
  have hreconstructed : InCircleBand n reconstructed :=
    paired_original_band i x₀ y₀ x₁ y₁ n reconstructed interpolation q hn
      rfl hinterpolation hq
  apply band_eq_of_agreement f reconstructed n hf hreconstructed samples hmany
  intro t ht
  have hrow := (eq_div_iff (hden t ht)).mp (hrows t ht)
  dsimp [reconstructed]
  rw [map_add, map_mul, eval_nativeLineLaurent i x₀ y₀ x₁ y₁ hi t]
  linear_combination -hrow

/-- Exact degree correction on an arbitrary finite source table: if a
bounded own-quotient polynomial satisfies the native row formula at every
listed row, the table is the evaluation of a bounded reconstructed original.
This uses *all* rows of the claimed table. CAS05 authenticates a sparse
sample, so its soundness still needs a proximity/correlated-agreement proof. -/
theorem bounded_source_of_all_own_quotient_rows
    (i x₀ y₀ x₁ y₁ : F) (hi : i ^ 2 = -1)
    (n : ℕ) (hn : 1 ≤ n)
    (interpolation q : CirclePoly F)
    (hinterpolation : InCircleBand 1 interpolation)
    (hq : InCircleBand (n - 1) q)
    (source : Fˣ → F) (rows : Finset Fˣ)
    (hden : ∀ t ∈ rows,
      CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
        (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) ≠ 0)
    (hrows : ∀ t ∈ rows,
      eval₂ (RingHom.id F) t q =
        (source t - eval₂ (RingHom.id F) t interpolation) /
          CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
            (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val)) :
    ∃ f : CirclePoly F,
      InCircleBand n f ∧
      ∀ t ∈ rows, eval₂ (RingHom.id F) t f = source t := by
  let f := interpolation + nativeLineLaurent i x₀ y₀ x₁ y₁ * q
  refine ⟨f, ?_, ?_⟩
  · exact paired_original_band i x₀ y₀ x₁ y₁ n f interpolation q hn
      rfl hinterpolation hq
  intro t ht
  have hrow := (eq_div_iff (hden t ht)).mp (hrows t ht)
  dsimp [f]
  rw [map_add, map_mul, eval_nativeLineLaurent i x₀ y₀ x₁ y₁ hi t]
  linear_combination hrow

end S31.Gadgets.PcsFri.CircleLaurentUniqueness
