import S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
import Mathlib.Tactic

/-!
Gate's exact four-coefficient/two-point own-quotient degree implication.
The native four-slot source has Laurent radius two. A correct conjugate OOD
claim produces an own quotient of radius one; at every row with nonzero
denominator, both the unscaled and native-scaled row formulas evaluate that
same polynomial. This is a coefficient theorem, not an accepted-proof or
native FFT/source-commitment refinement.
-/

namespace S31.Gadgets.PcsFri.GateFourBlockOwnQuotient

open LaurentPolynomial AddMonoidAlgebra
open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.NativeCircleQuotientRows
open S31.Gadgets.PcsFri.CanonicalCircleLaurentRows

variable {F : Type*} [Field F]

def sourceAt (i c₀ c₁ c₂ c₃ : F) (t : Fˣ) : F :=
  nativeFourBlock c₀ c₁ c₂ c₃
    (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val)

def interpolationAt (i v₀ v₁ y₀ y₁ : F) (t : Fˣ) : F :=
  affineClaim v₀ v₁ y₀ y₁ (fourierY i t.val t⁻¹.val)

def denominatorAt (i x₀ y₀ x₁ y₁ : F) (t : Fˣ) : F :=
  CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
    (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val)

def ownQuotientAt (i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ : F)
    (t : Fˣ) : F :=
  (sourceAt i c₀ c₁ c₂ c₃ t - interpolationAt i v₀ v₁ y₀ y₁ t) /
    denominatorAt i x₀ y₀ x₁ y₁ t

/-- CAS05's actually computed numerator and divisor, evaluated at a base
circle row and embedded in the OOD extension. -/
def nativeScaledAt
    {E : Type*} [Field E] [Algebra F E]
    (u : E) (i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ : F)
    (t : Fˣ) : E :=
  nativeNumerator
    ((algebraMap F E) v₀) ((algebraMap F E) v₁)
    ((algebraMap F E) y₀) ((algebraMap F E) y₁) u
    ((algebraMap F E) (fourierY i t.val t⁻¹.val))
    ((algebraMap F E) (sourceAt i c₀ c₁ c₂ c₃ t)) /
      (algebraMap F E) (denominatorAt i x₀ y₀ x₁ y₁ t)

/-- The native numerator's `-2*u*y₁` factor is exact; no degree claim is
hidden in this algebraic scale conversion. -/
theorem nativeScaledAt_eq_of_ownQuotientAt
    {E : Type*} [Field E] [Algebra F E]
    (u : E) (i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ : F)
    (hy : y₁ ≠ 0) (t : Fˣ) (q : CirclePoly F)
    (hrow : ownQuotientAt i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ t =
      eval₂ (RingHom.id F) t q) :
    nativeScaledAt u i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ t =
      (-2 * u * (algebraMap F E) y₁) *
        (algebraMap F E) (eval₂ (RingHom.id F) t q) := by
  unfold nativeScaledAt
  rw [nativeQuotient_eq_scaled_own_quotient _ _ _ _ _ _ _ _
    ((map_ne_zero (algebraMap F E)).mpr hy)]
  have hinterp : affineClaim
      ((algebraMap F E) v₀) ((algebraMap F E) v₁)
      ((algebraMap F E) y₀) ((algebraMap F E) y₁)
      ((algebraMap F E) (fourierY i t.val t⁻¹.val)) =
        (algebraMap F E) (interpolationAt i v₀ v₁ y₀ y₁ t) := by
    simp [interpolationAt, affineClaim]
  rw [hinterp]
  have hmap :
      ((algebraMap F E) (sourceAt i c₀ c₁ c₂ c₃ t) -
          (algebraMap F E) (interpolationAt i v₀ v₁ y₀ y₁ t)) /
          (algebraMap F E) (denominatorAt i x₀ y₀ x₁ y₁ t) =
        (algebraMap F E)
          (ownQuotientAt i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ t) := by
    simp [ownQuotientAt]
  rw [hmap, hrow]

/-- The guarded quadratic OOD line has no zero on any base-field Fourier
row. Its Laurent line is a nonzero scalar times the quadratic minimal
polynomial; an irreducible quadratic has no base-field root. -/
theorem denominatorAt_ne_zero
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (d i x₀ y₀ x₁ y₁ : F)
    (hi : i ^ 2 = -1)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hminpoly : (minpoly F z.val).Monic)
    (hdegree : (minpoly F z.val).natDegree = 2)
    (u : E)
    (hsampledX : fourierX z.val z⁻¹.val =
      (algebraMap F E) x₀ + u * (algebraMap F E) x₁)
    (hsampledY : fourierY ((algebraMap F E) i) z.val z⁻¹.val =
      (algebraMap F E) y₀ + u * (algebraMap F E) y₁)
    (t : Fˣ) : denominatorAt i x₀ y₀ x₁ y₁ t ≠ 0 := by
  let m : Polynomial F := minpoly F z.val
  have hint : IsIntegral F z.val :=
    ⟨m, hminpoly, minpoly.aeval F z.val⟩
  have hmroot : m.eval t.val ≠ 0 := by
    intro h
    have hirr : Irreducible m := minpoly.irreducible hint
    have hmdegree : m.natDegree = 2 := hdegree
    have hdegree_ne : m.natDegree ≠ 1 := by omega
    exact (hirr.not_isRoot_of_natDegree_ne_one hdegree_ne) h
  let c : F := (-y₁ - i * x₁) / 2
  have hc : c ≠ 0 :=
    (CircleVanishingLine.fourier_edges_ne_zero
      d i x₀ y₀ x₁ y₁ hi h₀ h₁ hy).1
  have hline := CircleLaurentQuotient.native_line_scaled_minpoly
    z d i x₀ y₀ x₁ y₁ hi h₀ h₁ hy hminpoly hdegree
    (native_line_root_of_sampled_coordinates i x₀ y₀ x₁ y₁ hi
      z u hsampledX hsampledY)
  have heval := congrArg (LaurentPolynomial.eval₂ (RingHom.id F) t) hline
  have hdeneq : denominatorAt i x₀ y₀ x₁ y₁ t =
      c * m.eval t.val * (t⁻¹ : Fˣ).val := by
    unfold denominatorAt
    rw [← eval_nativeLineLaurent i x₀ y₀ x₁ y₁ hi t]
    simpa [LaurentPolynomial.eval₂_T] using heval
  rw [hdeneq]
  exact mul_ne_zero (mul_ne_zero hc hmroot) (Units.ne_zero _)

/-- For a four-slot source and its correct two-point OOD values, the
constructed own quotient lies in radius one and exactly matches every
unscaled row quotient. The row identity needs a nonzero denominator; the
native guarded OOD circle supplies that in the concrete CM31/QM31 model. -/
theorem four_block_own_quotient_degree_and_rows
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (d i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ : F)
    (hi : i ^ 2 = -1)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hminpoly : (minpoly F z.val).Monic)
    (hdegree : (minpoly F z.val).natDegree = 2)
    (u : E)
    (hsampledX : fourierX z.val z⁻¹.val =
      (algebraMap F E) x₀ + u * (algebraMap F E) x₁)
    (hsampledY : fourierY ((algebraMap F E) i) z.val z⁻¹.val =
      (algebraMap F E) y₀ + u * (algebraMap F E) y₁)
    (hnativeClaim : nativeFourBlock
      ((algebraMap F E) c₀) ((algebraMap F E) c₁)
      ((algebraMap F E) c₂) ((algebraMap F E) c₃)
      (fourierX z.val z⁻¹.val)
      (fourierY ((algebraMap F E) i) z.val z⁻¹.val) =
        (algebraMap F E) v₀ + u * (algebraMap F E) v₁) :
    ∃ q : CirclePoly F,
      InCircleBand 1 q ∧
      fourBlockLaurent i c₀ c₁ c₂ c₃ =
        interpolationLaurent i v₀ v₁ y₀ y₁ +
          nativeLineLaurent i x₀ y₀ x₁ y₁ * q ∧
      ∀ t : Fˣ, denominatorAt i x₀ y₀ x₁ y₁ t ≠ 0 →
        ownQuotientAt i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ t =
          eval₂ (RingHom.id F) t q ∧
        nativeScaledAt u i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ t =
          (-2 * u * (algebraMap F E) y₁) *
            (algebraMap F E) (eval₂ (RingHom.id F) t q) := by
  obtain ⟨q, hq, hrelation⟩ :=
    four_block_native_claim_constructs_own_quotient z d i x₀ y₀ x₁ y₁
      v₀ v₁ c₀ c₁ c₂ c₃ hi h₀ h₁ hy hminpoly hdegree
      u hsampledX hsampledY hnativeClaim
  refine ⟨q, hq, hrelation, ?_⟩
  intro t hden
  have hsource := (nativeFourBlock_eq_eval_laurent
    i c₀ c₁ c₂ c₃ hi t).symm
  have hinterp := eval_interpolationLaurent i v₀ v₁ y₀ y₁ hi t
  have hline := eval_nativeLineLaurent i x₀ y₀ x₁ y₁ hi t
  have heval := congrArg (eval₂ (RingHom.id F) t) hrelation
  simp only [map_add, map_mul] at heval
  rw [hsource, hinterp, hline] at heval
  change sourceAt i c₀ c₁ c₂ c₃ t =
    interpolationAt i v₀ v₁ y₀ y₁ t +
      denominatorAt i x₀ y₀ x₁ y₁ t * eval₂ (RingHom.id F) t q at heval
  have hrow : ownQuotientAt i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ t =
      eval₂ (RingHom.id F) t q := by
    unfold ownQuotientAt
    rw [heval]
    field_simp [hden]
    ring
  exact ⟨hrow, nativeScaledAt_eq_of_ownQuotientAt
    u i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ hy t q hrow⟩

/-- The full four-slot degree relation on *every* base Fourier row. The
denominator premise is discharged from the same quadratic OOD point and
native `y₁ ≠ 0` guard used to construct the quotient. This is still a
coefficient-model theorem: native committed rows must be shown to come from
these four ordered coefficients, and native claims/interpolation must refine
the modeled inputs. -/
theorem four_block_own_quotient_on_all_base_rows
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (d i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ : F)
    (hi : i ^ 2 = -1)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hminpoly : (minpoly F z.val).Monic)
    (hdegree : (minpoly F z.val).natDegree = 2)
    (u : E)
    (hsampledX : fourierX z.val z⁻¹.val =
      (algebraMap F E) x₀ + u * (algebraMap F E) x₁)
    (hsampledY : fourierY ((algebraMap F E) i) z.val z⁻¹.val =
      (algebraMap F E) y₀ + u * (algebraMap F E) y₁)
    (hnativeClaim : nativeFourBlock
      ((algebraMap F E) c₀) ((algebraMap F E) c₁)
      ((algebraMap F E) c₂) ((algebraMap F E) c₃)
      (fourierX z.val z⁻¹.val)
      (fourierY ((algebraMap F E) i) z.val z⁻¹.val) =
        (algebraMap F E) v₀ + u * (algebraMap F E) v₁) :
    ∃ q : CirclePoly F,
      InCircleBand 1 q ∧
      fourBlockLaurent i c₀ c₁ c₂ c₃ =
        interpolationLaurent i v₀ v₁ y₀ y₁ +
          nativeLineLaurent i x₀ y₀ x₁ y₁ * q ∧
      ∀ t : Fˣ,
        ownQuotientAt i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ t =
          eval₂ (RingHom.id F) t q ∧
        nativeScaledAt u i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ t =
          (-2 * u * (algebraMap F E) y₁) *
            (algebraMap F E) (eval₂ (RingHom.id F) t q) := by
  obtain ⟨q, hq, hrelation, hrows⟩ :=
    four_block_own_quotient_degree_and_rows z d i x₀ y₀ x₁ y₁
      v₀ v₁ c₀ c₁ c₂ c₃ hi h₀ h₁ hy hminpoly hdegree
      u hsampledX hsampledY hnativeClaim
  refine ⟨q, hq, hrelation, ?_⟩
  intro t
  exact hrows t (denominatorAt_ne_zero z d i x₀ y₀ x₁ y₁
    hi h₀ h₁ hy hminpoly hdegree u hsampledX hsampledY t)

end S31.Gadgets.PcsFri.GateFourBlockOwnQuotient
