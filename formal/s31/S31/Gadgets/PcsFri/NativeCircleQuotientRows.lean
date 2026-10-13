import S31.Gadgets.PcsFri.CircleLaurentQuotient
import S31.Gadgets.PcsFri.QM31FieldInstance
import Mathlib.Tactic

/-!
CAS05's native conjugate interpolation numerator and two-row quotient in the
finite Laurent circle model. The native source locations and the remaining
commitment and basis gaps are recorded in
`design/s31/security/PCS_FRI_CAS05_NATIVE_CIRCLE_REFINEMENT.md`.
-/

namespace S31.Gadgets.PcsFri.NativeCircleQuotientRows

open LaurentPolynomial AddMonoidAlgebra
open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.CircleLaurentQuotient

variable {F : Type*} [Field F]

/-- The CM31 affine line interpolating a QM31 claim `v₀+u v₁` at the sampled
point whose y-coordinate is `y₀+u y₁`. The native guard is `y₁ ≠ 0`. -/
def affineClaim (v₀ v₁ y₀ y₁ rowY : F) : F :=
  v₀ + (v₁ / y₁) * (rowY - y₀)

theorem affineClaim_at_sample (v₀ v₁ y₀ y₁ u : F) (hy : y₁ ≠ 0) :
    affineClaim v₀ v₁ y₀ y₁ (y₀ + u * y₁) = v₀ + u * v₁ := by
  unfold affineClaim
  field_simp [hy]
  ring

/-- This spells out the three native `LineCoeffs` before its `alpha=1`
specialization: `a=v'-v`, `c=y'-y`, `b=v*c-a*y`. -/
def nativeNumerator (v₀ v₁ y₀ y₁ u rowY rowValue : F) : F :=
  let value := v₀ + u * v₁
  let conjugateValue := v₀ - u * v₁
  let sampleY := y₀ + u * y₁
  let conjugateY := y₀ - u * y₁
  let a := conjugateValue - value
  let c := conjugateY - sampleY
  let b := value * c - a * sampleY
  c * rowValue - a * rowY - b

/-- Native QM31 numerator is the CM31 interpolation residual multiplied by
`-2*u*y₁`. No tower-square equation is needed: the `u²` terms cancel. -/
theorem nativeNumerator_eq_scaled_residual
    (v₀ v₁ y₀ y₁ u rowY rowValue : F) (hy : y₁ ≠ 0) :
    nativeNumerator v₀ v₁ y₀ y₁ u rowY rowValue =
      (-2 * u * y₁) * (rowValue - affineClaim v₀ v₁ y₀ y₁ rowY) := by
  unfold nativeNumerator affineClaim
  field_simp [hy]
  ring

theorem nativeQuotient_eq_scaled_own_quotient
    (v₀ v₁ y₀ y₁ u rowY rowValue denominator : F)
    (hy : y₁ ≠ 0) :
    nativeNumerator v₀ v₁ y₀ y₁ u rowY rowValue / denominator =
      (-2 * u * y₁) *
        ((rowValue - affineClaim v₀ v₁ y₀ y₁ rowY) / denominator) := by
  rw [nativeNumerator_eq_scaled_residual _ _ _ _ _ _ _ hy]
  ring

/-- Fourier y-coordinate as a degree-one circle Laurent polynomial. The
specialized native line equals y because `nativeLine 0 0 1 0 a b = b`. -/
noncomputable def yLaurent (i : F) : CirclePoly F :=
  nativeLineLaurent i 0 0 1 0

/-- The actual native interpolation line represented in the same coefficient
model as `CircleLaurentQuotient`. -/
noncomputable def interpolationLaurent (i v₀ v₁ y₀ y₁ : F) : CirclePoly F :=
  C (v₀ - (v₁ / y₁) * y₀) + C (v₁ / y₁) * yLaurent i

theorem eval_yLaurent (i : F) (hi : i ^ 2 = -1) (t : Fˣ) :
    eval₂ (RingHom.id F) t (yLaurent i) = fourierY i t.val t⁻¹.val := by
  rw [yLaurent, eval_nativeLineLaurent i 0 0 1 0 hi t]
  simp [CircleVanishingLine.nativeLine]

theorem eval_interpolationLaurent (i v₀ v₁ y₀ y₁ : F)
    (hi : i ^ 2 = -1) (t : Fˣ) :
    eval₂ (RingHom.id F) t (interpolationLaurent i v₀ v₁ y₀ y₁) =
      affineClaim v₀ v₁ y₀ y₁ (fourierY i t.val t⁻¹.val) := by
  simp only [interpolationLaurent, map_add, map_mul, LaurentPolynomial.eval₂_C,
    eval_yLaurent i hi t, RingHom.id_apply]
  unfold affineClaim
  ring

theorem constant_in_band_one (c : F) :
    InCircleBand 1 (C c : CirclePoly F) := by
  intro k hk
  by_contra hband
  have hk0 : k ≠ 0 := by omega
  exact hk (by simp [LaurentPolynomial.C_apply, hk0])

theorem scale_in_band_one (c : F) (f : CirclePoly F)
    (hf : InCircleBand 1 f) : InCircleBand 1 (C c * f) := by
  intro k hk
  have hfne : f k ≠ 0 := by
    intro hz
    apply hk
    rw [← LaurentPolynomial.smul_eq_C_mul]
    simp [hz]
  exact hf k hfne

/-- The native affine interpolation is genuinely radius one in the Laurent
filtration; no source degree bound is assumed. -/
theorem interpolation_in_band_one (i v₀ v₁ y₀ y₁ : F) :
    InCircleBand 1 (interpolationLaurent i v₀ v₁ y₀ y₁) := by
  unfold interpolationLaurent
  apply band_add
  · exact constant_in_band_one _
  · exact scale_in_band_one _ _ (line_in_band_one i 0 0 1 0)

theorem eval_yLaurent_algebra
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i : F) (hi : i ^ 2 = -1) (z : Eˣ) :
    eval₂ (algebraMap F E) z (yLaurent i) =
      fourierY ((algebraMap F E) i) z.val z⁻¹.val := by
  have hiE : ((algebraMap F E) i) ^ 2 = -1 := by
    rw [← map_pow, hi]
    simp
  have hiE0 : (algebraMap F E) i ≠ 0 := by
    intro hz
    simp [hz] at hiE
  have htwo : (2 : E) ≠ 0 := by
    have hmap : (algebraMap F E) (2 : F) ≠ 0 :=
      (map_ne_zero (algebraMap F E)).mpr (NeZero.ne (2 : F))
    simpa only [_root_.map_ofNat] using hmap
  simp [yLaurent, nativeLineLaurent, fourierY]
  rw [show (algebraMap F E) (2 : F) = (2 : E) by
    exact _root_.map_ofNat (algebraMap F E) 2]
  field_simp [hiE0, htwo]
  rw [hiE]
  ring

/-- Extension-field evaluation of the concrete CM31 interpolation polynomial.
The statement uses only algebra-map field laws; native QM31 representation
refinement remains outside this theorem. -/
theorem eval_interpolation_algebra
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i v₀ v₁ y₀ y₁ : F) (hi : i ^ 2 = -1) (z : Eˣ) :
    eval₂ (algebraMap F E) z (interpolationLaurent i v₀ v₁ y₀ y₁) =
      affineClaim ((algebraMap F E) v₀) ((algebraMap F E) v₁)
        ((algebraMap F E) y₀) ((algebraMap F E) y₁)
        (fourierY ((algebraMap F E) i) z.val z⁻¹.val) := by
  have hmap : (algebraMap F E) (v₁ / y₁) =
      (algebraMap F E) v₁ / (algebraMap F E) y₁ :=
    by simp
  simp only [interpolationLaurent, map_add, map_mul,
    LaurentPolynomial.eval₂_C, eval_yLaurent_algebra i hi z]
  unfold affineClaim
  simp only [_root_.map_sub, _root_.map_mul, hmap]
  ring

/-- A concrete claim `v₀+u*v₁` at OOD y-coordinate `y₀+u*y₁` is exactly the
evaluation of the degree-one Laurent interpolation polynomial. -/
theorem interpolation_at_ood
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i v₀ v₁ y₀ y₁ : F) (hi : i ^ 2 = -1)
    (hy : y₁ ≠ 0) (z : Eˣ) (u : E)
    (hsampledY : fourierY ((algebraMap F E) i) z.val z⁻¹.val =
      (algebraMap F E) y₀ + u * (algebraMap F E) y₁) :
    eval₂ (algebraMap F E) z (interpolationLaurent i v₀ v₁ y₀ y₁) =
      (algebraMap F E) v₀ + u * (algebraMap F E) v₁ := by
  rw [eval_interpolation_algebra i v₀ v₁ y₀ y₁ hi z, hsampledY]
  exact affineClaim_at_sample _ _ _ _ _
    ((map_ne_zero (algebraMap F E)).mpr hy)

/-- The modeled native line's extension evaluation is the same line equation
used by CAS05's denominator, at the Fourier circle coordinates. -/
theorem eval_nativeLine_algebra
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i x₀ y₀ x₁ y₁ : F) (hi : i ^ 2 = -1) (z : Eˣ) :
    eval₂ (algebraMap F E) z (nativeLineLaurent i x₀ y₀ x₁ y₁) =
      CircleVanishingLine.nativeLine
        ((algebraMap F E) x₀) ((algebraMap F E) y₀)
        ((algebraMap F E) x₁) ((algebraMap F E) y₁)
        (fourierX z.val z⁻¹.val)
        (fourierY ((algebraMap F E) i) z.val z⁻¹.val) := by
  have hiE : ((algebraMap F E) i) ^ 2 = -1 := by
    rw [← map_pow, hi]
    simp
  rw [nativeLine_fourier ((algebraMap F E) i)
    ((algebraMap F E) x₀) ((algebraMap F E) y₀)
    ((algebraMap F E) x₁) ((algebraMap F E) y₁)
    z.val z⁻¹.val hiE]
  simp [nativeLineLaurent]
  rw [show (algebraMap F E) (2 : F) = (2 : E) by
    exact _root_.map_ofNat (algebraMap F E) 2]

theorem native_line_root_of_sampled_coordinates
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i x₀ y₀ x₁ y₁ : F) (hi : i ^ 2 = -1)
    (z : Eˣ) (u : E)
    (hx : fourierX z.val z⁻¹.val =
      (algebraMap F E) x₀ + u * (algebraMap F E) x₁)
    (hy : fourierY ((algebraMap F E) i) z.val z⁻¹.val =
      (algebraMap F E) y₀ + u * (algebraMap F E) y₁) :
    eval₂ (algebraMap F E) z (nativeLineLaurent i x₀ y₀ x₁ y₁) = 0 := by
  rw [eval_nativeLine_algebra i x₀ y₀ x₁ y₁ hi z, hx, hy]
  unfold CircleVanishingLine.nativeLine
  ring

/-- From the native conjugate claim and sampled Fourier circle coordinates to
the *constructed* own quotient in the coefficient model. The line root is
derived from the sampled coordinates; source band and quadratic minimal
polynomial still require separate certificates. -/
theorem native_claim_constructs_circle_quotient
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (n : ℕ) (hn : 1 ≤ n)
    (d i x₀ y₀ x₁ y₁ v₀ v₁ : F)
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
    (f : CirclePoly F) (hf : InCircleBand n f)
    (hclaim : eval₂ (algebraMap F E) z f =
      (algebraMap F E) v₀ + u * (algebraMap F E) v₁) :
    ∃ q : CirclePoly F,
      InCircleBand (n - 1) q ∧
      f = interpolationLaurent i v₀ v₁ y₀ y₁ +
        nativeLineLaurent i x₀ y₀ x₁ y₁ * q := by
  apply native_circle_quotient_exists z n hn d i x₀ y₀ x₁ y₁
    hi h₀ h₁ hy hminpoly hdegree
    (native_line_root_of_sampled_coordinates i x₀ y₀ x₁ y₁ hi
      z u hsampledX hsampledY) f
    (interpolationLaurent i v₀ v₁ y₀ y₁) hf
    (interpolation_in_band_one i v₀ v₁ y₀ y₁)
  rw [hclaim, interpolation_at_ood i v₀ v₁ y₀ y₁ hi hy z u hsampledY]

end S31.Gadgets.PcsFri.NativeCircleQuotientRows
