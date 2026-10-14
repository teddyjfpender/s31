import S31.Gadgets.PcsFri.GateFourBlockOwnQuotient
import Mathlib.Tactic

/-!
An exact Gate-sized circle-code obstruction for quotient-only degree testing.
The M31-valued source `x²` is outside the first four native circle-basis
slots `1,y,x,xy`, while a correct guarded two-point claim gives it an own
quotient in the same radius-one Laurent band as honest four-slot sources.
This is an algebraic separation, not an accepting native proof or a security
attack: the paper's circle-code filtration and FRI acceptance remain open.
-/

namespace S31.Gadgets.PcsFri.GateQuotientOnlyGap

open LaurentPolynomial AddMonoidAlgebra
open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.NativeCircleQuotientRows
open S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
open S31.Gadgets.PcsFri.GateFourBlockOwnQuotient

variable {F : Type*} [Field F]

/-- Every first-four-slot circle polynomial has equal sums on the two
opposite cardinal pairs. All nonconstant terms cancel in both sums. -/
theorem native_four_block_cardinal_invariant (c₀ c₁ c₂ c₃ : F) :
    nativeFourBlock c₀ c₁ c₂ c₃ 1 0 +
      nativeFourBlock c₀ c₁ c₂ c₃ (-1) 0 =
    nativeFourBlock c₀ c₁ c₂ c₃ 0 1 +
      nativeFourBlock c₀ c₁ c₂ c₃ 0 (-1) := by
  unfold nativeFourBlock
  ring

/-- `x²` violates the four-slot invariant in every field of odd
characteristic, even though all four witness points lie on the circle. -/
theorem x_square_not_native_four_block [NeZero (2 : F)] :
    ¬ ∃ c₀ c₁ c₂ c₃ : F,
      ∀ x y : F, x ^ 2 + y ^ 2 = 1 →
        nativeFourBlock c₀ c₁ c₂ c₃ x y = x ^ 2 := by
  rintro ⟨c₀, c₁, c₂, c₃, h⟩
  have h₁ := h 1 0 (by norm_num)
  have h₂ := h (-1) 0 (by norm_num)
  have h₃ := h 0 1 (by norm_num)
  have h₄ := h 0 (-1) (by norm_num)
  have hinvariant := native_four_block_cardinal_invariant c₀ c₁ c₂ c₃
  rw [h₁, h₂, h₃, h₄] at hinvariant
  have htwo : (2 : F) = 0 := by
    calc
      (2 : F) = 1 + 1 := by ring
      _ = 0 := by simpa using hinvariant
  exact (NeZero.ne (2 : F)) htwo

/-- The five coordinates obtained by reconstructing from an affine
own quotient. `i₀+i₁*y` is the two-point interpolation line, and the
remaining factor is exactly the native circle denominator. -/
def reconstructedAt (x₀ y₀ x₁ y₁ i₀ i₁ a b c x y : F) : F :=
  i₀ + i₁ * y +
    CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁ x y *
      (a + b * x + c * y)

def edgeCorrection (x₁ y₁ b c : F) : F := y₁ * b + x₁ * c

/-- The quotient-only reconstruction occupies five circle-basis slots.
The extra `x²` coefficient is the negative of one explicit linear form
in the quotient's `x,y` coefficients. -/
theorem reconstructed_five_slot (x₀ y₀ x₁ y₁ i₀ i₁ a b c x y : F)
    (hcircle : x ^ 2 + y ^ 2 = 1) :
    reconstructedAt x₀ y₀ x₁ y₁ i₀ i₁ a b c x y =
      nativeFourBlock
        (i₀ + (x₀ * y₁ - y₀ * x₁) * a + x₁ * c)
        (i₁ + (x₀ * y₁ - y₀ * x₁) * c + x₁ * a)
        ((x₀ * y₁ - y₀ * x₁) * b - y₁ * a)
        (x₁ * b - y₁ * c) x y -
        edgeCorrection x₁ y₁ b c * x ^ 2 := by
  unfold reconstructedAt CircleVanishingLine.nativeLine nativeFourBlock
    edgeCorrection
  linear_combination (x₁ * c) * hcircle

/-- A four-slot source satisfies the exact cardinal-pair invariant. The
reconstructed source violates it by `-2*(y₁*b+x₁*c)` unless the fifth
coordinate cancels. -/
theorem reconstructed_cardinal_gap (x₀ y₀ x₁ y₁ i₀ i₁ a b c : F) :
    reconstructedAt x₀ y₀ x₁ y₁ i₀ i₁ a b c 1 0 +
      reconstructedAt x₀ y₀ x₁ y₁ i₀ i₁ a b c (-1) 0 -
      reconstructedAt x₀ y₀ x₁ y₁ i₀ i₁ a b c 0 1 -
      reconstructedAt x₀ y₀ x₁ y₁ i₀ i₁ a b c 0 (-1) =
        -2 * edgeCorrection x₁ y₁ b c := by
  unfold reconstructedAt CircleVanishingLine.nativeLine edgeCorrection
  ring

/-- Exact quotient-only degree-correction criterion for this Gate-sized
algebraic model. A radius-one quotient `a+b*x+c*y` reconstructs a four-slot
source iff the single edge-cancellation equation `y₁*b+x₁*c=0` holds.
This is a candidate extra relation, not a check implemented by the native
verifier or a probabilistic soundness theorem. -/
theorem reconstructed_in_four_slots_iff [NeZero (2 : F)]
    (x₀ y₀ x₁ y₁ i₀ i₁ a b c : F) :
    (∃ c₀ c₁ c₂ c₃ : F,
      ∀ x y : F, x ^ 2 + y ^ 2 = 1 →
        reconstructedAt x₀ y₀ x₁ y₁ i₀ i₁ a b c x y =
          nativeFourBlock c₀ c₁ c₂ c₃ x y) ↔
      edgeCorrection x₁ y₁ b c = 0 := by
  constructor
  · rintro ⟨c₀, c₁, c₂, c₃, h⟩
    have h₁ := h 1 0 (by norm_num)
    have h₂ := h (-1) 0 (by norm_num)
    have h₃ := h 0 1 (by norm_num)
    have h₄ := h 0 (-1) (by norm_num)
    have hinvariant := native_four_block_cardinal_invariant c₀ c₁ c₂ c₃
    rw [← h₁, ← h₂, ← h₃, ← h₄] at hinvariant
    have hgap := reconstructed_cardinal_gap x₀ y₀ x₁ y₁ i₀ i₁ a b c
    have hzero : -2 * edgeCorrection x₁ y₁ b c = 0 := by
      rw [← hgap]
      linear_combination hinvariant
    exact (mul_eq_zero.mp hzero).resolve_left (neg_ne_zero.mpr (NeZero.ne (2 : F)))
  · intro hcancel
    refine ⟨i₀ + (x₀ * y₁ - y₀ * x₁) * a + x₁ * c,
      i₁ + (x₀ * y₁ - y₀ * x₁) * c + x₁ * a,
      (x₀ * y₁ - y₀ * x₁) * b - y₁ * a,
      x₁ * b - y₁ * c, ?_⟩
    intro x y hcircle
    rw [reconstructed_five_slot _ _ _ _ _ _ _ _ _ _ _ hcircle, hcancel]
    ring

/-- An M31 base-field source can use `x²`; in Fourier coordinates it is a
finite Laurent polynomial of radius two. -/
noncomputable def xSquareLaurent (i : F) : CirclePoly F :=
  xLaurent i * xLaurent i

theorem xSquare_in_band_two (i : F) :
    InCircleBand 2 (xSquareLaurent i) := by
  exact line_mul_band i 0 0 0 (-1) 1 (xLaurent i)
    (line_in_band_one i 0 0 0 (-1))

theorem eval_xSquareLaurent (i : F) (hi : i ^ 2 = -1)
    (t : Fˣ) :
    eval₂ (RingHom.id F) t (xSquareLaurent i) =
      (fourierX t.val t⁻¹.val) ^ 2 := by
  simp [xSquareLaurent, eval_xLaurent i hi t, pow_two]

theorem eval_xSquareLaurent_algebra [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i : F) (hi : i ^ 2 = -1) (z : Eˣ) :
    eval₂ (algebraMap F E) z (xSquareLaurent i) =
      (fourierX z.val z⁻¹.val) ^ 2 := by
  simp [xSquareLaurent, eval_xLaurent_algebra i hi z, pow_two]

/-- The same guarded OOD premises as the native quotient line give an own
quotient of radius one for `x²`, provided the claim is its real OOD value.
Thus the broad Laurent radius test alone cannot enforce four-slot source
membership. The quotient and source remain coefficient objects here. -/
theorem x_square_correct_claim_has_radius_one_quotient
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (d i x₀ y₀ x₁ y₁ v₀ v₁ : F)
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
    (hclaim : (fourierX z.val z⁻¹.val) ^ 2 =
      (algebraMap F E) v₀ + u * (algebraMap F E) v₁) :
    ∃ q : CirclePoly F,
      InCircleBand 1 q ∧
      xSquareLaurent i = interpolationLaurent i v₀ v₁ y₀ y₁ +
        nativeLineLaurent i x₀ y₀ x₁ y₁ * q ∧
      ∀ t : Fˣ,
        eval₂ (RingHom.id F) t q =
          ((fourierX t.val t⁻¹.val) ^ 2 -
            affineClaim v₀ v₁ y₀ y₁ (fourierY i t.val t⁻¹.val)) /
          CircleVanishingLine.nativeLine x₀ y₀ x₁ y₁
            (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) := by
  obtain ⟨q, hq, hrelation⟩ :=
    native_claim_constructs_circle_quotient z 2 (by omega)
      d i x₀ y₀ x₁ y₁ v₀ v₁ hi h₀ h₁ hy hminpoly hdegree
      u hsampledX hsampledY (xSquareLaurent i)
      (xSquare_in_band_two i)
      (by rw [eval_xSquareLaurent_algebra i hi z]; exact hclaim)
  refine ⟨q, hq, hrelation, ?_⟩
  intro t
  have hden := denominatorAt_ne_zero z d i x₀ y₀ x₁ y₁
    hi h₀ h₁ hy hminpoly hdegree u hsampledX hsampledY t
  have hrow := paired_row_quotient_eq i x₀ y₀ x₁ y₁ hi t
    (xSquareLaurent i) (interpolationLaurent i v₀ v₁ y₀ y₁) q
    hrelation hden
  simpa only [eval_xSquareLaurent i hi t,
    eval_interpolationLaurent i v₀ v₁ y₀ y₁ hi t] using hrow

end S31.Gadgets.PcsFri.GateQuotientOnlyGap
