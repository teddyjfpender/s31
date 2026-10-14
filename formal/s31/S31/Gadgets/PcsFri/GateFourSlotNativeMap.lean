import S31.Gadgets.PcsFri.GateQuotientOnlyGap
import Mathlib.Tactic

/-!
Exact coefficient map for the four native Gate source slots under the CAS07
quadratic two-point quotient. This is an all-input algebraic model, not a
verifier acceptance or probabilistic soundness theorem.
-/

namespace S31.Gadgets.PcsFri.GateFourSlotNativeMap

open S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
open S31.Gadgets.PcsFri.GateQuotientOnlyGap

variable {F : Type*} [Field F]

def claimZero (d x₀ y₀ x₁ y₁ c₀ c₁ c₂ c₃ : F) : F :=
  c₀ + c₁ * y₀ + c₂ * x₀ + c₃ * (x₀ * y₀ + d * x₁ * y₁)

def claimOne (x₀ y₀ x₁ y₁ c₁ c₂ c₃ : F) : F :=
  c₁ * y₁ + c₂ * x₁ + c₃ * (x₀ * y₁ + x₁ * y₀)

def upperNorm (x₁ y₁ : F) : F := x₁ ^ 2 + y₁ ^ 2

def quotientA (x₀ y₀ x₁ y₁ c₂ c₃ : F) : F :=
  -c₂ / y₁ + c₃ * (x₀ * y₁ - y₀ * x₁) * x₁ /
    (y₁ * upperNorm x₁ y₁)

def quotientB (x₁ y₁ c₃ : F) : F := c₃ * x₁ / upperNorm x₁ y₁

def quotientC (x₁ y₁ c₃ : F) : F := -c₃ * y₁ / upperNorm x₁ y₁

/-- The native sample guards imply that the rational map's second
denominator is nonzero. -/
theorem upperNorm_ne_zero (d x₀ y₀ x₁ y₁ : F)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0) : upperNorm x₁ y₁ ≠ 0 := by
  exact S31.Gadgets.PcsFri.CircleVanishingLine.upper_norm_ne_zero
    d x₀ y₀ x₁ y₁ h₀ h₁ hy

/-- The native four-slot polynomial evaluated at `x=x₀+u*x₁`,
`y=y₀+u*y₁`; the two listed coefficients are exact for `u²=d`. -/
theorem claim_map {E : Type*} [Field E] [Algebra F E]
    (u : E) (d x₀ y₀ x₁ y₁ c₀ c₁ c₂ c₃ : F)
    (hu : u ^ 2 = (algebraMap F E) d) :
    nativeFourBlock
      ((algebraMap F E) c₀) ((algebraMap F E) c₁)
      ((algebraMap F E) c₂) ((algebraMap F E) c₃)
      ((algebraMap F E) x₀ + u * (algebraMap F E) x₁)
      ((algebraMap F E) y₀ + u * (algebraMap F E) y₁) =
    (algebraMap F E) (claimZero d x₀ y₀ x₁ y₁ c₀ c₁ c₂ c₃) +
      u * (algebraMap F E) (claimOne x₀ y₀ x₁ y₁ c₁ c₂ c₃) := by
  simp only [nativeFourBlock, claimZero, claimOne, map_add, map_mul]
  linear_combination ((algebraMap F E) c₃ * (algebraMap F E) x₁ *
    (algebraMap F E) y₁) * hu

/-- The quotient map satisfies the exact four-slot edge-cancellation
constraint for every source coefficient tuple. -/
theorem edge_zero (x₁ y₁ c₃ : F)
    (hs : upperNorm x₁ y₁ ≠ 0) :
    edgeCorrection x₁ y₁ (quotientB x₁ y₁ c₃)
      (quotientC x₁ y₁ c₃) = 0 := by
  unfold edgeCorrection quotientB quotientC
  field_simp [hs]
  ring

/-- Exact quotient reconstruction at every base circle row. The line and
affine interpolation are exactly those used by native pairedHeight. -/
theorem reconstruction (d x₀ y₀ x₁ y₁ c₀ c₁ c₂ c₃ x y : F)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hcircle : x ^ 2 + y ^ 2 = 1) :
    nativeFourBlock c₀ c₁ c₂ c₃ x y =
      reconstructedAt x₀ y₀ x₁ y₁
        (claimZero d x₀ y₀ x₁ y₁ c₀ c₁ c₂ c₃ -
          claimOne x₀ y₀ x₁ y₁ c₁ c₂ c₃ * y₀ / y₁)
        (claimOne x₀ y₀ x₁ y₁ c₁ c₂ c₃ / y₁)
        (quotientA x₀ y₀ x₁ y₁ c₂ c₃)
        (quotientB x₁ y₁ c₃) (quotientC x₁ y₁ c₃) x y := by
  have hs := upperNorm_ne_zero d x₀ y₀ x₁ y₁ h₀ h₁ hy
  have hs' : x₁ ^ 2 + y₁ ^ 2 ≠ 0 := hs
  unfold nativeFourBlock reconstructedAt
    S31.Gadgets.PcsFri.CircleVanishingLine.nativeLine
    claimZero claimOne quotientA quotientB quotientC upperNorm
  field_simp [hy, hs']
  linear_combination (c₃ * x₁ * y₁ ^ 2) * hcircle -
    (c₃ * x₁ * y₁ ^ 2) * h₀ -
    (2 * c₃ * x₁ * y₁ * (y - y₀)) * h₁

/-- At a row where the native denominator is invertible, the own quotient is
exactly the affine polynomial given by the coefficient map. The native
numerator is this value scaled by `-2*u*y₁`; see
`GateFourBlockOwnQuotient.nativeScaledAt_eq_of_ownQuotientAt`. -/
theorem own_quotient_at_row (d x₀ y₀ x₁ y₁ c₀ c₁ c₂ c₃ x y : F)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hcircle : x ^ 2 + y ^ 2 = 1)
    (hden : S31.Gadgets.PcsFri.CircleVanishingLine.nativeLine
      x₀ y₀ x₁ y₁ x y ≠ 0) :
    (nativeFourBlock c₀ c₁ c₂ c₃ x y -
      (claimZero d x₀ y₀ x₁ y₁ c₀ c₁ c₂ c₃ +
        claimOne x₀ y₀ x₁ y₁ c₁ c₂ c₃ * (y - y₀) / y₁)) /
      S31.Gadgets.PcsFri.CircleVanishingLine.nativeLine
        x₀ y₀ x₁ y₁ x y =
      quotientA x₀ y₀ x₁ y₁ c₂ c₃ +
        quotientB x₁ y₁ c₃ * x + quotientC x₁ y₁ c₃ * y := by
  rw [reconstruction d x₀ y₀ x₁ y₁ c₀ c₁ c₂ c₃ x y h₀ h₁ hy hcircle]
  unfold reconstructedAt
  field_simp [hy, hden]
  ring

end S31.Gadgets.PcsFri.GateFourSlotNativeMap
