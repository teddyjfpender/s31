import Mathlib.Tactic

/-!
The field-valued operation performed by one native FRI butterfly.  Native
`ibutterfly` deliberately omits division by two, so an affine polynomial
evaluated at `x` and `-x` folds to twice its value at the challenge.
This model assumes that the coordinate supplied by the domain is nonzero.
-/

namespace S31.Gadgets.PcsFri.FoldAlgebra

variable {F : Type*} [Field F]

def pairFold (alpha invCoord left right : F) : F :=
  (left + right) + alpha * ((left - right) * invCoord)

theorem pairFold_affine (c₀ c₁ alpha x : F) (hx : x ≠ 0) :
    pairFold alpha x⁻¹ (c₀ + x * c₁) (c₀ - x * c₁) =
      2 * (c₀ + alpha * c₁) := by
  unfold pairFold
  field_simp [hx]
  ring

def circleAccumulate (previous alpha invY left right : F) : F :=
  previous * alpha ^ 2 + pairFold alpha invY left right

theorem circleAccumulate_affine (previous c₀ c₁ alpha y : F) (hy : y ≠ 0) :
    circleAccumulate previous alpha y⁻¹ (c₀ + y * c₁) (c₀ - y * c₁) =
      previous * alpha ^ 2 + 2 * (c₀ + alpha * c₁) := by
  simp [circleAccumulate, pairFold_affine c₀ c₁ alpha y hy]

def challengeAt (alpha : F) (step : Nat) : F := alpha ^ (2 ^ step)

theorem challengeAt_succ (alpha : F) (step : Nat) :
    challengeAt alpha (step + 1) = (challengeAt alpha step) ^ 2 := by
  simp [challengeAt, pow_succ, pow_mul]

end S31.Gadgets.PcsFri.FoldAlgebra
