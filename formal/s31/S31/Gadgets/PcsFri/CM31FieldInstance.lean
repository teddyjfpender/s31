import S31.Gadgets.Air.QuadField
import S31.Gadgets.PcsFri.ConcreteCM31Tower
import S31.Gadgets.PcsFri.OodGuardFiniteCount
import S31.Gadgets.PcsFri.PairedTowerCircle
import Mathlib.Algebra.Field.TransferInstance

/-!
The modeled native CM31 coefficient pair is isomorphic to the quadratic
field already used by the AIR formalization.  This is an algebraic bridge:
it does not identify Zig machine operations with these definitions.
-/

namespace S31.Gadgets.PcsFri.CM31FieldInstance

open NativeTowerFormulas

abbrev F := S31.Field.F
abbrev CM31 := CM F

/-- The coordinates of the native-shaped CM31 pair are the coordinates of
the AIR's quadratic algebra, with `i² = -1`. -/
def toQuadratic : CM31 ≃ S31.Gadgets.Air.QuadField.CM where
  toFun x := ⟨x.a, x.b⟩
  invFun x := ⟨x.re, x.im⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; cases x; rfl

noncomputable instance : Field CM31 := toQuadratic.field
noncomputable instance : DecidableEq CM31 := Classical.decEq _

instance : NeZero (2 : CM31) := ⟨by
  intro h
  have ha := congrArg CM.a h
  change (2 : F) = 0 at ha
  exact (show (2 : F) ≠ 0 from by decide) ha⟩

theorem add_eq_cmAdd (x y : CM31) : x + y = cmAdd x y := by
  ext <;> rfl

theorem mul_eq_cmMul (x y : CM31) : x * y = cmMul x y := by
  change toQuadratic.symm (toQuadratic x * toQuadratic y) = cmMul x y
  ext <;> dsimp [toQuadratic, cmMul, QuadraticAlgebra.instMul] <;> ring

theorem square_eq_cmSquare (x : CM31) : x ^ 2 = cmSquare x := by
  rw [pow_two, mul_eq_cmMul, cm_square_eq_mul]

theorem imaginary_square : (⟨0, 1⟩ : CM31) ^ 2 = -1 := by
  rw [square_eq_cmSquare]
  change (⟨-1, 0⟩ : CM31) = toQuadratic.symm (-1)
  ext <;> rfl

theorem r_nonsquare (x : CM31) : x ^ 2 ≠ (r : CM31) := by
  rw [square_eq_cmSquare]
  exact ConcreteCM31Tower.r_nonsquare_cm31 x

/-- Membership in the counted support is exactly the algebraic rational-map
admission predicate, including the rejection of singular seeds. -/
theorem accepted_guard_iff_cm31 (z : CM31 × CM31) :
    z ∈ OodGuardFiniteCount.acceptedGuard (r : CM31) ↔
      OodGuardFiniteCount.denominatorNorm (r : CM31) z.1 z.2 ≠ 0 ∧
      OodGuardFiniteCount.yUpper (r : CM31) z.1 z.2 ≠ 0 := by
  classical
  exact OodGuardFiniteCount.accepted_guard_iff
    (r : CM31) (⟨0, 1⟩ : CM31) r_nonsquare imaginary_square z

/-- The actual modeled CM31 field instantiates the generic conic count and
the CAS05 upper-coordinate guard with `R = 2+i`. -/
theorem accepted_guard_card_cm31 :
    (OodGuardFiniteCount.acceptedGuard (r : CM31)).card =
      (2147483647 ^ 2 - 1) ^ 2 := by
  classical
  rw [OodGuardFiniteCount.accepted_guard_card (r : CM31) (⟨0, 1⟩ : CM31)
    r_nonsquare imaginary_square, ConcreteCM31Tower.card_cm31]

theorem excluded_regular_card_cm31 :
    (OodGuardFiniteCount.excludedRegular (r : CM31)).card =
      2 * (2147483647 ^ 2) - 3 := by
  classical
  rw [OodGuardFiniteCount.excluded_regular_card (r : CM31) (⟨0, 1⟩ : CM31)
    r_nonsquare imaginary_square, ConcreteCM31Tower.card_cm31]

/-- The generic all-row determinant theorem now has its nonsquare premise
discharged for the concrete modeled M31/CM31 tower. -/
theorem denominator_ne_zero_cm31
    (x y : PairedTowerCircle.Pair CM31) (a b : CM31)
    (hcircle : PairedTowerCircle.add
      (PairedTowerCircle.square (r : CM31) x)
      (PairedTowerCircle.square (r : CM31) y) = PairedTowerCircle.one)
    (hbase : a ^ 2 + b ^ 2 = 1)
    (hguard : y.c1 ≠ 0) :
    (x.c0 - a) * y.c1 - (y.c0 - b) * x.c1 ≠ 0 :=
  PairedTowerCircle.denominator_ne_zero_of_pair_circle
    (r : CM31) x y a b r_nonsquare hcircle hbase hguard

end S31.Gadgets.PcsFri.CM31FieldInstance
