import S31.Gadgets.PcsFri.CM31FieldInstance
import S31.Gadgets.PcsFri.NativeTowerInverse
import Mathlib.Algebra.Field.TransferInstance

/-!
The native-shaped four-coordinate QM31 model is the same quadratic tower as
the AIR's QM31 field model. This transfers field laws to the coefficient
structure; it is an algebraic model, not a semantics for compiled Zig.
-/

namespace S31.Gadgets.PcsFri.QM31FieldInstance

open NativeTowerFormulas

abbrev F := S31.Field.F
abbrev CM31 := CM F
abbrev QM31 := QM F

def toQuadratic : QM31 ≃ S31.Gadgets.Air.QuadField.QM where
  toFun x := ⟨⟨x.c0.a, x.c0.b⟩, ⟨x.c1.a, x.c1.b⟩⟩
  invFun x := ⟨⟨x.re.re, x.re.im⟩, ⟨x.im.re, x.im.im⟩⟩
  left_inv := by intro x; cases x with | mk a b => cases a; cases b; rfl
  right_inv := by intro x; cases x with | mk a b => cases a; cases b; rfl

noncomputable instance : Field QM31 := toQuadratic.field

theorem add_eq_qmAdd (x y : QM31) : x + y = qmAdd x y := by
  ext <;> rfl

theorem one_eq_qmOne : (1 : QM31) = qmOne := by
  ext <;> rfl

theorem square_eq_qmSquare (x : QM31) : x ^ 2 = qmSquare x := by
  apply toQuadratic.injective
  change (toQuadratic x) ^ 2 = toQuadratic (qmSquare x)
  rw [pow_two]
  ext <;>
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;>
    dsimp [toQuadratic, qmSquare, cmAdd, cmSquare, cmMulByR,
      cmMul, S31.Gadgets.Air.QuadField.twoPlusI] <;>
    ring

/-- A field-level circle equation entails each of the four native-shaped
coefficient equations. The premise is still about the algebraic model. -/
theorem circle_coefficients_of_field (x y : QM31)
    (hcircle : x ^ 2 + y ^ 2 = 1) :
    (qmSquare x).c0.a + (qmSquare y).c0.a = 1 ∧
    (qmSquare x).c0.b + (qmSquare y).c0.b = 0 ∧
    (qmSquare x).c1.a + (qmSquare y).c1.a = 0 ∧
    (qmSquare x).c1.b + (qmSquare y).c1.b = 0 := by
  have hnative : qmAdd (qmSquare x) (qmSquare y) = qmOne := by
    rw [← square_eq_qmSquare, ← square_eq_qmSquare,
      ← add_eq_qmAdd, ← one_eq_qmOne]
    exact hcircle
  exact circle_coefficient_equations x y hnative

def toPair (x : QM31) : PairedTowerCircle.Pair CM31 := ⟨x.c0, x.c1⟩

theorem toPair_add (x y : QM31) :
    toPair (x + y) = PairedTowerCircle.add (toPair x) (toPair y) := by
  rw [add_eq_qmAdd]
  apply NativeTowerInverse.pair_ext
  · exact (CM31FieldInstance.add_eq_cmAdd x.c0 y.c0).symm
  · exact (CM31FieldInstance.add_eq_cmAdd x.c1 y.c1).symm

theorem toPair_one :
    toPair (1 : QM31) = PairedTowerCircle.one := by
  rw [one_eq_qmOne]
  rfl

theorem toPair_square (x : QM31) :
    toPair (x ^ 2) = PairedTowerCircle.square (r : CM31) (toPair x) := by
  rw [square_eq_qmSquare]
  apply NativeTowerInverse.pair_ext
  · change cmAdd (cmSquare x.c0) (cmMulByR (cmSquare x.c1)) =
      x.c0 ^ 2 + (r : CM31) * x.c1 ^ 2
    rw [CM31FieldInstance.square_eq_cmSquare x.c0,
      CM31FieldInstance.square_eq_cmSquare x.c1,
      CM31FieldInstance.add_eq_cmAdd]
    rw [cm_mul_by_r, ← CM31FieldInstance.mul_eq_cmMul,
      mul_comm (cmSquare x.c1) r]
  · change cmAdd (cmMul x.c0 x.c1) (cmMul x.c0 x.c1) =
      2 * x.c0 * x.c1
    rw [← CM31FieldInstance.add_eq_cmAdd,
      ← CM31FieldInstance.mul_eq_cmMul]
    ring

/-- A genuine modeled QM31 circle point with the native upper-coordinate
guard has a nonzero paired quotient denominator at every base-circle row. -/
theorem denominator_ne_zero_of_field_circle (x y : QM31) (a b : CM31)
    (hcircle : x ^ 2 + y ^ 2 = 1)
    (hbase : a ^ 2 + b ^ 2 = 1)
    (hguard : y.c1 ≠ 0) :
    (x.c0 - a) * y.c1 - (y.c0 - b) * x.c1 ≠ 0 := by
  have hpair : PairedTowerCircle.add
      (PairedTowerCircle.square (r : CM31) (toPair x))
      (PairedTowerCircle.square (r : CM31) (toPair y)) =
      PairedTowerCircle.one := by
    rw [← toPair_square, ← toPair_square, ← toPair_add,
      ← toPair_one, hcircle]
  exact CM31FieldInstance.denominator_ne_zero_cm31
    (toPair x) (toPair y) a b hpair hbase hguard

end S31.Gadgets.PcsFri.QM31FieldInstance
