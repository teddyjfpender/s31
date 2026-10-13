import S31.Gadgets.PcsFri.CM31FieldInstance
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

end S31.Gadgets.PcsFri.QM31FieldInstance
