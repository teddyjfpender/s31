import S31.Gadgets.PcsFri.PairedBatchSourceBinding
import S31.Gadgets.PcsFri.ConcreteCircleCount
import Mathlib.Tactic

/-!
Local algebraic refinement of the experimental CAS05 paired sparse row.
The model follows `transposed_paired_sparse.zig` at draft commit
`234ac67b2819e6b102e8d43da93a38a4a902075e`. It does not interpret Zig
execution, authenticate the source opening, or prove a PCS security bound.
-/

namespace S31.Gadgets.PcsFri.PairedBatchNativeRefinement

open S31.Gadgets.PcsFri.NativeTowerFormulas
open S31.Gadgets.PcsFri.PairedProtocolRecurrence
open S31.Gadgets.PcsFri.PairedBatchSourceBinding

abbrev M31 := S31.Field.F
abbrev CM31 := CM M31
abbrev QM31 := QM M31

noncomputable def fromCM (x : CM31) : QM31 := ConcreteCircleCount.embedCM x
noncomputable def fromBase (x : M31) : QM31 := fromCM ⟨x, 0⟩

theorem fromBase_eq_native_shape (x : M31) :
    fromBase x = qmFromBase x := by
  rfl

theorem fromCM_add (x y : CM31) : fromCM (x + y) = fromCM x + fromCM y :=
  ConcreteCircleCount.embedCM_add x y

theorem fromCM_one : fromCM (1 : CM31) = (1 : QM31) :=
  ConcreteCircleCount.embedCM_one

theorem fromCM_mul (x y : CM31) : fromCM (x * y) = fromCM x * fromCM y := by
  apply QM31FieldInstance.toQuadratic.injective
  change QM31FieldInstance.toQuadratic (fromCM (x * y)) =
    QM31FieldInstance.toQuadratic (fromCM x) *
      QM31FieldInstance.toQuadratic (fromCM y)
  ext <;>
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;>
    simp [fromCM, ConcreteCircleCount.embedCM,
      QM31FieldInstance.toQuadratic, CM31FieldInstance.mul_eq_cmMul,
      cmMul, ConcreteCircleCount.cm31_zero_eq,
      S31.Gadgets.Air.QuadField.twoPlusI] <;>
    ring

theorem fromCM_zero : fromCM (0 : CM31) = (0 : QM31) := by
  apply QM31FieldInstance.toQuadratic.injective
  rfl

theorem fromCM_inv (x : CM31) : fromCM x⁻¹ = (fromCM x)⁻¹ := by
  by_cases hx : x = 0
  · subst x
    simp [fromCM_zero]
  · have hmul := fromCM_mul x x⁻¹
    rw [mul_inv_cancel₀ hx, fromCM_one] at hmul
    exact eq_inv_of_mul_eq_one_right hmul.symm

theorem fromCM_ne_zero {x : CM31} (hx : x ≠ 0) : fromCM x ≠ 0 := by
  intro h
  have h' := congrArg QM.c0 h
  have : x = 0 := by simpa [fromCM, ConcreteCircleCount.embedCM] using h'
  exact hx this

/-- The same determinant used by CAS05, before its checked CM31 inverse. -/
noncomputable def rowDenominator (pointX pointY : QM31) (rowX rowY : CM31) : CM31 :=
  (pointX.c0 - rowX) * pointY.c1 - (pointY.c0 - rowY) * pointX.c1

theorem rowDenominator_nonzero (pointX pointY : QM31) (rowX rowY : CM31)
    (hcircle : pointX ^ 2 + pointY ^ 2 = 1)
    (hrow : rowX ^ 2 + rowY ^ 2 = 1)
    (hguard : pointY.c1 ≠ 0) :
    rowDenominator pointX pointY rowX rowY ≠ 0 := by
  exact QM31FieldInstance.denominator_ne_zero_of_field_circle
    pointX pointY rowX rowY hcircle hrow hguard

/-- The coordinate operation `QM31.mulM31` in the pinned Zig source. -/
noncomputable def nativeMulM31 (value : QM31) (scalar : M31) : QM31 :=
  ⟨⟨value.c0.a * scalar, value.c0.b * scalar⟩,
    ⟨value.c1.a * scalar, value.c1.b * scalar⟩⟩

theorem nativeMulM31_eq_mul (value : QM31) (scalar : M31) :
    nativeMulM31 value scalar = value * fromBase scalar := by
  apply QM31FieldInstance.toQuadratic.injective
  change QM31FieldInstance.toQuadratic (nativeMulM31 value scalar) =
    QM31FieldInstance.toQuadratic value *
      QM31FieldInstance.toQuadratic (fromBase scalar)
  ext <;>
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;>
    simp [nativeMulM31, fromBase, fromCM,
      ConcreteCircleCount.embedCM, QM31FieldInstance.toQuadratic,
      ConcreteCircleCount.cm31_zero_eq,
      S31.Gadgets.Air.QuadField.twoPlusI]

/-- `coefficient.c.mulM31(original).sub(coefficient.a.mulM31(rowY)).sub(coefficient.b)`
in the pinned draft, with its modeled coordinate multiplication. -/
noncomputable def nativeNumerator (coefficient : DeepQuotientAlgebra.LineCoeffs QM31)
    (rowY original : M31) : QM31 :=
  nativeMulM31 coefficient.c original - nativeMulM31 coefficient.a rowY - coefficient.b

theorem nativeNumerator_eq_residual (coefficient : DeepQuotientAlgebra.LineCoeffs QM31)
    (rowY original : M31) :
    nativeNumerator coefficient rowY original =
      DeepQuotientAlgebra.lineResidual coefficient (fromBase rowY)
        (fromBase original) := by
  unfold nativeNumerator DeepQuotientAlgebra.lineResidual
  rw [nativeMulM31_eq_mul, nativeMulM31_eq_mul]
  ring

/-- The coordinate operation `QM31.mulCM31` in the pinned Zig source. -/
noncomputable def nativeMulCM (value : QM31) (scalar : CM31) : QM31 :=
  ⟨value.c0 * scalar, value.c1 * scalar⟩

theorem nativeMulCM_eq_mul (value : QM31) (scalar : CM31) :
    nativeMulCM value scalar = value * fromCM scalar := by
  apply QM31FieldInstance.toQuadratic.injective
  change QM31FieldInstance.toQuadratic (nativeMulCM value scalar) =
    QM31FieldInstance.toQuadratic value *
      QM31FieldInstance.toQuadratic (fromCM scalar)
  ext <;>
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul] <;>
    simp [nativeMulCM, fromCM, ConcreteCircleCount.embedCM,
      QM31FieldInstance.toQuadratic, CM31FieldInstance.mul_eq_cmMul,
      cmMul, ConcreteCircleCount.cm31_zero_eq,
      S31.Gadgets.Air.QuadField.twoPlusI] <;>
    ring

/-- The native `mulCM31(inverse)` is extension-field multiplication by the
embedded checked inverse. -/
noncomputable def nativeOwnQuotient (coefficient : DeepQuotientAlgebra.LineCoeffs QM31)
    (rowY original : M31) (denominator : CM31) : QM31 :=
  nativeMulCM (nativeNumerator coefficient rowY original) denominator⁻¹

noncomputable def recipe (coefficient : DeepQuotientAlgebra.LineCoeffs QM31)
    (rowY : M31) (denominator : CM31) : Recipe QM31 :=
  { coeffs := coefficient, rowY := fromBase rowY,
    denominator := fromCM denominator }

theorem nativeOwnQuotient_eq_recipe (coefficient : DeepQuotientAlgebra.LineCoeffs QM31)
    (rowY original : M31) (denominator : CM31) :
    nativeOwnQuotient coefficient rowY original denominator =
      ownQuotient (recipe coefficient rowY denominator) (fromBase original) := by
  rw [nativeOwnQuotient, nativeMulCM_eq_mul,
    nativeNumerator_eq_residual, fromCM_inv]
  rfl

theorem recipe_checked (coefficient : DeepQuotientAlgebra.LineCoeffs QM31)
    (rowY : M31) (denominator : CM31) (hden : denominator ≠ 0) :
    (recipe coefficient rowY denominator).denominator ≠ 0 :=
  fromCM_ne_zero hden

/-- Zig's two updates of `power` and `answer` for each adjacent original and
own quotient. `List` order is the authenticated column roster order. -/
noncomputable def nativeBatch (challenge power : QM31) (rowY : M31) (denominator : CM31) :
    List (M31 × DeepQuotientAlgebra.LineCoeffs QM31) → QM31
  | [] => 0
  | (original, coefficient) :: rest =>
      power * fromBase original +
        (power * challenge) * nativeOwnQuotient coefficient rowY original denominator +
        nativeBatch challenge (power * challenge * challenge) rowY denominator rest

noncomputable def nativePairs (rowY : M31) (denominator : CM31)
    (columns : List (M31 × DeepQuotientAlgebra.LineCoeffs QM31)) :
    List (QM31 × QM31) :=
  columns.map fun (original, coefficient) =>
    (fromBase original, nativeOwnQuotient coefficient rowY original denominator)

theorem nativeBatch_eq_batchLoop (challenge power : QM31) (rowY : M31)
    (denominator : CM31)
    (columns : List (M31 × DeepQuotientAlgebra.LineCoeffs QM31)) :
    nativeBatch challenge power rowY denominator columns =
      batchLoop challenge power (nativePairs rowY denominator columns) := by
  induction columns generalizing power with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨original, coefficient⟩
      simp only [nativeBatch, nativePairs, List.map_cons, batchLoop]
      exact congrArg
        (fun rest => power * fromBase original +
          (power * challenge) * nativeOwnQuotient coefficient rowY original denominator + rest)
        (ih (power * challenge * challenge))

/-- For a fixed roster, the native-shaped row equals the fixed-source Lean
batch polynomial at the same challenge. This is local field algebra only. -/
theorem nativeBatch_eq_source_poly {n : Nat} (challenge : QM31) (rowY : M31)
    (denominator : CM31) (coefficients : Fin n → DeepQuotientAlgebra.LineCoeffs QM31)
    (source : Fin n → M31) :
    nativeBatch challenge 1 rowY denominator
        (List.ofFn fun i => (source i, coefficients i)) =
      (rowPoly (sourcePairs
        (fun i => recipe (coefficients i) rowY denominator)
        (fun i => fromBase (source i)))).eval challenge := by
  rw [nativeBatch_eq_batchLoop, rowPoly_eval]
  congr 1
  simp [nativePairs, sourcePairs, nativeOwnQuotient_eq_recipe,
    Function.comp_def]

/-- A modeled accepted circle row supplies the native nonzero denominator
check, every column's own quotient identity, and equality of the entire
ordered row batch with its fixed-source polynomial. Source authentication,
claims fixed before the challenge, and Zig execution are external premises. -/
theorem accepted_row_local_refinement {n : Nat} (challenge : QM31)
    (pointX pointY : QM31) (rowX rowY : M31)
    (coefficients : Fin n → DeepQuotientAlgebra.LineCoeffs QM31)
    (source : Fin n → M31)
    (hcircle : pointX ^ 2 + pointY ^ 2 = 1)
    (hrow : (⟨rowX, 0⟩ : CM31) ^ 2 + (⟨rowY, 0⟩ : CM31) ^ 2 = 1)
    (hguard : pointY.c1 ≠ 0) :
    let denominator := rowDenominator pointX pointY ⟨rowX, 0⟩ ⟨rowY, 0⟩
    CheckedRecipes (fun i => recipe (coefficients i) rowY denominator) ∧
    (∀ i, nativeOwnQuotient (coefficients i) rowY (source i) denominator *
        fromCM denominator =
      DeepQuotientAlgebra.lineResidual (coefficients i) (fromBase rowY)
        (fromBase (source i))) ∧
    nativeBatch challenge 1 rowY denominator
        (List.ofFn fun i => (source i, coefficients i)) =
      (rowPoly (sourcePairs
        (fun i => recipe (coefficients i) rowY denominator)
        (fun i => fromBase (source i)))).eval challenge := by
  dsimp only
  have hden : rowDenominator pointX pointY ⟨rowX, 0⟩ ⟨rowY, 0⟩ ≠ 0 :=
    rowDenominator_nonzero pointX pointY _ _ hcircle hrow hguard
  refine ⟨?_, ?_, nativeBatch_eq_source_poly challenge rowY _ coefficients source⟩
  · intro i
    exact recipe_checked (coefficients i) rowY _ hden
  · intro i
    rw [nativeOwnQuotient_eq_recipe]
    exact ownQuotient_cross_mul (recipe (coefficients i) rowY _) (fromBase (source i))
      (recipe_checked (coefficients i) rowY _ hden)

end S31.Gadgets.PcsFri.PairedBatchNativeRefinement
