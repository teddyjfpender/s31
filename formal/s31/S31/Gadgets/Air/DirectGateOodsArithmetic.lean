import S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
import S31.Gadgets.Air.QuadField

/-!
The nine installed Gate arithmetic roots at a secure-field OODS point.
`resident_verifier.zig` executes base instructions in QM31, and then uses
`QM31.fromPartialEvals` for each `secure_col` extension instruction. The
first nine roots feed the base result and three zero registers to that
operation. This file models that exact root pattern and proves the resulting
values are the same nine polynomials over arbitrary QM31 sampled cells.

It does not prove that those sampled cells are authenticated openings, that
their composition coefficients are bound by the transcript, or that the
two LogUp roots agree with the pure interaction model.
-/

namespace S31.Gadgets.Air.DirectGateOodsArithmetic

open S31.Gadgets.Air.DirectGatePolynomial
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic

abbrev QM := S31.Gadgets.Air.QuadField.QM

def basisI : QM := ⟨⟨0, 1⟩, 0⟩
def basisU : QM := ⟨0, ⟨1, 0⟩⟩
def basisIU : QM := ⟨0, ⟨0, 1⟩⟩

/-- The algebraic shape of native `QM31.fromPartialEvals` at an OODS point.
The source-level correspondence to the Zig implementation is source-bound,
not an extracted compiler theorem. -/
def fromPartialEvals (a b c d : QM) : QM :=
  a + b * basisI + c * basisU + d * basisIU

theorem fromPartialEvals_three_zero (value : QM) :
    fromPartialEvals value 0 0 0 = value := by
  simp [fromPartialEvals]

/-- Root slots 0–8 are `secure_col` of each arithmetic base result and
the same constant-zero register in the remaining three coordinates. -/
def installedArithmeticRoots (cells : ArithmeticCells QM) : List QM :=
  (bytecodeArithmeticOver cells).map fun value =>
    fromPartialEvals value 0 0 0

theorem installed_arithmetic_roots_eq_oods_polynomials
    (cells : ArithmeticCells QM) :
    installedArithmeticRoots cells = modeledArithmetic cells := by
  simp [installedArithmeticRoots, fromPartialEvals_three_zero,
    bytecode_arithmetic_over_eq]

/-- A zero-root condition at one QM31 point gives only polynomial
evaluations at that point. It does not imply M31 row constraints without
the production random-composition and PCS/FRI arguments. -/
theorem installed_zero_iff_modeled_zero (cells : ArithmeticCells QM) :
    (∀ r ∈ installedArithmeticRoots cells, r = 0) ↔
      (∀ r ∈ modeledArithmetic cells, r = 0) := by
  rw [installed_arithmetic_roots_eq_oods_polynomials]

end S31.Gadgets.Air.DirectGateOodsArithmetic
