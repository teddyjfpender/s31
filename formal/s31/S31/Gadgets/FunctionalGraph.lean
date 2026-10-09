import S31.Semantics.Functional
import S31.Gadgets.Hash

/-!
An executable lowering of the functional core's residual polynomial into the
same straight-line graph model used by the S31 hash-circuit proofs. The exact
worked example is proved below. A universal compiler-correctness theorem for
this lowering and correspondence to production Zig AIR remain open.
-/

namespace S31.Functional

open Graph

def Poly.emit {n : Nat} : Poly n → FieldBuild Nat
  | .input i => pure i.val
  | .literal value => Graph.literal value
  | .add lhs rhs => do
      let left ← lhs.emit
      let right ← rhs.emit
      Graph.binary .add left right
  | .mul lhs rhs => do
      let left ← lhs.emit
      let right ← rhs.emit
      Graph.binary .mul left right

def Poly.code {n : Nat} (poly : Poly n) : Code M31 FieldOp :=
  build n do
    let output ← poly.emit
    return [output]

/-- The actual residual core, once beta-reduced, emits two gates. The output
index 2 is the new add gate; inputs occupy the prefix at index 0. -/
def capturedSquareCode : Code M31 FieldOp :=
  (specialize capturedSquare (inputResidual [(0 : Fin 1)])).code

theorem capturedSquareCode_shape :
    capturedSquareCode = ⟨[.apply .mul [0, 0], .apply .add [1, 0]], [2]⟩ := rfl

theorem capturedSquareCode_valid :
    capturedSquareCode.WellFormedFor fieldArity 1 := by
  apply Code.check_sound
  rw [capturedSquareCode_shape]
  rfl

theorem capturedSquareCode_eval (x : M31) :
    capturedSquareCode.eval fieldEval [x] = [x * x + x] := by
  rw [capturedSquareCode_shape]
  rfl

/-- Every auxiliary witness satisfying the concrete two-gate graph has the
same output as the source term, and the honest gate witnesses exist. -/
theorem capturedSquareCode_accepts (x : M31) (output : List M31) :
    capturedSquareCode.strictAccepts fieldArity Gadgets.Hash.fieldPrimitive [x] output ↔
      output = [denote capturedSquare (.cons x .nil)] := by
  rw [Gadgets.Hash.field_schedule_strict_sound_complete]
  simp [capturedSquareCode_valid, capturedSquareCode_eval, capturedSquare, denote, Env.get]

end S31.Functional
