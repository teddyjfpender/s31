import S31.Gadgets.Functional.Graph

/-!
A concrete model of the five-gate addition chain used for `std::math::pow<15>`.
The strict graph theorem covers all auxiliary witnesses in this model. The
production Python chain search and Zig AIR are checked separately by the
source/cost and native-proof acceptance gates.
-/

namespace S31.Functional

open Graph

/-- Input wire 0 is `x`; wires 1..5 are x², x⁴, x⁵, x¹⁰, x¹⁵. -/
def pow15Code : Code M31 FieldOp :=
  ⟨[.apply .mul [0, 0],
    .apply .mul [1, 1],
    .apply .mul [2, 0],
    .apply .mul [3, 3],
    .apply .mul [4, 3]], [5]⟩

/-- The left-to-right binary schedule needs one more gate. -/
def pow15BinaryCode : Code M31 FieldOp :=
  ⟨[.apply .mul [0, 0],
    .apply .mul [1, 0],
    .apply .mul [2, 2],
    .apply .mul [3, 0],
    .apply .mul [4, 4],
    .apply .mul [5, 0]], [6]⟩

theorem pow15Code_gate_count : pow15Code.gates.length = 5 := rfl

theorem pow15BinaryCode_gate_count : pow15BinaryCode.gates.length = 6 := rfl

theorem pow15Code_valid : pow15Code.WellFormedFor fieldArity 1 :=
  Code.check_sound pow15Code fieldArity 1 rfl

theorem pow15BinaryCode_valid :
    pow15BinaryCode.WellFormedFor fieldArity 1 :=
  Code.check_sound pow15BinaryCode fieldArity 1 rfl

private theorem modMulLeft (a b modulus : Nat) :
    Nat.mod (Nat.mul (Nat.mod a modulus) b) modulus =
      Nat.mod (Nat.mul a b) modulus := by
  change (a % modulus * b) % modulus = (a * b) % modulus
  rw [Nat.mul_comm (a % modulus) b, Nat.mul_mod_mod, Nat.mul_comm b a]

private theorem modMulRight (a b modulus : Nat) :
    Nat.mod (Nat.mul a (Nat.mod b modulus)) modulus =
      Nat.mod (Nat.mul a b) modulus := by
  change (a * (b % modulus)) % modulus = (a * b) % modulus
  exact Nat.mul_mod_mod a b modulus

theorem pow15Code_value (x : M31) :
    pow15Code.eval fieldEval [x] = [RiscvRefinement.M31.reduce (x.val ^ 15)] := by
  simp [pow15Code, Code.eval, Graph.run, Gate.eval, fieldEval]
  apply RiscvRefinement.M31.ext
  simp only [HMul.hMul, Mul.mul, HMod.hMod, Mod.mod,
    RiscvRefinement.M31.mul, RiscvRefinement.M31.reduce_val]
  simp only [modMulLeft, modMulRight]
  simp only [Nat.mul_eq]
  congr 1
  ring

theorem pow15BinaryCode_value (x : M31) :
    pow15BinaryCode.eval fieldEval [x] = [RiscvRefinement.M31.reduce (x.val ^ 15)] := by
  simp [pow15BinaryCode, Code.eval, Graph.run, Gate.eval, fieldEval]
  apply RiscvRefinement.M31.ext
  simp only [HMul.hMul, Mul.mul, HMod.hMod, Mod.mod,
    RiscvRefinement.M31.mul, RiscvRefinement.M31.reduce_val]
  simp only [modMulLeft, modMulRight]
  simp only [Nat.mul_eq]
  congr 1
  ring

/-- Every strictly accepted proof witness binds the result to x¹⁵, and the
honest result has a satisfying witness. -/
theorem pow15Code_accepts (x : M31) (output : List M31) :
    pow15Code.strictAccepts fieldArity Gadgets.Hash.fieldPrimitive [x] output ↔
      output = [RiscvRefinement.M31.reduce (x.val ^ 15)] := by
  rw [Gadgets.Hash.field_schedule_strict_sound_complete]
  simp [pow15Code_valid, pow15Code_value]

theorem pow15Code_rejects_forged (x claim : M31)
    (falseClaim : claim ≠ RiscvRefinement.M31.reduce (x.val ^ 15)) :
    ¬ pow15Code.strictAccepts fieldArity
        Gadgets.Hash.fieldPrimitive [x] [claim] := by
  intro accepted
  have equal : claim = RiscvRefinement.M31.reduce (x.val ^ 15) := by
    simpa using (pow15Code_accepts x [claim]).mp accepted
  exact falseClaim equal

end S31.Functional
