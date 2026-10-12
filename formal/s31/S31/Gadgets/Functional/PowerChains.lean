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

namespace AdditionChainCertificate

/-!
A source-independent certificate for multiplication schedules. Reference 0
is the input `x`; each pair refers to two earlier powers and appends their
product. The executable bound check rejects forward and missing references.
`values_eq_powers` proves the algebraic meaning of *any* such schedule. The
concrete 19-step certificate below is checked against the Python compiler's
chain in the source test; Python emission and native AIR remain separate trust
boundaries.
-/

abbrev F := S31.Field.F

def exponentStep (powers : List Nat) (refs : Nat × Nat) : List Nat :=
  powers ++ [powers.getD refs.1 0 + powers.getD refs.2 0]

def valueStep (values : List F) (refs : Nat × Nat) : List F :=
  values ++ [values.getD refs.1 1 * values.getD refs.2 1]

def exponents (refs : List (Nat × Nat)) : List Nat :=
  refs.foldl exponentStep [1]

def values (x : F) (refs : List (Nat × Nat)) : List F :=
  refs.foldl valueStep [x]

def valid (refs : List (Nat × Nat)) : Bool :=
  (refs.foldl (fun (state : Nat × Bool) pair =>
    (state.1 + 1, state.2 && decide (pair.1 < state.1) &&
                    decide (pair.2 < state.1))) (1, true)).2

private theorem getD_map_pow (x : F) (powers : List Nat) (index : Nat) :
    (powers.map (fun exponent => x ^ exponent)).getD index 1 =
      x ^ powers.getD index 0 := by
  cases h : powers[index]? with
  | none => simp [List.getD_eq_getElem?_getD, h]
  | some exponent => simp [List.getD_eq_getElem?_getD, h]

private theorem step_agrees (x : F) (powers : List Nat)
    (refs : Nat × Nat) :
    valueStep (powers.map (fun exponent => x ^ exponent)) refs =
      (exponentStep powers refs).map (fun exponent => x ^ exponent) := by
  simp only [valueStep, exponentStep, List.map_append, List.map_cons,
             List.map_nil]
  rw [getD_map_pow x powers refs.1, getD_map_pow x powers refs.2,
      pow_add]

private theorem fold_agrees (x : F) (refs : List (Nat × Nat))
    (powers : List Nat) :
    refs.foldl valueStep (powers.map (fun exponent => x ^ exponent)) =
      (refs.foldl exponentStep powers).map (fun exponent => x ^ exponent) := by
  induction refs generalizing powers with
  | nil => rfl
  | cons pair rest ih =>
      simp only [List.foldl_cons]
      rw [step_agrees]
      exact ih _

theorem values_eq_powers (x : F) (refs : List (Nat × Nat)) :
    values x refs = (exponents refs).map (fun exponent => x ^ exponent) := by
  simpa [values, exponents] using fold_agrees x refs [1]

/-- The actual star-chain wire indices for the compiler's large all-ones
schedule. Each pair's first index is the previous wire. -/
def pow65535Refs : List (Nat × Nat) := [
  (0, 0), (1, 0), (2, 2), (3, 3), (4, 2),
  (5, 5), (6, 6), (7, 7), (8, 8), (9, 5),
  (10, 10), (11, 11), (12, 12), (13, 13), (14, 14),
  (15, 15), (16, 16), (17, 17), (18, 10)
]

theorem pow65535Refs_valid : valid pow65535Refs = true := by decide
theorem pow65535Refs_steps : pow65535Refs.length = 19 := by decide
theorem pow65535Refs_target : (exponents pow65535Refs).getD 19 0 = 65535 := by decide

theorem pow65535_value (x : F) :
    (values x pow65535Refs).getD 19 1 = x ^ 65535 := by
  rw [values_eq_powers]
  rw [getD_map_pow, pow65535Refs_target]

/-- Build `x³`, then reuse the `65535` schedule with its references shifted
past the two prefix multiplications. Literal indices let the source test
compare this certificate directly with the production circuit graph. -/
def pow196605Refs : List (Nat × Nat) := [
  (0, 0), (1, 0),
  (2, 2), (3, 2), (4, 4), (5, 5), (6, 4),
  (7, 7), (8, 8), (9, 9), (10, 10), (11, 7),
  (12, 12), (13, 13), (14, 14), (15, 15), (16, 16),
  (17, 17), (18, 18), (19, 19), (20, 12)
]

theorem pow196605Refs_valid : valid pow196605Refs = true := by decide
theorem pow196605Refs_steps : pow196605Refs.length = 21 := by decide
theorem pow196605Refs_factor :
    pow196605Refs = [(0, 0), (1, 0)] ++
      pow65535Refs.map (fun refs => (refs.1 + 2, refs.2 + 2)) := by decide
theorem pow196605Refs_target :
    (exponents pow196605Refs).getD 21 0 = 196605 := by decide

theorem pow196605_value (x : F) :
    (values x pow196605Refs).getD 21 1 = x ^ 196605 := by
  rw [values_eq_powers]
  rw [getD_map_pow, pow196605Refs_target]

end AdditionChainCertificate

end S31.Functional
