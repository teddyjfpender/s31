import S31.Gadgets.BuilderValidity
import S31.Gadgets.Hash
import S31.Semantics.Poseidon2
import S31.Semantics.Sha256

namespace S31.Poseidon2

open Graph

/-- The actual fifth-power schedule used by Poseidon2 preserves valid wiring
for any existing builder state and any live input wire. All three new
multiplication gates read only previous wires and have binary arity. -/
theorem fifth_valid (state : Builder M31 FieldOp) (x : Nat)
    (h : state.ValidFor fieldArity)
    (hx : x < state.inputCount + state.gates.size) :
    let (result, next) := (fifth x).run state
    next.ValidFor fieldArity ∧ next.inputCount = state.inputCount ∧
      state.gates.size + 3 = next.gates.size ∧
      result < next.inputCount + next.gates.size := by
  let bound := state.inputCount + state.gates.size
  let first : Gate M31 FieldOp := .apply .mul [x, x]
  let afterFirst : Builder M31 FieldOp := {state with gates := state.gates.push first}
  have hfirst : afterFirst.ValidFor fieldArity :=
    (emit_valid fieldArity state first h
      ⟨(by simpa [first, Gate.ValidAt] using hx), (by rfl)⟩).2
  let second : Gate M31 FieldOp := .apply .mul [bound, bound]
  let afterSecond : Builder M31 FieldOp :=
    {afterFirst with gates := afterFirst.gates.push second}
  have hbound : bound < afterFirst.inputCount + afterFirst.gates.size := by
    dsimp [bound, afterFirst]
    simp
  have hsecond : afterSecond.ValidFor fieldArity :=
    (emit_valid fieldArity afterFirst second hfirst
      ⟨(by simpa [second, Gate.ValidAt] using hbound), (by rfl)⟩).2
  let third : Gate M31 FieldOp := .apply .mul [x, bound + 1]
  let afterThird : Builder M31 FieldOp :=
    {afterSecond with gates := afterSecond.gates.push third}
  have hx2 : x < afterSecond.inputCount + afterSecond.gates.size := by
    dsimp [afterSecond, afterFirst]
    simp
    omega
  have hb2 : bound + 1 < afterSecond.inputCount + afterSecond.gates.size := by
    dsimp [bound, afterSecond, afterFirst]
    simp only [Array.size_push]
    omega
  have hthird : afterThird.ValidFor fieldArity :=
    (emit_valid fieldArity afterSecond third hsecond
      ⟨(by simpa [third, Gate.ValidAt] using And.intro hx2 hb2), (by rfl)⟩).2
  simp [fifth, mul, binary, emit]
  exact hthird

/-- A complete circuit built from the same Poseidon2 fifth-power routine. -/
def fifthCircuit : Code M31 FieldOp := build 1 do
  let result ← fifth 0
  return [result]

theorem fifthCircuit_valid : fifthCircuit.WellFormedFor fieldArity 1 := by
  unfold fifthCircuit
  apply build_valid
  intro state hs hcount
  have hx : 0 < state.inputCount + state.gates.size := by omega
  have hstep := fifth_valid state 0 hs hx
  change (let (result, next) := (fifth 0).run state
    next.ValidFor fieldArity ∧ next.inputCount = 1 ∧
      ∀ index ∈ [result], index < next.inputCount + next.gates.size)
  cases hrun : (fifth 0).run state with
  | mk result next =>
    simp only [hrun] at hstep
    refine ⟨hstep.1, hstep.2.1.trans hcount, ?_⟩
    intro index member
    simp only [List.mem_singleton] at member
    subst index
    exact hstep.2.2.2

theorem fifthCircuit_strict_sound_complete (x : M31) (output : List M31) :
    fifthCircuit.strictAccepts fieldArity Gadgets.Hash.fieldPrimitive [x] output ↔
      output = fifthCircuit.eval fieldEval [x] := by
  rw [Gadgets.Hash.field_schedule_strict_sound_complete]
  simp [fifthCircuit_valid]

theorem fifthCircuit_eval (x : M31) :
    fifthCircuit.eval fieldEval [x] =
      [RiscvRefinement.Recursion.CompactPoseidon.fifthPower x] := by
  rw [← RiscvRefinement.Recursion.CompactPoseidon.lowered_eq_fifthPower]
  rfl

/-- Every satisfying intermediate witness for this generated circuit has the
same fifth-power output as the canonical M31 S-box. -/
theorem fifthCircuit_correct (x : M31) (output : List M31) :
    fifthCircuit.strictAccepts fieldArity Gadgets.Hash.fieldPrimitive [x] output ↔
      output = [RiscvRefinement.Recursion.CompactPoseidon.fifthPower x] := by
  rw [fifthCircuit_strict_sound_complete, fifthCircuit_eval]

end S31.Poseidon2

namespace S31.Sha256

open Graph

/-- Both SHA sigma variants preserve builder validity. The proof checks the
five emitted unary/binary gates for either rotate or logical shift, including
the wire indices of both XOR gates. -/
theorem sigma_valid (state : Builder Words.Word WordOp) (x a b c : Nat) (logical : Bool)
    (h : state.ValidFor wordArity)
    (hx : x < state.inputCount + state.gates.size) :
    let (result, next) := (sigma x a b c logical).run state
    next.ValidFor wordArity ∧ next.inputCount = state.inputCount ∧
      state.gates.size + 5 = next.gates.size ∧
      result < next.inputCount + next.gates.size := by
  cases logical <;> simp [sigma, rot, shr, xor, unary, binary, emit]
  all_goals
    unfold Builder.ValidFor at h ⊢
    simp only [Array.toList_push]
    constructor
    · repeat' apply GatesValid.snoc
      · exact h.1
      all_goals simp [Gate.ValidAt, Array.length_toList] <;> omega
    · intro gate hgate
      simp only [List.mem_append, List.mem_singleton] at hgate
      rcases hgate with ((((hold | h1) | h2) | h3) | h4) | h5
      · exact h.2 gate hold
      all_goals (subst gate; rfl)

/-- A family of SHA sigma circuits, for arbitrary rotation amounts and either
choice of logical shift or rotation in the third term. -/
def sigmaCircuit (a b c : Nat) (logical : Bool) : Code Words.Word WordOp := build 1 do
  let result ← sigma 0 a b c logical
  return [result]

theorem sigmaCircuit_valid (a b c : Nat) (logical : Bool) :
    (sigmaCircuit a b c logical).WellFormedFor wordArity 1 := by
  unfold sigmaCircuit
  apply build_valid
  intro state hs hcount
  have hx : 0 < state.inputCount + state.gates.size := by omega
  have hstep := sigma_valid state 0 a b c logical hs hx
  change (let (result, next) := (sigma 0 a b c logical).run state
    next.ValidFor wordArity ∧ next.inputCount = 1 ∧
      ∀ index ∈ [result], index < next.inputCount + next.gates.size)
  cases hrun : (sigma 0 a b c logical).run state with
  | mk result next =>
    simp only [hrun] at hstep
    refine ⟨hstep.1, hstep.2.1.trans hcount, ?_⟩
    intro index member
    simp only [List.mem_singleton] at member
    subst index
    exact hstep.2.2.2

theorem sigmaCircuit_strict_sound_complete (a b c : Nat) (logical : Bool)
    (x : Words.Word) (output : List Words.Word) :
    (sigmaCircuit a b c logical).strictAccepts wordArity Gadgets.Word.primitive [x] output ↔
      output = (sigmaCircuit a b c logical).eval wordEval [x] := by
  rw [Gadgets.Hash.word_schedule_strict_sound_complete]
  simp [sigmaCircuit_valid a b c logical]

theorem sigmaCircuit_eval (a b c : Nat) (logical : Bool) (x : Words.Word) :
    (sigmaCircuit a b c logical).eval wordEval [x] =
      [(Words.rotr x a ^^^ Words.rotr x b) ^^^
        (if logical then x >>> c else Words.rotr x c)] := by
  cases logical <;> rfl

/-- The generated SHA sigma circuit computes its exact word formula for every
satisfying primitive witness, for all shift amounts and either variant. -/
theorem sigmaCircuit_correct (a b c : Nat) (logical : Bool)
    (x : Words.Word) (output : List Words.Word) :
    (sigmaCircuit a b c logical).strictAccepts wordArity Gadgets.Word.primitive [x] output ↔
      output = [(Words.rotr x a ^^^ Words.rotr x b) ^^^
        (if logical then x >>> c else Words.rotr x c)] := by
  rw [sigmaCircuit_strict_sound_complete, sigmaCircuit_eval]

end S31.Sha256
