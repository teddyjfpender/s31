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

/-- One complete SHA compression round preserves all eight live state wires.
This checks the actual 27-gate builder body, including `Ch`, `Maj`, both sigma
calls, the round constant and the two output additions. -/
theorem round_valid (builder : Builder Words.Word WordOp)
    (a b c d e f g h message constantValue : Nat)
    (hb : builder.ValidFor wordArity)
    (hlive : ∀ index ∈ [a, b, c, d, e, f, g, h, message],
      index < builder.inputCount + builder.gates.size) :
    let (output, next) := (round [a, b, c, d, e, f, g, h] message constantValue).run builder
    next.ValidFor wordArity ∧ next.inputCount = builder.inputCount ∧
      builder.gates.size + 27 = next.gates.size ∧ output.length = 8 ∧
      ∀ index ∈ output, index < next.inputCount + next.gates.size := by
  have ha : a < builder.inputCount + builder.gates.size := hlive a (by simp)
  have hbwire : b < builder.inputCount + builder.gates.size := hlive b (by simp)
  have hc : c < builder.inputCount + builder.gates.size := hlive c (by simp)
  have he : e < builder.inputCount + builder.gates.size := hlive e (by simp)
  have hf : f < builder.inputCount + builder.gates.size := hlive f (by simp)
  have hg : g < builder.inputCount + builder.gates.size := hlive g (by simp)
  simp [round, sigma, rot, xor, and, not, add, constant,
    unary, binary, literal, emit]
  constructor
  · unfold Builder.ValidFor at hb ⊢
    simp only [Array.toList_push]
    constructor
    · repeat' apply GatesValid.snoc
      · exact hb.1
      all_goals simp [Gate.ValidAt, Array.length_toList] at * <;> omega
    · intro gate hgate
      simp only [List.mem_append, List.mem_singleton] at hgate
      aesop (add simp [Gate.ArityValid, wordArity])
  · omega

/-- A length-eight state has exactly the eight wires consumed by `round`. -/
private theorem list8_decomp {α : Type} (xs : List α) (hlen : xs.length = 8) :
    ∃ a b c d e f g h : α, xs = [a, b, c, d, e, f, g, h] := by
  rcases xs with _ | ⟨a, xs⟩
  · simp at hlen
  rcases xs with _ | ⟨b, xs⟩
  · simp at hlen
  rcases xs with _ | ⟨c, xs⟩
  · simp at hlen
  rcases xs with _ | ⟨d, xs⟩
  · simp at hlen
  rcases xs with _ | ⟨e, xs⟩
  · simp at hlen
  rcases xs with _ | ⟨f, xs⟩
  · simp at hlen
  rcases xs with _ | ⟨g, xs⟩
  · simp at hlen
  rcases xs with _ | ⟨h, xs⟩
  · simp at hlen
  cases xs with
  | nil => exact ⟨a, b, c, d, e, f, g, h, rfl⟩
  | cons _ _ => simp at hlen

/-- The same round invariant for a dynamic state list known to contain eight
live wires. The exact gate count makes earlier message wires remain live for
later rounds. -/
theorem round_state_valid (builder : Builder Words.Word WordOp)
    (state : List Nat) (message constantValue : Nat)
    (hb : builder.ValidFor wordArity)
    (hlen : state.length = 8)
    (hstate : ∀ index ∈ state, index < builder.inputCount + builder.gates.size)
    (hmessage : message < builder.inputCount + builder.gates.size) :
    let (output, next) := (round state message constantValue).run builder
    next.ValidFor wordArity ∧ next.inputCount = builder.inputCount ∧
      builder.gates.size + 27 = next.gates.size ∧ output.length = 8 ∧
      ∀ index ∈ output, index < next.inputCount + next.gates.size := by
  obtain ⟨a, b, c, d, e, f, g, h, rfl⟩ := list8_decomp state hlen
  apply round_valid builder a b c d e f g h message constantValue hb
  intro index member
  change index ∈ [a, b, c, d, e, f, g, h] ++ [message] at member
  rcases List.mem_append.mp member with old | last
  · exact hstate index old
  · simp only [List.mem_singleton] at last
    subst index
    exact hmessage

/-- Any number of actual SHA rounds preserves a live eight-word state. The
proof is inductive over the same `foldlM` used by the compression builder.
Each round contributes exactly 27 gates, independently of its constant. -/
theorem rounds_valid (builder : Builder Words.Word WordOp)
    (state : List Nat) (pairs : List (Nat × Nat))
    (hb : builder.ValidFor wordArity)
    (hlen : state.length = 8)
    (hstate : ∀ index ∈ state, index < builder.inputCount + builder.gates.size)
    (hpairs : ∀ pair ∈ pairs, pair.1 < builder.inputCount + builder.gates.size) :
    let (output, next) := (pairs.foldlM (fun s (w, k) => round s w k) state).run builder
    next.ValidFor wordArity ∧ next.inputCount = builder.inputCount ∧
      builder.gates.size + 27 * pairs.length = next.gates.size ∧
      output.length = 8 ∧
      ∀ index ∈ output, index < next.inputCount + next.gates.size := by
  induction pairs generalizing builder state with
  | nil =>
    simp [List.foldlM_nil]
    exact ⟨hb, hlen, hstate⟩
  | cons pair tail ih =>
    obtain ⟨message, constantValue⟩ := pair
    have hm : message < builder.inputCount + builder.gates.size :=
      hpairs (message, constantValue) (by simp)
    have hstep := round_state_valid builder state message constantValue hb hlen hstate hm
    cases hrun : (round state message constantValue).run builder with
    | mk intermediate next =>
      simp only [hrun] at hstep
      have htail : ∀ pair ∈ tail,
          pair.1 < next.inputCount + next.gates.size := by
        intro pair member
        have hprior := hpairs pair (by simp [member])
        omega
      have hrec := ih next intermediate hstep.1 hstep.2.2.2.1
        hstep.2.2.2.2 htail
      cases htailrun : (tail.foldlM (fun s (w, k) => round s w k) intermediate).run next with
      | mk output final =>
        simp only [htailrun] at hrec
        simp only [List.foldlM_cons, StateT.run_bind, hrun, List.length_cons]
        change (let (out, result) :=
          (tail.foldlM (fun s (w, k) => round s w k) intermediate).run next
          result.ValidFor wordArity ∧ result.inputCount = builder.inputCount ∧
            builder.gates.size + 27 * (tail.length + 1) = result.gates.size ∧
            out.length = 8 ∧
            ∀ index ∈ out, index < result.inputCount + result.gates.size)
        simp only [htailrun]
        refine ⟨hrec.1, ?_, ?_, hrec.2.2.2.1, hrec.2.2.2.2⟩
        · exact hrec.2.1.trans hstep.2.1
        · omega

/-- A complete SHA compression round with eight state words and one message
word. The circuit is generated by the same round builder used in SHA-256. -/
def roundCircuit (constantValue : Nat) : Code Words.Word WordOp :=
  build 9 (round [0, 1, 2, 3, 4, 5, 6, 7] 8 constantValue)

theorem roundCircuit_valid (constantValue : Nat) :
    (roundCircuit constantValue).WellFormedFor wordArity 9 := by
  unfold roundCircuit
  apply build_valid
  intro builder hb hcount
  have hlive : ∀ index ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8],
      index < builder.inputCount + builder.gates.size := by
    intro index member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have hr := round_valid builder 0 1 2 3 4 5 6 7 8 constantValue hb hlive
  cases hrun : (round [0, 1, 2, 3, 4, 5, 6, 7] 8 constantValue).run builder with
  | mk output next =>
    simp only [hrun] at hr
    exact ⟨hr.1, hr.2.1.trans hcount, hr.2.2.2.2⟩

/-- For any nine input words and any round constant, a strict circuit witness
is accepted exactly when its output equals the computed eight-word state. -/
theorem roundCircuit_strict_sound_complete (constantValue : Nat)
    (inputs output : List Words.Word) (hinputs : inputs.length = 9) :
    (roundCircuit constantValue).strictAccepts wordArity
        Gadgets.Word.primitive inputs output ↔
      output = (roundCircuit constantValue).eval wordEval inputs := by
  rw [Gadgets.Hash.word_schedule_strict_sound_complete]
  simp [hinputs, roundCircuit_valid constantValue]

/-- A parameterized compression-round circuit. The first eight inputs are the
initial state; each `(wire, constant)` pair chooses a live message input and
one round constant. The proof covers zero or arbitrarily many rounds. -/
def roundsCircuit (inputCount : Nat) (pairs : List (Nat × Nat)) : Code Words.Word WordOp :=
  build inputCount (pairs.foldlM (fun s (w, k) => round s w k) [0, 1, 2, 3, 4, 5, 6, 7])

theorem roundsCircuit_valid (inputCount : Nat) (pairs : List (Nat × Nat))
    (hinput : 8 ≤ inputCount) (hpairs : ∀ pair ∈ pairs, pair.1 < inputCount) :
    (roundsCircuit inputCount pairs).WellFormedFor wordArity inputCount := by
  unfold roundsCircuit
  apply build_valid
  intro builder hb hcount
  have hstate : ∀ index ∈ [0, 1, 2, 3, 4, 5, 6, 7],
      index < builder.inputCount + builder.gates.size := by
    intro index member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    omega
  have hmessages : ∀ pair ∈ pairs,
      pair.1 < builder.inputCount + builder.gates.size := by
    intro pair member
    have h := hpairs pair member
    omega
  have hr := rounds_valid builder [0, 1, 2, 3, 4, 5, 6, 7] pairs hb rfl hstate hmessages
  cases hrun : (pairs.foldlM (fun s (w, k) => round s w k) [0, 1, 2, 3, 4, 5, 6, 7]).run builder with
  | mk output next =>
    simp only [hrun] at hr
    exact ⟨hr.1, hr.2.1.trans hcount, hr.2.2.2.2⟩

/-- Every witness accepted by the generated multi-round circuit agrees with
its evaluator. This includes arbitrary intermediate gate witnesses. -/
theorem roundsCircuit_strict_sound_complete (inputCount : Nat) (pairs : List (Nat × Nat))
    (inputs output : List Words.Word) (hinput : 8 ≤ inputCount)
    (hpairs : ∀ pair ∈ pairs, pair.1 < inputCount)
    (hinputs : inputs.length = inputCount) :
    (roundsCircuit inputCount pairs).strictAccepts wordArity
        Gadgets.Word.primitive inputs output ↔
      output = (roundsCircuit inputCount pairs).eval wordEval inputs := by
  rw [Gadgets.Hash.word_schedule_strict_sound_complete]
  simp [hinputs, roundsCircuit_valid inputCount pairs hinput hpairs]

/-- The concrete 64-round SHA core. Inputs 0–7 are the state and inputs 8–71
are the already-expanded message words. Round constants are drawn from the
same generated table used by the SHA compression semantics. -/
def sha64Pairs : List (Nat × Nat) :=
  (List.range 64).map (fun i => (8 + i, Constants.shaRound.getD i 0))

def sha64Circuit : Code Words.Word WordOp := roundsCircuit 72 sha64Pairs

theorem shaRound_length : Constants.shaRound.length = 64 := by rfl

theorem sha64Pairs_length : sha64Pairs.length = 64 := by simp [sha64Pairs]

theorem sha64Pairs_bound : ∀ pair ∈ sha64Pairs, pair.1 < 72 := by
  intro pair member
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp member
  have hibound : i < 64 := List.mem_range.mp hi
  simp
  omega

theorem sha64Circuit_valid : sha64Circuit.WellFormedFor wordArity 72 := by
  exact roundsCircuit_valid 72 sha64Pairs (by omega) sha64Pairs_bound

/-- The fixed 64-round circuit accepts exactly its computed eight-word state
for every 72-word input and every auxiliary gate assignment. -/
theorem sha64Circuit_strict_sound_complete
    (inputs output : List Words.Word) (hinputs : inputs.length = 72) :
    sha64Circuit.strictAccepts wordArity Gadgets.Word.primitive inputs output ↔
      output = sha64Circuit.eval wordEval inputs := by
  exact roundsCircuit_strict_sound_complete 72 sha64Pairs inputs output
    (by omega) sha64Pairs_bound hinputs

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
