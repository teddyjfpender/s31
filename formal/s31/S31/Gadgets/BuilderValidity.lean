import S31.Semantics.Graph

namespace S31.Graph

variable {α Op : Type}

/-- Append one gate after a valid schedule. Its operands are checked against
the old bound, so it cannot read itself or a future gate. -/
theorem GatesValid.snoc {bound : Nat} {gates : List (Gate α Op)} {gate : Gate α Op}
    (h : GatesValid bound gates) (hg : gate.ValidAt (bound + gates.length)) :
    GatesValid bound (gates ++ [gate]) := by
  induction h with
  | nil bound =>
    simpa using GatesValid.cons hg (GatesValid.nil (bound + 1))
  | @cons bound head tail hhead htail ih =>
    simp only [List.cons_append]
    apply GatesValid.cons hhead
    apply ih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hg

def Builder.ValidFor (arity : Op → Nat) (state : Builder α Op) : Prop :=
  GatesValid state.inputCount state.gates.toList ∧
    ∀ gate ∈ state.gates.toList, gate.ArityValid arity

theorem Builder.empty_valid (arity : Op → Nat) (inputCount : Nat) :
    (⟨inputCount, #[]⟩ : Builder α Op).ValidFor arity := by
  constructor
  · exact .nil inputCount
  · simp

/-- Core builder rule: a locally valid gate preserves the global schedule,
and `emit` returns exactly the new wire index. -/
theorem emit_valid (arity : Op → Nat) (state : Builder α Op) (gate : Gate α Op)
    (h : state.ValidFor arity)
    (hg : gate.ValidAt (state.inputCount + state.gates.size) ∧ gate.ArityValid arity) :
    (emit gate).run state =
      (state.inputCount + state.gates.size, {state with gates := state.gates.push gate}) ∧
      ({state with gates := state.gates.push gate} : Builder α Op).ValidFor arity := by
  constructor
  · rfl
  · constructor
    · simpa [Builder.ValidFor, Array.toList_push, Array.length_toList] using
        GatesValid.snoc h.1 (by simpa [Array.length_toList] using hg.1)
    · intro item hmem
      rw [Array.toList_push, List.mem_append] at hmem
      rcases hmem with hold | hnew
      · exact h.2 item hold
      · have heq : item = gate := List.mem_singleton.mp hnew
        simpa [heq] using hg.2

theorem emit_fresh (state : Builder α Op) (gate : Gate α Op) :
    let (index, next) := (emit gate).run state
    index < next.inputCount + next.gates.size := by
  simp [emit]

theorem literal_valid (arity : Op → Nat) (state : Builder α Op) (value : α)
    (h : state.ValidFor arity) :
    let (result, next) := (literal value : Build α Op Nat).run state
    next.ValidFor arity ∧ next.inputCount = state.inputCount ∧
      next.gates.size = state.gates.size + 1 ∧
      result < next.inputCount + next.gates.size := by
  have hv := (emit_valid arity state (.constant value) h ⟨trivial, trivial⟩).2
  simp [literal, emit]
  exact hv

theorem unary_valid (arity : Op → Nat) (op : Op) (state : Builder α Op) (x : Nat)
    (h : state.ValidFor arity) (ha : arity op = 1)
    (hx : x < state.inputCount + state.gates.size) :
    let (result, next) := (unary op x).run state
    next.ValidFor arity ∧ next.inputCount = state.inputCount ∧
      next.gates.size = state.gates.size + 1 ∧
      result < next.inputCount + next.gates.size := by
  have hv := (emit_valid arity state (.apply op [x]) h
    ⟨(by simpa [Gate.ValidAt] using hx), (by simp [Gate.ArityValid, ha])⟩).2
  simp [unary, emit]
  exact hv

theorem binary_valid (arity : Op → Nat) (op : Op) (state : Builder α Op) (x y : Nat)
    (h : state.ValidFor arity) (ha : arity op = 2)
    (hx : x < state.inputCount + state.gates.size)
    (hy : y < state.inputCount + state.gates.size) :
    let (result, next) := (binary op x y).run state
    next.ValidFor arity ∧ next.inputCount = state.inputCount ∧
      next.gates.size = state.gates.size + 1 ∧
      result < next.inputCount + next.gates.size := by
  have hv := (emit_valid arity state (.apply op [x, y]) h
    ⟨(by simpa [Gate.ValidAt] using And.intro hx hy),
      (by simp [Gate.ArityValid, ha])⟩).2
  simp [binary, emit]
  exact hv

/-- A builder program whose state invariant and output bounds are proved
produces a strictly well-formed circuit, without reducing the complete code. -/
theorem build_valid (arity : Op → Nat) (inputCount : Nat)
    (program : Build α Op (List Nat))
    (h : ∀ state : Builder α Op, state.ValidFor arity → state.inputCount = inputCount →
      let (outputs, next) := program.run state
      next.ValidFor arity ∧ next.inputCount = inputCount ∧
        ∀ index ∈ outputs, index < next.inputCount + next.gates.size) :
    (build inputCount program).WellFormedFor arity inputCount := by
  let initial : Builder α Op := ⟨inputCount, #[]⟩
  have hinitial : initial.ValidFor arity := Builder.empty_valid arity inputCount
  cases hrun : program.run initial with
  | mk outputs next =>
    have hresult := h initial hinitial rfl
    simp only [hrun] at hresult
    obtain ⟨hnext, hcount, houtputs⟩ := hresult
    simp only [build, show (⟨inputCount, #[]⟩ : Builder α Op) = initial from rfl, hrun]
    refine ⟨⟨?_, ?_⟩, hnext.2⟩
    · simpa [hcount] using hnext.1
    · intro index member
      simpa [hcount, Array.length_toList] using houtputs index member

end S31.Graph
