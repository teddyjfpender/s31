import S31.Semantics.Functional
import S31.Gadgets.Hash
import S31.Gadgets.BuilderValidity

/-!
An executable lowering of the functional core's residual polynomial into the
same straight-line graph model used by the S31 hash-circuit proofs. The exact
worked example is proved below. A universal compiler-correctness theorem for
this lowering and correspondence to production Zig AIR remain open.
-/

namespace S31.Functional

open Graph

private theorem stateBindRun {σ α β : Type} (action : StateM σ α)
    (next : α → StateM σ β) (state : σ) :
    (action >>= next).run state =
      (next (action.run state).1).run (action.run state).2 := rfl

private theorem runAppend (first second : List (Gate M31 FieldOp))
    (values : List M31) :
    Graph.run fieldEval (first ++ second) values =
      Graph.run fieldEval second (Graph.run fieldEval first values) := by
  induction first generalizing values with
  | nil => rfl
  | cons gate rest ih =>
      simp only [List.cons_append, Graph.run]
      exact ih (values ++ [gate.eval fieldEval values])

private theorem runPreserves (gates : List (Gate M31 FieldOp))
    (values : List M31) (index : Nat) (hindex : index < values.length) :
    (Graph.run fieldEval gates values).getD index 0 = values.getD index 0 := by
  induction gates generalizing values with
  | nil => rfl
  | cons gate rest ih =>
      change (Graph.run fieldEval rest (values ++ [gate.eval fieldEval values])).getD index 0 = _
      rw [ih (values ++ [gate.eval fieldEval values]) (by simp; omega)]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hindex]

private theorem getD_append_singleton (values : List M31) (x : M31) :
    (values ++ [x]).getD values.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

private theorem runPreservesPrefix (first second : List (Gate M31 FieldOp))
    (inputs : List M31) (index : Nat)
    (hindex : index < (Graph.run fieldEval first inputs).length) :
    (Graph.run fieldEval (first ++ second) inputs).getD index 0 =
      (Graph.run fieldEval first inputs).getD index 0 := by
  rw [runAppend]
  exact runPreserves second _ index hindex

private theorem runAppendedGate (gates : List (Gate M31 FieldOp))
    (inputs : List M31) (gate : Gate M31 FieldOp) :
    (Graph.run fieldEval (gates ++ [gate]) inputs).getD
      (inputs.length + gates.length) 0 =
      gate.eval fieldEval (Graph.run fieldEval gates inputs) := by
  rw [runAppend]
  change (Graph.run fieldEval gates inputs ++
    [gate.eval fieldEval (Graph.run fieldEval gates inputs)]).getD
      (inputs.length + gates.length) 0 = _
  rw [← Graph.run_length fieldEval gates inputs]
  exact getD_append_singleton _ _

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

/-- Emission preserves a valid builder, keeps the input prefix fixed, returns
a live wire and never removes gates. The last condition keeps the left operand
live while the right subtree is emitted. -/
theorem Poly.emit_valid {n : Nat} (poly : Poly n) (state : Builder M31 FieldOp)
    (hs : state.ValidFor fieldArity) (hcount : state.inputCount = n) :
    let (wire, next) := poly.emit.run state
    next.ValidFor fieldArity ∧ next.inputCount = n ∧
      wire < next.inputCount + next.gates.size ∧
      state.gates.size ≤ next.gates.size := by
  induction poly generalizing state with
  | input i =>
      simp only [Poly.emit, StateT.run_pure]
      exact ⟨hs, hcount, by omega, Nat.le_refl _⟩
  | literal value =>
      have h := Graph.literal_valid fieldArity state value hs
      simp only [Poly.emit]
      cases hrun : (Graph.literal value : FieldBuild Nat).run state with
      | mk wire next =>
          simp only [hrun] at h
          exact ⟨h.1, h.2.1.trans hcount, h.2.2.2, by omega⟩
  | add lhs rhs ihl ihr =>
      cases hleft : lhs.emit.run state with
      | mk left afterLeft =>
          have hl := ihl state hs hcount
          simp only [hleft] at hl
          cases hright : rhs.emit.run afterLeft with
          | mk right afterRight =>
              have hr := ihr afterLeft hl.1 hl.2.1
              simp only [hright] at hr
              have leftLive : left < afterRight.inputCount + afterRight.gates.size := by omega
              have hb := Graph.binary_valid fieldArity .add afterRight left right hr.1
                rfl leftLive hr.2.2.1
              simp only [Poly.emit, stateBindRun, hleft, hright]
              cases hbinary : (Graph.binary .add left right).run afterRight with
              | mk wire next =>
                  simp only [hbinary] at hb ⊢
                  exact ⟨hb.1, hb.2.1.trans hr.2.1, hb.2.2.2, by omega⟩
  | mul lhs rhs ihl ihr =>
      cases hleft : lhs.emit.run state with
      | mk left afterLeft =>
          have hl := ihl state hs hcount
          simp only [hleft] at hl
          cases hright : rhs.emit.run afterLeft with
          | mk right afterRight =>
              have hr := ihr afterLeft hl.1 hl.2.1
              simp only [hright] at hr
              have leftLive : left < afterRight.inputCount + afterRight.gates.size := by omega
              have hb := Graph.binary_valid fieldArity .mul afterRight left right hr.1
                rfl leftLive hr.2.2.1
              simp only [Poly.emit, stateBindRun, hleft, hright]
              cases hbinary : (Graph.binary .mul left right).run afterRight with
              | mk wire next =>
                  simp only [hbinary] at hb ⊢
                  exact ⟨hb.1, hb.2.1.trans hr.2.1, hb.2.2.2, by omega⟩

/-- Every residual polynomial, not only the worked example, emits a graph
with valid wire indices, exact primitive arities and a live output. -/
theorem Poly.code_valid {n : Nat} (poly : Poly n) :
    poly.code.WellFormedFor fieldArity n := by
  unfold Poly.code
  apply Graph.build_valid
  intro state hs hcount
  have hstep := poly.emit_valid state hs hcount
  change (let (wire, next) := poly.emit.run state
    next.ValidFor fieldArity ∧ next.inputCount = n ∧
      ∀ index ∈ [wire], index < next.inputCount + next.gates.size)
  cases hrun : poly.emit.run state with
  | mk wire next =>
      simp only [hrun] at hstep
      refine ⟨hstep.1, hstep.2.1, ?_⟩
      intro index member
      simp only [List.mem_singleton] at member
      subst index
      exact hstep.2.2.1

/-- Emission appends gates to the existing graph without changing earlier
gates. This is the structural premise used in semantic composition. -/
theorem Poly.emit_prefix {n : Nat} (poly : Poly n)
    (state : Builder M31 FieldOp) :
    let (_, next) := poly.emit.run state
    ∃ suffix, next.gates.toList = state.gates.toList ++ suffix := by
  induction poly generalizing state with
  | input i =>
      simp [Poly.emit]
  | literal x =>
      refine ⟨[.constant x], ?_⟩
      simp [Array.toList_push]
  | add lhs rhs ihl ihr =>
      cases hleft : lhs.emit.run state with
      | mk left afterLeft =>
          have hl := ihl state
          simp only [hleft] at hl
          obtain ⟨first, hfirst⟩ := hl
          cases hright : rhs.emit.run afterLeft with
          | mk right afterRight =>
              have hr := ihr afterLeft
              simp only [hright] at hr
              obtain ⟨second, hsecond⟩ := hr
              simp only [Poly.emit, stateBindRun, hleft, hright]
              refine ⟨first ++ second ++ [.apply .add [left, right]], ?_⟩
              simp [Array.toList_push, hsecond, hfirst,
                List.append_assoc]
  | mul lhs rhs ihl ihr =>
      cases hleft : lhs.emit.run state with
      | mk left afterLeft =>
          have hl := ihl state
          simp only [hleft] at hl
          obtain ⟨first, hfirst⟩ := hl
          cases hright : rhs.emit.run afterLeft with
          | mk right afterRight =>
              have hr := ihr afterLeft
              simp only [hright] at hr
              obtain ⟨second, hsecond⟩ := hr
              simp only [Poly.emit, stateBindRun, hleft, hright]
              refine ⟨first ++ second ++ [.apply .mul [left, right]], ?_⟩
              simp [Array.toList_push, hsecond, hfirst,
                List.append_assoc]

/-- Evaluating the emitted graph at its returned wire agrees with the
polynomial for any valid existing builder prefix and any input assignment. -/
theorem Poly.emit_value {n : Nat} (poly : Poly n)
    (state : Builder M31 FieldOp) (inputs : List M31)
    (hs : state.ValidFor fieldArity) (hcount : state.inputCount = n)
    (hinputs : inputs.length = n) :
    let (wire, next) := poly.emit.run state
    (Graph.run fieldEval next.gates.toList inputs).getD wire 0 =
      poly.eval (fun i => inputs.getD i.val 0) := by
  induction poly generalizing state with
  | input i =>
      simp only [Poly.emit, StateT.run_pure, Poly.eval]
      exact runPreserves state.gates.toList inputs i.val (by omega)
  | literal x =>
      simp only [Poly.emit, Poly.eval]
      simpa [Graph.literal, Graph.emit, Array.toList_push, hcount, hinputs]
        using runAppendedGate state.gates.toList inputs (.constant x)
  | add lhs rhs ihl ihr =>
      cases hleft : lhs.emit.run state with
      | mk left afterLeft =>
          have hl := ihl state hs hcount
          simp only [hleft] at hl
          have hvalidLeft := lhs.emit_valid state hs hcount
          simp only [hleft] at hvalidLeft
          cases hright : rhs.emit.run afterLeft with
          | mk right afterRight =>
              have hr := ihr afterLeft hvalidLeft.1 hvalidLeft.2.1
              simp only [hright] at hr
              have hvalidRight := rhs.emit_valid afterLeft hvalidLeft.1 hvalidLeft.2.1
              simp only [hright] at hvalidRight
              have hp := rhs.emit_prefix afterLeft
              simp only [hright] at hp
              obtain ⟨suffix, hprefix⟩ := hp
              have hleftBound :
                  left < (Graph.run fieldEval afterLeft.gates.toList inputs).length := by
                rw [Graph.run_length]
                simpa [hinputs, Array.length_toList, hvalidLeft.2.1] using hvalidLeft.2.2.1
              have hleftRetained :
                  (Graph.run fieldEval afterRight.gates.toList inputs).getD left 0 =
                    lhs.eval (fun i => inputs.getD i.val 0) := by
                rw [hprefix, runPreservesPrefix _ _ _ _ hleftBound]
                exact hl
              simp only [Poly.emit, stateBindRun, hleft, hright, Poly.eval]
              have hgate := runAppendedGate afterRight.gates.toList inputs
                (.apply .add [left, right])
              change
                (Graph.run fieldEval (afterRight.gates.toList ++
                  [.apply .add [left, right]]) inputs).getD
                    (inputs.length + afterRight.gates.toList.length) 0 =
                  (Graph.run fieldEval afterRight.gates.toList inputs).getD left 0 +
                    (Graph.run fieldEval afterRight.gates.toList inputs).getD right 0 at hgate
              rw [hleftRetained, hr] at hgate
              simpa [Graph.binary, Graph.emit, Array.toList_push,
                hinputs, hvalidRight.2.1, Array.length_toList] using hgate

  | mul lhs rhs ihl ihr =>
      cases hleft : lhs.emit.run state with
      | mk left afterLeft =>
          have hl := ihl state hs hcount
          simp only [hleft] at hl
          have hvalidLeft := lhs.emit_valid state hs hcount
          simp only [hleft] at hvalidLeft
          cases hright : rhs.emit.run afterLeft with
          | mk right afterRight =>
              have hr := ihr afterLeft hvalidLeft.1 hvalidLeft.2.1
              simp only [hright] at hr
              have hvalidRight := rhs.emit_valid afterLeft hvalidLeft.1 hvalidLeft.2.1
              simp only [hright] at hvalidRight
              have hp := rhs.emit_prefix afterLeft
              simp only [hright] at hp
              obtain ⟨suffix, hprefix⟩ := hp
              have hleftBound :
                  left < (Graph.run fieldEval afterLeft.gates.toList inputs).length := by
                rw [Graph.run_length]
                simpa [hinputs, Array.length_toList, hvalidLeft.2.1] using hvalidLeft.2.2.1
              have hleftRetained :
                  (Graph.run fieldEval afterRight.gates.toList inputs).getD left 0 =
                    lhs.eval (fun i => inputs.getD i.val 0) := by
                rw [hprefix, runPreservesPrefix _ _ _ _ hleftBound]
                exact hl
              simp only [Poly.emit, stateBindRun, hleft, hright, Poly.eval]
              have hgate := runAppendedGate afterRight.gates.toList inputs
                (.apply .mul [left, right])
              change
                (Graph.run fieldEval (afterRight.gates.toList ++
                  [.apply .mul [left, right]]) inputs).getD
                    (inputs.length + afterRight.gates.toList.length) 0 =
                  (Graph.run fieldEval afterRight.gates.toList inputs).getD left 0 *
                    (Graph.run fieldEval afterRight.gates.toList inputs).getD right 0 at hgate
              rw [hleftRetained, hr] at hgate
              simpa [Graph.binary, Graph.emit, Array.toList_push,
                hinputs, hvalidRight.2.1, Array.length_toList] using hgate

/-- Universal semantic preservation of residual polynomial graph lowering. -/
theorem Poly.code_eval {n : Nat} (poly : Poly n) (inputs : List M31)
    (hinputs : inputs.length = n) :
    poly.code.eval fieldEval inputs =
      [poly.eval (fun i => inputs.getD i.val 0)] := by
  let initial : Builder M31 FieldOp := ⟨n, #[]⟩
  have hstep := poly.emit_value initial inputs
    (Graph.Builder.empty_valid fieldArity n) rfl hinputs
  cases hrun : poly.emit.run initial with
  | mk wire next =>
      simp only [hrun] at hstep
      simpa [Poly.code, Graph.build, Graph.Code.eval, initial, hrun]
        using hstep

/-- A strict graph proof exists exactly for the polynomial's value; all
intermediate gate witnesses are quantified by `strictAccepts`. -/
theorem Poly.code_accepts {n : Nat} (poly : Poly n)
    (inputs output : List M31) (hinputs : inputs.length = n) :
    poly.code.strictAccepts fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
      output = [poly.eval (fun i => inputs.getD i.val 0)] := by
  rw [Gadgets.Hash.field_schedule_strict_sound_complete]
  simp [hinputs, poly.code_valid, poly.code_eval inputs hinputs]

/-- End-to-end theorem for the typed total source core through specialization,
polynomial graph emission and arbitrary-witness strict circuit acceptance. -/
theorem program_graph_accepts {n : Nat} (indices : List (Fin n))
    (e : Expr (indices.map fun _ => .field) .field)
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (specialize e (inputResidual indices)).code.strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
      output = [denote e (inputSource (fun i => inputs.getD i.val 0) indices)] := by
  rw [Poly.code_accepts _ inputs output hinputs]
  rw [program_correct]

/-- The actual residual core, once beta-reduced, emits two gates. The output
index 2 is the new add gate; inputs occupy the prefix at index 0. -/
def capturedSquareCode : Code M31 FieldOp :=
  (specialize capturedSquare (inputResidual [(0 : Fin 1)])).code

theorem capturedSquareCode_shape :
    capturedSquareCode = ⟨[.apply .mul [0, 0], .apply .add [1, 0]], [2]⟩ := rfl

theorem capturedSquareCode_valid :
    capturedSquareCode.WellFormedFor fieldArity 1 := by
  exact Poly.code_valid _

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
