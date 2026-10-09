import S31.Gadgets.FunctionalGraph

/-!
Multiple first-order field outputs of the typed functional core. Each output
is specialized in the same input environment, and all residual trees are
emitted into one straight-line graph. This models output binding without
silently dropping a second or later output.
-/

namespace S31.Functional

open Graph

def PolyList.emit {n : Nat} : List (Poly n) → FieldBuild (List Nat)
  | [] => pure []
  | poly :: rest => do
      let wire ← poly.emit
      let wires ← PolyList.emit rest
      return wire :: wires

def PolyList.code {n : Nat} (polys : List (Poly n)) : Code M31 FieldOp :=
  build n (PolyList.emit polys)

theorem PolyList.emit_valid {n : Nat} (polys : List (Poly n))
    (state : Builder M31 FieldOp)
    (hs : state.ValidFor fieldArity) (hcount : state.inputCount = n) :
    let (wires, next) := (PolyList.emit polys).run state
    next.ValidFor fieldArity ∧ next.inputCount = n ∧
      (∀ wire ∈ wires, wire < next.inputCount + next.gates.size) ∧
      state.gates.size ≤ next.gates.size := by
  induction polys generalizing state with
  | nil =>
      simp only [PolyList.emit, StateT.run_pure]
      exact ⟨hs, hcount, by simp, Nat.le_refl _⟩
  | cons poly rest ih =>
      cases hfirst : poly.emit.run state with
      | mk wire afterFirst =>
          have hp := poly.emit_valid state hs hcount
          simp only [hfirst] at hp
          cases hrest : (PolyList.emit rest).run afterFirst with
          | mk wires next =>
              have hr := ih afterFirst hp.1 hp.2.1
              simp only [hrest] at hr
              simp only [PolyList.emit, stateBindRun, hfirst, hrest]
              refine ⟨hr.1, hr.2.1, ?_, by omega⟩
              intro index member
              rcases List.mem_cons.mp member with rfl | htail
              · omega
              · exact hr.2.2.1 index htail

theorem PolyList.code_valid {n : Nat} (polys : List (Poly n)) :
    (PolyList.code polys).WellFormedFor fieldArity n := by
  unfold PolyList.code
  apply Graph.build_valid
  intro state hs hcount
  have hstep := PolyList.emit_valid polys state hs hcount
  cases hrun : (PolyList.emit polys).run state with
  | mk wires next =>
      simp only [hrun] at hstep
      exact ⟨hstep.1, hstep.2.1, hstep.2.2.1⟩

theorem PolyList.emit_prefix {n : Nat} (polys : List (Poly n))
    (state : Builder M31 FieldOp) :
    let (_, next) := (PolyList.emit polys).run state
    ∃ suffix, next.gates.toList = state.gates.toList ++ suffix := by
  induction polys generalizing state with
  | nil =>
      simp [PolyList.emit]
  | cons poly rest ih =>
      cases hfirst : poly.emit.run state with
      | mk wire afterFirst =>
          have hp := poly.emit_prefix state
          simp only [hfirst] at hp
          obtain ⟨first, hprefix⟩ := hp
          cases hrest : (PolyList.emit rest).run afterFirst with
          | mk wires next =>
              have hr := ih afterFirst
              simp only [hrest] at hr
              obtain ⟨second, hsuffix⟩ := hr
              simp only [PolyList.emit, stateBindRun, hfirst, hrest]
              exact ⟨first ++ second, by rw [hsuffix, hprefix, List.append_assoc]⟩

theorem PolyList.emit_values {n : Nat} (polys : List (Poly n))
    (state : Builder M31 FieldOp) (inputs : List M31)
    (hs : state.ValidFor fieldArity) (hcount : state.inputCount = n)
    (hinputs : inputs.length = n) :
    let (wires, next) := (PolyList.emit polys).run state
    wires.map ((Graph.run fieldEval next.gates.toList inputs).getD · 0) =
      polys.map (Poly.eval (fun i => inputs.getD i.val 0)) := by
  induction polys generalizing state with
  | nil =>
      simp [PolyList.emit]
  | cons poly rest ih =>
      cases hfirst : poly.emit.run state with
      | mk wire afterFirst =>
          have hp := poly.emit_value state inputs hs hcount hinputs
          simp only [hfirst] at hp
          have hv := poly.emit_valid state hs hcount
          simp only [hfirst] at hv
          cases hrest : (PolyList.emit rest).run afterFirst with
          | mk wires next =>
              have hr := ih afterFirst hv.1 hv.2.1
              simp only [hrest] at hr
              have hprefix := PolyList.emit_prefix rest afterFirst
              simp only [hrest] at hprefix
              obtain ⟨suffix, hsuffix⟩ := hprefix
              have hwireBound :
                  wire < (Graph.run fieldEval afterFirst.gates.toList inputs).length := by
                rw [Graph.run_length]
                simpa [hinputs, Array.length_toList, hv.2.1] using hv.2.2.1
              have hretained :
                  (Graph.run fieldEval next.gates.toList inputs).getD wire 0 =
                    poly.eval (fun i => inputs.getD i.val 0) := by
                rw [hsuffix, runPreservesPrefix _ _ _ _ hwireBound]
                exact hp
              simp only [PolyList.emit, stateBindRun, hfirst, hrest,
                List.map_cons]
              exact congrArg₂ List.cons hretained hr

theorem PolyList.code_eval {n : Nat} (polys : List (Poly n))
    (inputs : List M31) (hinputs : inputs.length = n) :
    (PolyList.code polys).eval fieldEval inputs =
      polys.map (Poly.eval (fun i => inputs.getD i.val 0)) := by
  let initial : Builder M31 FieldOp := ⟨n, #[]⟩
  have hstep := PolyList.emit_values polys initial inputs
    (Graph.Builder.empty_valid fieldArity n) rfl hinputs
  cases hrun : (PolyList.emit polys).run initial with
  | mk wires next =>
      simp only [hrun] at hstep
      simpa [PolyList.code, Graph.build, Graph.Code.eval, initial, hrun]
        using hstep

/-- Every claimed output is bound to its own source expression. The theorem
quantifies over arbitrary auxiliary gate witnesses through `strictAccepts`. -/
theorem programs_graph_accepts {n : Nat} (indices : List (Fin n))
    (programs : List (Expr (indices.map fun _ => .field) .field))
    (inputs output : List M31) (hinputs : inputs.length = n) :
    (PolyList.code (programs.map (fun e => specialize e (inputResidual indices)))).strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs output ↔
      output = programs.map (fun e => denote e
        (inputSource (fun i => inputs.getD i.val 0) indices)) := by
  rw [Gadgets.Hash.field_schedule_strict_sound_complete]
  simp only [hinputs, PolyList.code_valid, true_and]
  rw [PolyList.code_eval _ inputs hinputs]
  simp only [List.map_map]
  have hm := List.map_congr_left (l := programs)
    (f := (Poly.eval (fun i => inputs.getD i.val 0) ∘
      fun e => specialize e (inputResidual indices)))
    (g := fun e => denote e
      (inputSource (fun i => inputs.getD i.val 0) indices))
    (fun e _ => program_correct indices e (fun i => inputs.getD i.val 0))
  rw [hm]

/-- The second public output aliases the input. Reusing that wire costs no
extra gate, but the second output is still part of strict acceptance. -/
def capturedSquarePair : List (Expr [.field] .field) :=
  [capturedSquare, .var .here]

def capturedSquarePairCode : Code M31 FieldOp :=
  PolyList.code (capturedSquarePair.map
    (fun e => specialize e (inputResidual [(0 : Fin 1)])))

theorem capturedSquarePairCode_shape :
    capturedSquarePairCode =
      ⟨[.apply .mul [0, 0], .apply .add [1, 0]], [2, 0]⟩ := rfl

theorem capturedSquarePairCode_accepts (x : M31) (output : List M31) :
    capturedSquarePairCode.strictAccepts fieldArity
      Gadgets.Hash.fieldPrimitive [x] output ↔
      output = [x * x + x, x] := by
  simpa [capturedSquarePairCode, capturedSquarePair, inputSource,
    inputResidual, denote, capturedSquare, Env.get] using
    (programs_graph_accepts [(0 : Fin 1)] capturedSquarePair [x] output rfl)

theorem capturedSquarePair_rejects_forged_second (x y : M31)
    (hneq : y ≠ x) :
    ¬ capturedSquarePairCode.strictAccepts fieldArity
      Gadgets.Hash.fieldPrimitive [x] [x * x + x, y] := by
  intro h
  have hout := (capturedSquarePairCode_accepts x _).mp h
  exact hneq (List.cons.inj (List.cons.inj hout).2).1

end S31.Functional
