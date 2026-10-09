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
