import S31.Gadgets.FunctionalOutputs
import S31.Gadgets.Boolean

/-!
A witness-dependent choice over the total typed field/function core. Both
branches are emitted into one graph. The separate select relation constrains
the selector to a bit and binds the chosen output for arbitrary gate witnesses.
Partial operations are absent from this core; the Python effect checker that
enforces that premise is not verified here.
-/

namespace S31.Functional

open Graph

def fieldSelect (selector onFalse onTrue output : M31) : Prop :=
  Gadgets.selectConstraint (Field.toZMod selector) (Field.toZMod onFalse)
    (Field.toZMod onTrue) (Field.toZMod output)

theorem field_select_iff (selector onFalse onTrue output : M31) :
    fieldSelect selector onFalse onTrue output ↔
      (selector = 0 ∧ output = onFalse) ∨
      (selector = 1 ∧ output = onTrue) := by
  constructor
  · intro accepted
    change Gadgets.selectConstraint (Field.toZMod selector)
      (Field.toZMod onFalse) (Field.toZMod onTrue) (Field.toZMod output) at accepted
    obtain ⟨choice, hchoice⟩ := Gadgets.bit_has_bool (Field.toZMod selector) accepted.1
    cases choice with
    | false =>
        have hs : selector = 0 := Field.toZMod_injective
          (by simpa [Gadgets.encodeBool, Field.toZMod_zero] using hchoice)
        rw [hchoice] at accepted
        have hout := (Gadgets.select_sound_complete false
          (Field.toZMod onFalse) (Field.toZMod onTrue) (Field.toZMod output)).mp accepted
        exact Or.inl ⟨hs, Field.toZMod_injective (by simpa using hout)⟩
    | true =>
        have hs : selector = 1 := Field.toZMod_injective
          (by simpa [Gadgets.encodeBool, Field.toZMod_one] using hchoice)
        rw [hchoice] at accepted
        have hout := (Gadgets.select_sound_complete true
          (Field.toZMod onFalse) (Field.toZMod onTrue) (Field.toZMod output)).mp accepted
        exact Or.inr ⟨hs, Field.toZMod_injective (by simpa using hout)⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      simp [fieldSelect, Field.toZMod_zero, Field.toZMod_one,
        Gadgets.selectConstraint, Gadgets.bit]

def ifCode {n : Nat} (indices : List (Fin n))
    (selector onTrue onFalse : Expr (indices.map fun _ => .field) .field) :
    Code M31 FieldOp :=
  PolyList.code ([selector, onTrue, onFalse].map
    (fun e => specialize e (inputResidual indices)))

/-- All three source expressions are evaluated in the same graph. The result
is constrained by a separate selector equation, independently of the source
interpreter. -/
def IfAccepts {n : Nat} (indices : List (Fin n))
    (selector onTrue onFalse : Expr (indices.map fun _ => .field) .field)
    (inputs : List M31) (output : M31) : Prop :=
  ∃ s t f,
    (ifCode indices selector onTrue onFalse).strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs [s, t, f] ∧
    fieldSelect s f t output

/-- For every satisfying intermediate graph witness and selector witness,
the result is exactly the selected source value. The converse constructs
honest witnesses for either selector value. -/
theorem if_accepts_iff {n : Nat} (indices : List (Fin n))
    (selector onTrue onFalse : Expr (indices.map fun _ => .field) .field)
    (inputs : List M31) (output : M31) (hinputs : inputs.length = n) :
    IfAccepts indices selector onTrue onFalse inputs output ↔
      (denote selector (inputSource (fun i => inputs.getD i.val 0) indices) = 0 ∧
       output = denote onFalse (inputSource (fun i => inputs.getD i.val 0) indices)) ∨
      (denote selector (inputSource (fun i => inputs.getD i.val 0) indices) = 1 ∧
       output = denote onTrue (inputSource (fun i => inputs.getD i.val 0) indices)) := by
  let env := inputSource (fun i => inputs.getD i.val 0) indices
  have hgraph := programs_graph_accepts indices [selector, onTrue, onFalse]
    inputs
  constructor
  · rintro ⟨s, t, f, acceptedGraph, acceptedSelect⟩
    have hvalues := (hgraph [s, t, f] hinputs).mp acceptedGraph
    change [s, t, f] = [denote selector env, denote onTrue env, denote onFalse env] at hvalues
    have hs : s = denote selector env := (List.cons.inj hvalues).1
    have ht : t = denote onTrue env := (List.cons.inj (List.cons.inj hvalues).2).1
    have hf : f = denote onFalse env :=
      (List.cons.inj (List.cons.inj (List.cons.inj hvalues).2).2).1
    subst s
    subst t
    subst f
    exact (field_select_iff _ _ _ _).mp acceptedSelect
  · intro selected
    refine ⟨denote selector env, denote onTrue env, denote onFalse env, ?_, ?_⟩
    · exact (hgraph _ hinputs).mpr rfl
    · exact (field_select_iff _ _ _ _).mpr selected

end S31.Functional
