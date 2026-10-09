import S31.Gadgets.FunctionalArrays
import S31.Gadgets.FunctionalConditional

/-!
An eager, array-valued conditional in the total functional core. The selector
and both complete branches enter one strict graph. A separate pointwise select
relation constrains one shared selector bit and every output lane. This is a
source/graph theorem, not a proof of production Python or Zig lowering.
-/

namespace S31.Functional

open Graph

def arrayChoiceWords {m : Nat} (selector : M31)
    (onTrue onFalse : Fin m → M31) : Fin ((1 + m) + m) → M31 :=
  Fin.append (Fin.append (fun _ : Fin 1 => selector) onTrue) onFalse

theorem arrayChoiceWords_eq_iff {m : Nat}
    (selector selector' : M31)
    (onTrue onFalse onTrue' onFalse' : Fin m → M31) :
    arrayChoiceWords selector onTrue onFalse =
      arrayChoiceWords selector' onTrue' onFalse' ↔
      selector = selector' ∧ onTrue = onTrue' ∧ onFalse = onFalse' := by
  constructor
  · intro h
    have hprefix : Fin.append (fun _ : Fin 1 => selector) onTrue =
        Fin.append (fun _ : Fin 1 => selector') onTrue' := by
      funext i
      have hi := congrFun h (Fin.castAdd m i)
      simpa [arrayChoiceWords] using hi
    have hfalse : onFalse = onFalse' := by
      funext i
      have hi := congrFun h (Fin.natAdd (1 + m) i)
      simpa [arrayChoiceWords] using hi
    have hs : selector = selector' := by
      have hi := congrFun hprefix (Fin.castAdd m (0 : Fin 1))
      simpa using hi
    have ht : onTrue = onTrue' := by
      funext i
      have hi := congrFun hprefix (Fin.natAdd 1 i)
      simpa using hi
    exact ⟨hs, ht, hfalse⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

def arraySelect {m : Nat} (selector : M31)
    (onFalse onTrue output : Fin m → M31) : Prop :=
  (selector = 0 ∨ selector = 1) ∧
    ∀ i, fieldSelect selector (onFalse i) (onTrue i) (output i)

theorem array_select_iff {m : Nat} (selector : M31)
    (onFalse onTrue output : Fin m → M31) :
    arraySelect selector onFalse onTrue output ↔
      (selector = 0 ∧ output = onFalse) ∨
      (selector = 1 ∧ output = onTrue) := by
  constructor
  · rintro ⟨hbit, hlanes⟩
    have h01 : (0 : M31) ≠ 1 := by decide
    rcases hbit with hzero | hone
    · left
      refine ⟨hzero, funext fun i => ?_⟩
      rcases (field_select_iff _ _ _ _).mp (hlanes i) with hfalse | htrue
      · exact hfalse.2
      · exact False.elim (h01 (hzero.symm.trans htrue.1))
    · right
      refine ⟨hone, funext fun i => ?_⟩
      rcases (field_select_iff _ _ _ _).mp (hlanes i) with hfalse | htrue
      · exact False.elim (h01 (hfalse.1.symm.trans hone))
      · exact htrue.2
  · rintro (⟨hzero, rfl⟩ | ⟨hone, rfl⟩)
    · exact ⟨Or.inl hzero, fun i => (field_select_iff _ _ _ _).mpr
        (Or.inl ⟨hzero, rfl⟩)⟩
    · exact ⟨Or.inr hone, fun i => (field_select_iff _ _ _ _).mpr
        (Or.inr ⟨hone, rfl⟩)⟩

def arrayIfTerm {n m : Nat}
    (selector : Expr [.array n] .field)
    (onTrue onFalse : Expr [.array n] (.array m)) :
    Expr [.array n] (.array ((1 + m) + m)) :=
  .arrayConcat (.arrayConcat (.arraySplat selector) onTrue) onFalse

theorem arrayIfTerm_denote {n m : Nat}
    (selector : Expr [.array n] .field)
    (onTrue onFalse : Expr [.array n] (.array m))
    (env : Env Meaning [.array n]) :
    denote (arrayIfTerm selector onTrue onFalse) env =
      arrayChoiceWords (denote selector env) (denote onTrue env)
        (denote onFalse env) := rfl

def ArrayIfAccepts {n m : Nat}
    (selector : Expr [.array n] .field)
    (onTrue onFalse : Expr [.array n] (.array m))
    (inputs : List M31) (output : Fin m → M31) : Prop :=
  ∃ s t f,
    (arrayCode (arrayIfTerm selector onTrue onFalse)).strictAccepts
      fieldArity Gadgets.Hash.fieldPrimitive inputs
      (List.ofFn (arrayChoiceWords s t f)) ∧
    arraySelect s f t output

/-- Arbitrary intermediate graph and selection witnesses bind all array
lanes to the selected source branch. The converse gives honest witnesses. -/
theorem array_if_accepts_iff {n m : Nat}
    (selector : Expr [.array n] .field)
    (onTrue onFalse : Expr [.array n] (.array m))
    (inputs : List M31) (output : Fin m → M31)
    (hinputs : inputs.length = n) :
    ArrayIfAccepts selector onTrue onFalse inputs output ↔
      (denote selector (arrayInputSource (fun i => inputs.getD i.val 0)) = 0 ∧
       output = denote onFalse (arrayInputSource (fun i => inputs.getD i.val 0))) ∨
      (denote selector (arrayInputSource (fun i => inputs.getD i.val 0)) = 1 ∧
       output = denote onTrue (arrayInputSource (fun i => inputs.getD i.val 0))) := by
  let env := arrayInputSource (n := n) (fun i => inputs.getD i.val 0)
  have hgraph (s : M31) (t f : Fin m → M31) :
      (arrayCode (arrayIfTerm selector onTrue onFalse)).strictAccepts
        fieldArity Gadgets.Hash.fieldPrimitive inputs
        (List.ofFn (arrayChoiceWords s t f)) ↔
      s = denote selector env ∧ t = denote onTrue env ∧
        f = denote onFalse env := by
    rw [arrayCode_accepts _ _ _ hinputs]
    rw [arrayIfTerm_denote]
    exact (List.ofFn_inj).trans (arrayChoiceWords_eq_iff _ _ _ _ _ _)
  constructor
  · rintro ⟨s, t, f, acceptedGraph, acceptedSelect⟩
    obtain ⟨hs, ht, hf⟩ := (hgraph s t f).mp acceptedGraph
    subst s
    subst t
    subst f
    exact (array_select_iff _ _ _ _).mp acceptedSelect
  · intro selected
    refine ⟨denote selector env, denote onTrue env, denote onFalse env, ?_, ?_⟩
    · exact (hgraph _ _ _).mpr ⟨rfl, rfl, rfl⟩
    · exact (array_select_iff _ _ _ _).mpr selected

/-- A two-lane worked example. The first input is the selector; the second
is copied to both output lanes when selected, otherwise both lanes are seven. -/
def chooseOrSevenSelector : Expr [.array 2] .field :=
  .arrayGet (.var .here) 0

def chooseOrSevenTrue : Expr [.array 2] (.array 2) :=
  .arraySplat (.arrayGet (.var .here) 1)

def chooseOrSevenFalse : Expr [.array 2] (.array 2) :=
  .arraySplat (.literal (RiscvRefinement.M31.reduce 7))

theorem chooseOrSeven_accepts (bit value : M31) (output : Fin 2 → M31) :
    ArrayIfAccepts chooseOrSevenSelector chooseOrSevenTrue chooseOrSevenFalse
      [bit, value] output ↔
      (bit = 0 ∧ output = fun _ => RiscvRefinement.M31.reduce 7) ∨
      (bit = 1 ∧ output = fun _ => value) := by
  simpa [chooseOrSevenSelector, chooseOrSevenTrue, chooseOrSevenFalse,
    arrayInputSource, denote, Env.get] using
    (array_if_accepts_iff chooseOrSevenSelector chooseOrSevenTrue
      chooseOrSevenFalse [bit, value] output rfl)

end S31.Functional
