import S31.Gadgets.Functional.Arrays
import S31.Gadgets.Functional.Conditional
import S31.Semantics.Node

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

/-- This is exactly the validity check and branch order of the normalized
relation IR's `select` evaluator for M31 arrays. -/
def normalizedArraySelect {m : Nat} (selector : M31)
    (onFalse onTrue output : Fin m → M31) : Prop :=
  selector.val ≤ 1 ∧
    output = if selector.val == 0 then onFalse else onTrue

theorem array_select_iff_normalized {m : Nat} (selector : M31)
    (onFalse onTrue output : Fin m → M31) :
    arraySelect selector onFalse onTrue output ↔
      normalizedArraySelect selector onFalse onTrue output := by
  rw [array_select_iff]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · have hz : (0 : M31).val = 0 := rfl
      simp [normalizedArraySelect, hz]
    · have ho : (1 : M31).val = 1 := rfl
      simp [normalizedArraySelect, ho]
  · rintro ⟨hbit, houtput⟩
    have hcases : selector.val = 0 ∨ selector.val = 1 := by omega
    rcases hcases with hzero | hone
    · left
      have hs : selector = 0 := RiscvRefinement.M31.ext (by simpa using hzero)
      exact ⟨hs, by simpa [normalizedArraySelect, hzero] using houtput⟩
    · right
      have hs : selector = 1 := RiscvRefinement.M31.ext (by simpa using hone)
      exact ⟨hs, by simpa [normalizedArraySelect, hone] using houtput⟩

/-- A concrete normalized-IR select node and its three already validated
operands. This names false, true and selector separately so their order is
visible in the evaluator statement. -/
def normalizedSelectNode : Node :=
  { name := "out", op := .select, lhs := some "false_arm",
    rhs := some "true_arm", selector := some "selector" }

def normalizedSelectEnv {m : Nat} (selector : M31)
    (onFalse onTrue : Fin m → M31) : S31.Env :=
  [("false_arm", ⟨.m31, List.ofFn onFalse⟩),
   ("true_arm", ⟨.m31, List.ofFn onTrue⟩),
   ("selector", ⟨.m31, [selector]⟩)]

theorem normalizedSelectNode_shape {m : Nat} (selector : M31)
    (onFalse onTrue : Fin m → M31) :
    inferNode ((normalizedSelectEnv selector onFalse onTrue).map
      (fun (name, value) => (name, value.shape))) normalizedSelectNode =
      .ok ⟨.m31, m⟩ := by
  have hshape : ((⟨.m31, m⟩ : Shape) == ⟨.m31, m⟩) = true := by
    change ((Kind.m31 == Kind.m31) && (m == m)) = true
    simp [show (Kind.m31 == Kind.m31) = true by rfl]
  have hkind : (Kind.m31 == Kind.m31) = true := by rfl
  simp [normalizedSelectNode, normalizedSelectEnv, inferNode,
    Node.metadataValid, Node.fields, shapeOperand, expectShape,
    lookup, Value.shape, need, require, Except.map, Bind.bind, Except.bind,
    hshape, hkind]
  rfl

theorem normalizedSelectNode_eval {m : Nat} (selector : M31)
    (onFalse onTrue : Fin m → M31) (hbit : selector.val ≤ 1) :
    evaluateNode (normalizedSelectEnv selector onFalse onTrue)
      normalizedSelectNode =
      .ok ⟨.m31, List.ofFn
        (if selector.val == 0 then onFalse else onTrue)⟩ := by
  unfold evaluateNode
  rw [normalizedSelectNode_shape selector onFalse onTrue]
  have hshape : ((⟨.m31, m⟩ : Shape) == ⟨.m31, m⟩) = true := by
    change ((Kind.m31 == Kind.m31) && (m == m)) = true
    simp [show (Kind.m31 == Kind.m31) = true by rfl]
  by_cases hzero : selector.val = 0
  · simp [normalizedSelectNode, normalizedSelectEnv, valueOperand, lookup,
      require, hzero, Value.shape, Value.valid, Bind.bind, Except.bind]
    have hpure : (pure (List.ofFn onFalse) : Result (List M31)) =
        .ok (List.ofFn onFalse) := rfl
    rw [hpure]
    simp [hshape]
    rfl
  · simp [normalizedSelectNode, normalizedSelectEnv, valueOperand, lookup,
      require, hzero, Value.shape, Value.valid, Bind.bind, Except.bind]
    have hpure : (pure (List.ofFn onTrue) : Result (List M31)) =
        .ok (List.ofFn onTrue) := rfl
    rw [hpure]
    simp [hbit, hshape]
    rfl

theorem normalizedSelectNode_rejects_invalid {m : Nat} (selector : M31)
    (onFalse onTrue : Fin m → M31) (hbit : ¬ selector.val ≤ 1) :
    evaluateNode (normalizedSelectEnv selector onFalse onTrue)
      normalizedSelectNode = .error .invalidValue := by
  unfold evaluateNode
  rw [normalizedSelectNode_shape selector onFalse onTrue]
  simp [normalizedSelectNode, normalizedSelectEnv, valueOperand, lookup,
    require, hbit, Bind.bind, Except.bind]

/-- The actual normalized relation evaluator accepts exactly the pointwise
selection constraint for these M31-array operands, including rejection of a
selector outside `{0,1}`. -/
theorem array_select_iff_evaluateNode {m : Nat} (selector : M31)
    (onFalse onTrue output : Fin m → M31) :
    arraySelect selector onFalse onTrue output ↔
      evaluateNode (normalizedSelectEnv selector onFalse onTrue)
        normalizedSelectNode = .ok ⟨.m31, List.ofFn output⟩ := by
  constructor
  · intro accepted
    obtain ⟨hbit, hout⟩ :=
      (array_select_iff_normalized selector onFalse onTrue output).mp accepted
    rw [normalizedSelectNode_eval selector onFalse onTrue hbit]
    simp [hout]
  · intro accepted
    by_cases hbit : selector.val ≤ 1
    · rw [normalizedSelectNode_eval selector onFalse onTrue hbit] at accepted
      have hwords : List.ofFn (if selector.val == 0 then onFalse else onTrue) =
          List.ofFn output := congrArg Value.words (Except.ok.inj accepted)
      have hout : output = if selector.val == 0 then onFalse else onTrue :=
        ((List.ofFn_inj).mp hwords).symm
      exact (array_select_iff_normalized selector onFalse onTrue output).mpr
        ⟨hbit, hout⟩
    · rw [normalizedSelectNode_rejects_invalid selector onFalse onTrue hbit]
        at accepted
      cases accepted

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

/-- Source conditional acceptance agrees with the normalized IR `select`
rule, including its canonical selector check and false/true operand order. -/
theorem array_if_accepts_iff_normalized {n m : Nat}
    (selector : Expr [.array n] .field)
    (onTrue onFalse : Expr [.array n] (.array m))
    (inputs : List M31) (output : Fin m → M31)
    (hinputs : inputs.length = n) :
    ArrayIfAccepts selector onTrue onFalse inputs output ↔
      normalizedArraySelect
        (denote selector (arrayInputSource (fun i => inputs.getD i.val 0)))
        (denote onFalse (arrayInputSource (fun i => inputs.getD i.val 0)))
        (denote onTrue (arrayInputSource (fun i => inputs.getD i.val 0)))
        output := by
  let env := arrayInputSource (n := n) (fun i => inputs.getD i.val 0)
  exact (array_if_accepts_iff selector onTrue onFalse inputs output hinputs).trans
    (((array_select_iff (denote selector env) (denote onFalse env)
      (denote onTrue env) output).symm).trans
      (array_select_iff_normalized (denote selector env)
        (denote onFalse env) (denote onTrue env) output))

/-- The source conditional's one-graph constraint model agrees with the
executable normalized `select` node on the denoted operands, for every input
assignment and every candidate output. -/
theorem array_if_accepts_iff_evaluateNode {n m : Nat}
    (selector : Expr [.array n] .field)
    (onTrue onFalse : Expr [.array n] (.array m))
    (inputs : List M31) (output : Fin m → M31)
    (hinputs : inputs.length = n) :
    ArrayIfAccepts selector onTrue onFalse inputs output ↔
      evaluateNode
        (normalizedSelectEnv
          (denote selector (arrayInputSource (fun i => inputs.getD i.val 0)))
          (denote onFalse (arrayInputSource (fun i => inputs.getD i.val 0)))
          (denote onTrue (arrayInputSource (fun i => inputs.getD i.val 0))))
        normalizedSelectNode = .ok ⟨.m31, List.ofFn output⟩ := by
  let env := arrayInputSource (n := n) (fun i => inputs.getD i.val 0)
  exact (array_if_accepts_iff_normalized selector onTrue onFalse
    inputs output hinputs).trans
      ((array_select_iff_normalized (denote selector env)
        (denote onFalse env) (denote onTrue env) output).symm.trans
        (array_select_iff_evaluateNode (denote selector env)
          (denote onFalse env) (denote onTrue env) output))

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
