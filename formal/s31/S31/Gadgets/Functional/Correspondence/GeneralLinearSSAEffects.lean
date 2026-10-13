import S31.Gadgets.Functional.Correspondence.GeneralLinearSSA

/-!
A separate effectful arithmetic profile. Constants are canonical M31 values;
assertions are retained as equality constraints, including when neither side
feeds the selected output. This module models source terms and normalized
arithmetic nodes. It does not derive source terms from text or authenticate
native rows.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAEffects

open S31
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes ArithmeticOp)

inductive Term where
  | input (id : Nat)
  | binary (op : ArithmeticOp) (lhs rhs : Term)
  | constant (multiply : Bool) (lhs : Term) (value : Nat)
deriving DecidableEq, Repr

def Term.eval {n : Nat} (inputs : Nat → Lanes n) : Term → Lanes n
  | .input id => inputs id
  | .binary op lhs rhs => fun i => op.eval (lhs.eval inputs i) (rhs.eval inputs i)
  | .constant multiply lhs value =>
      if multiply then fun i => lhs.eval inputs i * RiscvRefinement.M31.reduce value
      else fun i => lhs.eval inputs i + RiscvRefinement.M31.reduce value

structure Source where
  output : Term
  assertions : List (Term × Term)
deriving DecidableEq, Repr

/-- An assertion is an effect: even an unused producer must satisfy it.
This relation is empty on inputs that violate any assertion. -/
def Source.accepts {n : Nat} (source : Source) (inputs : Nat → Lanes n)
    (claimed : Lanes n) : Prop :=
  claimed = source.output.eval inputs ∧
    ∀ pair ∈ source.assertions,
      pair.1.eval inputs = pair.2.eval inputs

/-- Assertion placement can be collected after the total, immutable SSA
arithmetic without changing source acceptance. The production parser must
still check that each assertion reads identifiers already declared at its
original source position; this certificate has no statement positions. -/
theorem assertions_permutation {n : Nat} (output : Term)
    (before after : List (Term × Term))
    (inputs : Nat → Lanes n) (claimed : Lanes n)
    (hperm : before.Perm after) :
    (Source.mk output before).accepts inputs claimed ↔
      (Source.mk output after).accepts inputs claimed := by
  constructor <;> rintro ⟨hout, hass⟩ <;> refine ⟨hout, ?_⟩
  · intro pair hmem
    exact hass pair (hperm.mem_iff.mpr hmem)
  · intro pair hmem
    exact hass pair (hperm.mem_iff.mp hmem)

/-- The equality assertion AIR polynomial for each active lane. -/
def assertionPoly {n : Nat} (left right : Lanes n) : Prop :=
  ∀ i : Fin n, left i - right i = 0

theorem assertion_poly_iff_eq {n : Nat} (left right : Lanes n) :
    assertionPoly left right ↔ left = right := by
  constructor
  · intro h
    funext i
    exact (RiscvRefinement.M31.sub_eq_zero_iff _ _).mp (h i)
  · intro h
    subst right
    intro i
    simp

inductive Step where
  | binary (id lhs rhs : Nat) (op : ArithmeticOp)
  | constant (id lhs value : Nat) (multiply : Bool)
deriving DecidableEq, Repr

def Step.id : Step → Nat
  | .binary id _ _ _ | .constant id _ _ _ => id

structure Certificate where
  inputs : Nat
  steps : List Step
  assertions : List (Nat × Nat)
  output : Nat
deriving DecidableEq, Repr

def initialTerms (count : Nat) : List Term :=
  (List.range count).map Term.input

def initialValues {n : Nat} (count : Nat) (inputs : Nat → Lanes n) :
    List (Lanes n) :=
  (List.range count).map inputs

def checkStep (terms : List Term) (step : Step) : Option (List Term) := do
  if step.id != terms.length then none else
  match step with
  | .binary _ lhs rhs op =>
      let left ← terms[lhs]?
      let right ← terms[rhs]?
      return terms ++ [.binary op left right]
  | .constant _ lhs value multiply =>
      if value ≥ S31.modulus then none else
      let left ← terms[lhs]?
      return terms ++ [.constant multiply left value]

def executeStep {n : Nat} (values : List (Lanes n))
    (step : Step) : Option (List (Lanes n)) := do
  if step.id != values.length then none else
  match step with
  | .binary _ lhs rhs op =>
      let left ← values[lhs]?
      let right ← values[rhs]?
      return values ++ [fun i => op.eval (left i) (right i)]
  | .constant _ lhs value multiply =>
      if value ≥ S31.modulus then none else
      let left ← values[lhs]?
      return values ++ [if multiply then
        (fun i => left i * RiscvRefinement.M31.reduce value)
        else (fun i => left i + RiscvRefinement.M31.reduce value)]

def resolveAssertions (values : List α)
    (assertions : List (Nat × Nat)) : Option (List (α × α)) :=
  assertions.mapM fun (lhs, rhs) => do
    let left ← values[lhs]?
    let right ← values[rhs]?
    return (left, right)

def check (certificate : Certificate) (source : Source) : Option Unit := do
  let terms ← certificate.steps.foldlM checkStep
    (initialTerms certificate.inputs)
  let output ← terms[certificate.output]?
  let assertions ← resolveAssertions terms certificate.assertions
  if (Source.mk output assertions) = source then some () else none

theorem execute_step_correct {n : Nat} (terms : List Term)
    (step : Step) (inputs : Nat → Lanes n) :
    executeStep (terms.map (Term.eval inputs)) step =
      (checkStep terms step).map
        (fun next => next.map (Term.eval inputs)) := by
  cases step with
  | binary id lhs rhs op =>
      by_cases hid : id = terms.length
      · simp only [executeStep, checkStep, Step.id,
          List.length_map, List.getElem?_map, hid]
        cases hleft : terms[lhs]? with
        | none => simp
        | some left =>
            cases hright : terms[rhs]? with
            | none => simp
            | some right => simp [List.map_append, Term.eval]
      · simp [executeStep, checkStep, Step.id, hid]
  | constant id lhs value multiply =>
      by_cases hid : id = terms.length
      · by_cases hcanonical : value < S31.modulus
        · simp only [executeStep, checkStep, Step.id,
            List.length_map, List.getElem?_map, hid]
          have hbelow : ¬ value ≥ S31.modulus := Nat.not_le_of_gt hcanonical
          simp only [hbelow, ↓reduceIte]
          cases hleft : terms[lhs]? with
          | none => simp
          | some left =>
              cases multiply <;> simp [List.map_append, Term.eval]
        · have habove : value ≥ S31.modulus := Nat.le_of_not_gt hcanonical
          simp [executeStep, checkStep, Step.id, hid, habove]
      · simp [executeStep, checkStep, Step.id, hid]

theorem execute_folds_correct {n : Nat} (steps : List Step)
    (terms : List Term) (inputs : Nat → Lanes n) :
    steps.foldlM executeStep (terms.map (Term.eval inputs)) =
      (steps.foldlM checkStep terms).map
        (fun next => next.map (Term.eval inputs)) := by
  induction steps generalizing terms with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.foldlM_cons]
      rw [execute_step_correct]
      cases hstep : checkStep terms step with
      | none => simp
      | some next => simpa [hstep] using ih next

theorem resolve_assertions_map (values : List α)
    (assertions : List (Nat × Nat)) (f : α → β) :
    resolveAssertions (values.map f) assertions =
      (resolveAssertions values assertions).map
        (List.map fun pair => (f pair.1, f pair.2)) := by
  induction assertions with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨lhs, rhs⟩ := pair
      simp only [resolveAssertions, List.mapM_cons, List.getElem?_map]
      cases hleft : values[lhs]? with
      | none => simp
      | some left =>
          cases hright : values[rhs]? with
          | none => simp
          | some right =>
              simp only [resolveAssertions, List.getElem?_map] at ih
              rw [ih]
              cases hrest : rest.mapM (fun (lhs, rhs) => do
                  let left ← values[lhs]?
                  let right ← values[rhs]?
                  pure (left, right)) with
              | none => simp
              | some pairs => simp

theorem checked_parts (certificate : Certificate) (source : Source)
    (hcheck : check certificate source = some ()) :
    ∃ terms : List Term,
      certificate.steps.foldlM checkStep
        (initialTerms certificate.inputs) = some terms ∧
      terms[certificate.output]? = some source.output ∧
      resolveAssertions terms certificate.assertions = some source.assertions := by
  unfold check at hcheck
  cases hterms : certificate.steps.foldlM checkStep
      (initialTerms certificate.inputs) with
  | none => simp [hterms] at hcheck
  | some terms =>
      cases hout : terms[certificate.output]? with
      | none => simp [hterms, hout] at hcheck
      | some output =>
          cases hass : resolveAssertions terms certificate.assertions with
          | none => simp [hterms, hout, hass] at hcheck
          | some assertions =>
              have hsource : Source.mk output assertions = source := by
                by_contra hne
                simp [hterms, hout, hass, hne] at hcheck
              cases hsource
              exact ⟨terms, rfl, hout, hass⟩

def execute {n : Nat} (certificate : Certificate)
    (inputs : Nat → Lanes n) :
    Option (Lanes n × List (Lanes n × Lanes n)) := do
  let values ← certificate.steps.foldlM executeStep
    (initialValues certificate.inputs inputs)
  let output ← values[certificate.output]?
  let assertions ← resolveAssertions values certificate.assertions
  return (output, assertions)

theorem checked_execution {n : Nat} (certificate : Certificate)
    (source : Source) (inputs : Nat → Lanes n)
    (hcheck : check certificate source = some ()) :
    execute certificate inputs = some
      (source.output.eval inputs,
        source.assertions.map fun pair =>
          (pair.1.eval inputs, pair.2.eval inputs)) := by
  obtain ⟨terms, hterms, hout, hass⟩ :=
    checked_parts certificate source hcheck
  have hinit : initialValues certificate.inputs inputs =
      (initialTerms certificate.inputs).map (Term.eval inputs) := by
    simp [initialValues, initialTerms, List.map_map,
      Function.comp_def, Term.eval]
  have hrun : certificate.steps.foldlM executeStep
      (initialValues certificate.inputs inputs) =
        some (terms.map (Term.eval inputs)) := by
    rw [hinit]
    simpa [hterms] using execute_folds_correct certificate.steps
      (initialTerms certificate.inputs) inputs
  simp [execute, hrun, List.getElem?_map, hout,
    resolve_assertions_map, hass]

/-- A const operation uses the binary packed circuit with a fixed canonical
M31 operand. Every active output lane is constrained, including a partial
final four-lane chunk. This is a modeled circuit relation, not a claim about
which native Zig gate was emitted. -/
def acceptsRow {n : Nat} (values : List (Lanes n))
    (step : Step) (output : Lanes n)
    (tailA tailB : Nat → Fin 4 → M31) : Prop :=
  match step with
  | .binary id lhs rhs op =>
      ∃ left right : Lanes n,
        id = values.length ∧
        values[lhs]? = some left ∧ values[rhs]? = some right ∧
        op.packed left right output tailA tailB
  | .constant id lhs value multiply =>
      value < S31.modulus ∧ ∃ left : Lanes n,
        id = values.length ∧ values[lhs]? = some left ∧
        (if multiply then SourceFunctionBytes.Op.mul else SourceFunctionBytes.Op.add).packed
          left (fun _ => RiscvRefinement.M31.reduce value)
          output tailA tailB

theorem accepted_row_executes {n : Nat} (values : List (Lanes n))
    (step : Step) (output : Lanes n)
    (tailA tailB : Nat → Fin 4 → M31)
    (hrow : acceptsRow values step output tailA tailB) :
    executeStep values step = some (values ++ [output]) := by
  cases step with
  | binary id lhs rhs op =>
      obtain ⟨left, right, hid, hleft, hright, hpacked⟩ := hrow
      have hvalue : output = fun i => op.eval (left i) (right i) := by
        funext i
        exact (SourceFunctionBytes.packed_iff_eval op left right
          output tailA tailB).mp hpacked i
      simp [executeStep, Step.id, hid, hleft, hright, hvalue]
  | constant id lhs value multiply =>
      obtain ⟨hcanonical, left, hid, hleft, hpacked⟩ := hrow
      have habove : ¬ value ≥ S31.modulus := Nat.not_le_of_gt hcanonical
      cases multiply with
      | false =>
          have hvalue : output = fun i => left i +
              RiscvRefinement.M31.reduce value := by
            funext i
            exact (SourceFunctionBytes.packed_iff_eval SourceFunctionBytes.Op.add
              left (fun _ => RiscvRefinement.M31.reduce value)
              output tailA tailB).mp hpacked i
          simp [executeStep, Step.id, hid, habove, hleft, hvalue]
      | true =>
          have hvalue : output = fun i => left i *
              RiscvRefinement.M31.reduce value := by
            funext i
            exact (SourceFunctionBytes.packed_iff_eval SourceFunctionBytes.Op.mul
              left (fun _ => RiscvRefinement.M31.reduce value)
              output tailA tailB).mp hpacked i
          simp [executeStep, Step.id, hid, habove, hleft, hvalue]

inductive AcceptsTrace {n : Nat} :
    List (Lanes n) → List Step → List (Lanes n) → Prop where
  | done (values : List (Lanes n)) : AcceptsTrace values [] values
  | next {values final : List (Lanes n)}
      {step : Step} {rest : List Step}
      (output : Lanes n) (tailA tailB : Nat → Fin 4 → M31)
      (hrow : acceptsRow values step output tailA tailB)
      (hrest : AcceptsTrace (values ++ [output]) rest final) :
      AcceptsTrace values (step :: rest) final

theorem accepted_trace_executes {n : Nat}
    {initial final : List (Lanes n)} {steps : List Step}
    (hrows : AcceptsTrace initial steps final) :
    steps.foldlM executeStep initial = some final := by
  induction hrows with
  | done => rfl
  | next output tailA tailB hrow _ ih =>
      simp [List.foldlM_cons,
        accepted_row_executes _ _ output tailA tailB hrow, ih]

def constantNode (multiply : Bool) (value : Nat) : S31.Node :=
  { name := "out", op := if multiply then .mul_const else .add_const,
    lhs := some "left", constant := some value }

def constantEnv {n : Nat} (left : Lanes n) : S31.Env :=
  [("left", ⟨.m31, List.ofFn left⟩)]

theorem constant_node_shape {n : Nat} (multiply : Bool)
    (value : Nat) (left : Lanes n) (hcanonical : value < S31.modulus) :
    S31.inferNode ((constantEnv left).map
      (fun (name, result) => (name, result.shape)))
      (constantNode multiply value) = .ok ⟨.m31, n⟩ := by
  have hkind : (S31.Kind.m31 == S31.Kind.m31) = true := rfl
  cases multiply <;>
    simp [constantNode, constantEnv, S31.inferNode,
      S31.Node.metadataValid, S31.Node.fields,
      S31.shapeOperand, S31.expectShape, S31.lookup,
      S31.Value.shape, S31.need, S31.require,
      hkind, hcanonical, Bind.bind, Except.bind, Except.map]
  all_goals rfl

theorem constant_node_eval {n : Nat} (multiply : Bool)
    (value : Nat) (left : Lanes n) (hcanonical : value < S31.modulus) :
    S31.evaluateNode (constantEnv left) (constantNode multiply value) =
      .ok ⟨.m31, List.ofFn (fun i =>
        if multiply then left i * RiscvRefinement.M31.reduce value
        else left i + RiscvRefinement.M31.reduce value)⟩ := by
  unfold S31.evaluateNode
  rw [constant_node_shape multiply value left hcanonical]
  have hshape : ((⟨.m31, n⟩ : S31.Shape) == ⟨.m31, n⟩) = true := by
    change ((S31.Kind.m31 == S31.Kind.m31) && (n == n)) = true
    simp [show (S31.Kind.m31 == S31.Kind.m31) = true by rfl]
  cases multiply with
  | false =>
      simp [constantNode, constantEnv, S31.valueOperand,
        S31.lookup, S31.require, S31.Value.shape, S31.Value.valid,
        Bind.bind, Except.bind, List.map_ofFn, Function.comp_def]
      have hpure : (pure (List.ofFn (fun i : Fin n =>
          left i + RiscvRefinement.M31.reduce value)) :
          S31.Result (List M31)) = .ok (List.ofFn (fun i =>
          left i + RiscvRefinement.M31.reduce value)) := rfl
      rw [hpure]
      simp [hshape]
      rfl
  | true =>
      simp [constantNode, constantEnv, S31.valueOperand,
        S31.lookup, S31.require, S31.Value.shape, S31.Value.valid,
        Bind.bind, Except.bind, List.map_ofFn, Function.comp_def]
      have hpure : (pure (List.ofFn (fun i : Fin n =>
          left i * RiscvRefinement.M31.reduce value)) :
          S31.Result (List M31)) = .ok (List.ofFn (fun i =>
          left i * RiscvRefinement.M31.reduce value)) := rfl
      rw [hpure]
      simp [hshape]
      rfl

theorem constant_packed_iff_node {n : Nat} (multiply : Bool)
    (value : Nat) (left output : Lanes n)
    (tailA tailB : Nat → Fin 4 → M31)
    (hcanonical : value < S31.modulus) :
    (if multiply then SourceFunctionBytes.Op.mul else SourceFunctionBytes.Op.add).packed
        left (fun _ => RiscvRefinement.M31.reduce value) output tailA tailB ↔
      S31.evaluateNode (constantEnv left) (constantNode multiply value) =
        .ok ⟨.m31, List.ofFn output⟩ := by
  rw [constant_node_eval multiply value left hcanonical]
  cases multiply with
  | false =>
      rw [SourceFunctionBytes.packed_iff_eval]
      constructor
      · intro h
        have heq : (fun i : Fin n => left i + RiscvRefinement.M31.reduce value) =
            output := by funext i; exact (h i).symm
        simp [heq]
      · intro h
        have heq : (fun i : Fin n => left i + RiscvRefinement.M31.reduce value) =
            output := List.ofFn_injective (by simpa using congrArg S31.Value.words (Except.ok.inj h))
        intro i
        exact (congrFun heq i).symm
  | true =>
      rw [SourceFunctionBytes.packed_iff_eval]
      constructor
      · intro h
        have heq : (fun i : Fin n => left i * RiscvRefinement.M31.reduce value) =
            output := by funext i; exact (h i).symm
        simp [heq]
      · intro h
        have heq : (fun i : Fin n => left i * RiscvRefinement.M31.reduce value) =
            output := List.ofFn_injective (by simpa using congrArg S31.Value.words (Except.ok.inj h))
        intro i
        exact (congrFun heq i).symm

/-- Every graph edge runs the production normalized arithmetic evaluator.
Constant nodes use the exact canonical operand, and all prior reads resolve. -/
def acceptsNode {n : Nat} (values : List (Lanes n))
    (step : Step) (output : Lanes n) : Prop :=
  match step with
  | .binary id lhs rhs op =>
      ∃ left right : Lanes n,
        id = values.length ∧
        values[lhs]? = some left ∧ values[rhs]? = some right ∧
        S31.evaluateNode (S31.Functional.arithmeticEnv left right) op.node =
          .ok ⟨.m31, List.ofFn output⟩
  | .constant id lhs value multiply =>
      value < S31.modulus ∧ ∃ left : Lanes n,
        id = values.length ∧ values[lhs]? = some left ∧
        S31.evaluateNode (constantEnv left) (constantNode multiply value) =
          .ok ⟨.m31, List.ofFn output⟩

theorem row_iff_node {n : Nat} (values : List (Lanes n))
    (step : Step) (output : Lanes n)
    (tailA tailB : Nat → Fin 4 → M31) :
    acceptsRow values step output tailA tailB ↔
      acceptsNode values step output := by
  cases step with
  | binary id lhs rhs op =>
      constructor
      · rintro ⟨left, right, hid, hlhs, hrhs, hrow⟩
        exact ⟨left, right, hid, hlhs, hrhs,
          (SourceFunctionBytes.packed_iff_node op left right output
            tailA tailB).mp hrow⟩
      · rintro ⟨left, right, hid, hlhs, hrhs, hnode⟩
        exact ⟨left, right, hid, hlhs, hrhs,
          (SourceFunctionBytes.packed_iff_node op left right output
            tailA tailB).mpr hnode⟩
  | constant id lhs value multiply =>
      constructor
      · rintro ⟨hcanonical, left, hid, hlhs, hrow⟩
        exact ⟨hcanonical, left, hid, hlhs,
          (constant_packed_iff_node multiply value left output
            tailA tailB hcanonical).mp hrow⟩
      · rintro ⟨hcanonical, left, hid, hlhs, hnode⟩
        exact ⟨hcanonical, left, hid, hlhs,
          (constant_packed_iff_node multiply value left output
            tailA tailB hcanonical).mpr hnode⟩

inductive AcceptsNormalizedTrace {n : Nat} :
    List (Lanes n) → List Step → List (Lanes n) → Prop where
  | done (values : List (Lanes n)) :
      AcceptsNormalizedTrace values [] values
  | next {values final : List (Lanes n)}
      {step : Step} {rest : List Step}
      (output : Lanes n)
      (hnode : acceptsNode values step output)
      (hrest : AcceptsNormalizedTrace (values ++ [output]) rest final) :
      AcceptsNormalizedTrace values (step :: rest) final

/-- Full graph equivalence, including unused producers. Assertions remain
separate polynomial obligations and are not erased by this equivalence. -/
theorem air_iff_normalized_trace {n : Nat}
    (initial final : List (Lanes n)) (steps : List Step) :
    AcceptsTrace initial steps final ↔
      AcceptsNormalizedTrace initial steps final := by
  constructor
  · intro h
    induction h with
    | done => exact .done _
    | next output tailA tailB hrow _ ih =>
        exact .next output
          ((row_iff_node _ _ output tailA tailB).mp hrow) ih
  · intro h
    induction h with
    | done => exact .done _
    | next output hnode _ ih =>
        exact .next output (fun _ _ => 0) (fun _ _ => 0)
          ((row_iff_node _ _ output (fun _ _ => 0)
            (fun _ _ => 0)).mpr hnode) ih

theorem honest_row_accepted {n : Nat} (values : List (Lanes n))
    (step : Step) (output : Lanes n)
    (hstep : executeStep values step = some (values ++ [output])) :
    acceptsRow values step output (fun _ _ => 0) (fun _ _ => 0) := by
  cases step with
  | binary id lhs rhs op =>
      by_cases hid : id = values.length
      · cases hleft : values[lhs]? with
        | none => simp [executeStep, hid, hleft] at hstep
        | some left =>
            cases hright : values[rhs]? with
            | none => simp [executeStep, hid, hleft, hright] at hstep
            | some right =>
                have heq : (fun i => op.eval (left i) (right i)) = output := by
                  have h := hstep
                  simp [executeStep, hid, hleft, hright] at h
                  exact h.2
                exact ⟨left, right, hid, hleft, hright,
                  (SourceFunctionBytes.packed_iff_eval op left right output
                    (fun _ _ => 0) (fun _ _ => 0)).mpr
                    (fun i => (congrFun heq i).symm)⟩
      · have h := hstep
        simp [executeStep] at h
        exact False.elim (hid h.1)
  | constant id lhs value multiply =>
      by_cases hid : id = values.length
      · by_cases hcanonical : value < S31.modulus
        · have habove : ¬ value ≥ S31.modulus := Nat.not_le_of_gt hcanonical
          cases hleft : values[lhs]? with
          | none => simp [executeStep, hid, habove, hleft] at hstep
          | some left =>
              have heq : (if multiply then
                    (fun i => left i * RiscvRefinement.M31.reduce value)
                    else (fun i => left i + RiscvRefinement.M31.reduce value)) =
                    output := by
                have h := hstep
                simp [executeStep, hid, habove, hleft] at h
                exact h.2
              refine ⟨hcanonical, left, hid, hleft, ?_⟩
              cases multiply with
              | false =>
                  apply (SourceFunctionBytes.packed_iff_eval
                    SourceFunctionBytes.Op.add left
                    (fun _ => RiscvRefinement.M31.reduce value)
                    output (fun _ _ => 0) (fun _ _ => 0)).mpr
                  intro i
                  exact (congrFun heq i).symm
              | true =>
                  apply (SourceFunctionBytes.packed_iff_eval
                    SourceFunctionBytes.Op.mul left
                    (fun _ => RiscvRefinement.M31.reduce value)
                    output (fun _ _ => 0) (fun _ _ => 0)).mpr
                  intro i
                  exact (congrFun heq i).symm
        · have habove : value ≥ S31.modulus := Nat.le_of_not_gt hcanonical
          simp [executeStep, hid, habove] at hstep
      · have h := hstep
        simp [executeStep] at h
        exact False.elim (hid h.1)

theorem executing_trace_has_air_rows {n : Nat}
    (steps : List Step) (initial final : List (Lanes n))
    (h : steps.foldlM executeStep initial = some final) :
    AcceptsTrace initial steps final := by
  induction steps generalizing initial with
  | nil =>
      simp only [List.foldlM_nil] at h
      cases h
      exact .done _
  | cons step rest ih =>
      simp only [List.foldlM_cons] at h
      cases step with
      | binary id lhs rhs op =>
          by_cases hid : id = initial.length
          · cases hleft : initial[lhs]? with
            | none => simp [executeStep, Step.id, hid, hleft] at h
            | some left =>
                cases hright : initial[rhs]? with
                | none => simp [executeStep, Step.id, hid, hleft, hright] at h
                | some right =>
                    let output : Lanes n :=
                      fun i => op.eval (left i) (right i)
                    have hstep : executeStep initial (.binary id lhs rhs op) =
                        some (initial ++ [output]) := by
                      simp [executeStep, Step.id, hid, hleft, hright, output]
                    rw [hstep] at h
                    exact .next output (fun _ _ => 0) (fun _ _ => 0)
                      (honest_row_accepted initial _ output hstep)
                      (ih (initial ++ [output]) h)
          · simp [executeStep, Step.id, hid] at h
      | constant id lhs value multiply =>
          by_cases hid : id = initial.length
          · by_cases hcanonical : value < S31.modulus
            · have habove : ¬ value ≥ S31.modulus := Nat.not_le_of_gt hcanonical
              cases hleft : initial[lhs]? with
              | none => simp [executeStep, Step.id, hid, habove, hleft] at h
              | some left =>
                  let output : Lanes n :=
                    if multiply then
                      (fun i => left i * RiscvRefinement.M31.reduce value)
                    else (fun i => left i + RiscvRefinement.M31.reduce value)
                  have hstep : executeStep initial (.constant id lhs value multiply) =
                      some (initial ++ [output]) := by
                    simp [executeStep, Step.id, hid, habove, hleft, output]
                  rw [hstep] at h
                  exact .next output (fun _ _ => 0) (fun _ _ => 0)
                    (honest_row_accepted initial _ output hstep)
                    (ih (initial ++ [output]) h)
            · have habove : value ≥ S31.modulus := Nat.le_of_not_gt hcanonical
              simp [executeStep, Step.id, hid, habove] at h
          · simp [executeStep, Step.id, hid] at h

def assertionsAir {n : Nat} (values : List (Lanes n))
    (assertions : List (Nat × Nat)) : Prop :=
  ∃ pairs, resolveAssertions values assertions = some pairs ∧
    ∀ pair ∈ pairs, assertionPoly pair.1 pair.2

/-- Arbitrary accepted arithmetic witnesses and assertion polynomials imply
the source's partial meaning. The assertion effect remains live even when
its operands are not ancestors of the selected output. -/
theorem checked_air_sound {n : Nat} (certificate : Certificate)
    (source : Source) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (hcheck : check certificate source = some ())
    (hrows : AcceptsTrace
      (initialValues certificate.inputs inputs) certificate.steps final)
    (houtput : final[certificate.output]? = some claimed)
    (hassert : assertionsAir final certificate.assertions) :
    source.accepts inputs claimed := by
  have hrun := accepted_trace_executes hrows
  have hsem := checked_execution certificate source inputs hcheck
  obtain ⟨pairs, hresolve, hpoly⟩ := hassert
  have hpair : (claimed, pairs) =
      (source.output.eval inputs,
        source.assertions.map fun pair =>
          (pair.1.eval inputs, pair.2.eval inputs)) :=
    Option.some.inj (by simpa [execute, hrun, houtput, hresolve] using hsem)
  have hclaimed := congrArg Prod.fst hpair
  have hpairs : pairs = source.assertions.map (fun pair =>
      (pair.1.eval inputs, pair.2.eval inputs)) := by
    simpa using congrArg Prod.snd hpair
  refine ⟨hclaimed, ?_⟩
  intro pair hmem
  have hmapped : (pair.1.eval inputs, pair.2.eval inputs) ∈ pairs := by
    rw [hpairs]
    exact List.mem_map.mpr ⟨pair, hmem, rfl⟩
  exact (assertion_poly_iff_eq _ _).mp
    (hpoly _ hmapped)

theorem checked_normalized_sound {n : Nat} (certificate : Certificate)
    (source : Source) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (hcheck : check certificate source = some ())
    (hnodes : AcceptsNormalizedTrace
      (initialValues certificate.inputs inputs) certificate.steps final)
    (houtput : final[certificate.output]? = some claimed)
    (hassert : assertionsAir final certificate.assertions) :
    source.accepts inputs claimed :=
  checked_air_sound certificate source inputs claimed final hcheck
    ((air_iff_normalized_trace _ _ _).mpr hnodes) houtput hassert

/-- Completeness is deliberately conditional on the source's assertions.
Inputs that violate an assertion have no accepted witness. -/
theorem checked_air_complete {n : Nat} (certificate : Certificate)
    (source : Source) (inputs : Nat → Lanes n)
    (hcheck : check certificate source = some ())
    (haccept : source.accepts inputs (source.output.eval inputs)) :
    ∃ final : List (Lanes n),
      AcceptsTrace (initialValues certificate.inputs inputs)
        certificate.steps final ∧
      final[certificate.output]? = some (source.output.eval inputs) ∧
      assertionsAir final certificate.assertions := by
  have hsem := checked_execution certificate source inputs hcheck
  unfold execute at hsem
  cases hrun : certificate.steps.foldlM executeStep
      (initialValues certificate.inputs inputs) with
  | none => simp [hrun] at hsem
  | some final =>
      cases hout : final[certificate.output]? with
      | none => simp [hrun, hout] at hsem
      | some output =>
          cases hass : resolveAssertions final certificate.assertions with
          | none => simp [hrun, hout, hass] at hsem
          | some pairs =>
              have hpair : (output, pairs) =
                  (source.output.eval inputs,
                    source.assertions.map fun pair =>
                      (pair.1.eval inputs, pair.2.eval inputs)) :=
                Option.some.inj (by simpa [hrun, hout, hass] using hsem)
              have houtput : output = source.output.eval inputs :=
                congrArg Prod.fst hpair
              have hpairs : pairs = source.assertions.map (fun pair =>
                  (pair.1.eval inputs, pair.2.eval inputs)) := by
                simpa using congrArg Prod.snd hpair
              refine ⟨final,
                executing_trace_has_air_rows _ _ _ hrun,
                houtput ▸ hout, ⟨pairs, hass, ?_⟩⟩
              intro pair hmem
              rw [hpairs] at hmem
              obtain ⟨sourcePair, hsourcePair, rfl⟩ :=
                List.mem_map.mp hmem
              exact (assertion_poly_iff_eq _ _).mpr
                (haccept.2 sourcePair hsourcePair)

theorem checked_normalized_complete {n : Nat} (certificate : Certificate)
    (source : Source) (inputs : Nat → Lanes n)
    (hcheck : check certificate source = some ())
    (haccept : source.accepts inputs (source.output.eval inputs)) :
    ∃ final : List (Lanes n),
      AcceptsNormalizedTrace (initialValues certificate.inputs inputs)
        certificate.steps final ∧
      final[certificate.output]? = some (source.output.eval inputs) ∧
      assertionsAir final certificate.assertions := by
  obtain ⟨final, hrows, houtput, hassert⟩ :=
    checked_air_complete certificate source inputs hcheck haccept
  exact ⟨final, (air_iff_normalized_trace _ _ _).mp hrows,
    houtput, hassert⟩

/-- Exact fields in the production indexed effects roster. The two optional
operands preserve the JSON distinction between binary and constant nodes. -/
structure EmittedNode where
  id : Nat
  name : String
  op : String
  lhs : Nat
  rhs : Option Nat
  constant : Option Nat
deriving DecidableEq, Repr

structure EmittedSSA where
  lane_count : Nat
  inputs : List GeneralLinearSSA.EmittedInput
  nodes : List EmittedNode
  assertions : List (Nat × Nat)
  output : Nat
deriving DecidableEq, Repr

def EmittedNode.decode (node : EmittedNode) : Option Step := do
  match node.op with
  | "add" | "sub" | "mul" =>
      if node.constant.isSome then none else
      let rhs ← node.rhs
      let op ← GeneralLinearSSA.decodeOp node.op
      return .binary node.id node.lhs rhs op
  | "add_const" | "mul_const" =>
      if node.rhs.isSome then none else
      let value ← node.constant
      if value ≥ S31.modulus then none else
      return .constant node.id node.lhs value (node.op == "mul_const")
  | _ => none

def EmittedSSA.names (ssa : EmittedSSA) : List String :=
  ssa.inputs.map GeneralLinearSSA.EmittedInput.name ++
    ssa.nodes.map EmittedNode.name

def EmittedSSA.decode (ssa : EmittedSSA) : Option Certificate := do
  if ssa.lane_count = 0 then none else
  if ssa.inputs.map GeneralLinearSSA.EmittedInput.id !=
      List.range ssa.inputs.length then none else
  if !ssa.names.Nodup || ssa.names.contains "" then none else
  if !ssa.inputs.all (fun input =>
      input.visibility == "private" || input.visibility == "public") then none else
  let steps ← ssa.nodes.mapM EmittedNode.decode
  let result : Certificate :=
    { inputs := ssa.inputs.length, steps,
      assertions := ssa.assertions, output := ssa.output }
  -- All assertion IDs must resolve, including assertions on unused nodes.
  let terms ← result.steps.foldlM checkStep (initialTerms result.inputs)
  let _ ← resolveAssertions terms result.assertions
  return result

def checkEmittedSSA (ssa : EmittedSSA) (source : Source) :
    Option Certificate := do
  let certificate ← ssa.decode
  check certificate source
  return certificate

theorem checked_emitted_certificate (ssa : EmittedSSA) (source : Source)
    (certificate : Certificate)
    (hcheck : checkEmittedSSA ssa source = some certificate) :
    ssa.decode = some certificate ∧
    check certificate source = some () := by
  unfold checkEmittedSSA at hcheck
  cases hdecode : ssa.decode with
  | none => simp [hdecode] at hcheck
  | some decoded =>
      cases hsource : check decoded source with
      | none => simp [hdecode, hsource] at hcheck
      | some value =>
          cases value
          have heq : decoded = certificate := by
            simpa [hdecode, hsource] using hcheck
          subst certificate
          exact ⟨rfl, hsource⟩

theorem emitted_ssa_air_sound (ssa : EmittedSSA) (source : Source)
    (certificate : Certificate)
    (inputs : Nat → Lanes ssa.lane_count)
    (claimed : Lanes ssa.lane_count)
    (final : List (Lanes ssa.lane_count))
    (hcheck : checkEmittedSSA ssa source = some certificate)
    (hrows : AcceptsTrace
      (initialValues certificate.inputs inputs) certificate.steps final)
    (houtput : final[certificate.output]? = some claimed)
    (hassert : assertionsAir final certificate.assertions) :
    source.accepts inputs claimed :=
  checked_air_sound certificate source inputs claimed final
    (checked_emitted_certificate ssa source certificate hcheck).2
    hrows houtput hassert

end S31.Functional.Correspondence.GeneralLinearSSAEffects
