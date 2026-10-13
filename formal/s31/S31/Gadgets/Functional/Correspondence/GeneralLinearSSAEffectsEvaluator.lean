import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffects
import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAProgramEvaluate

/-!
Named-environment evaluator bridge for the effectful SSA fragment's canonical
M31 constant operations. This local theorem is parametric in the environment;
the existing single-entry fixture alone does not establish name preservation
inside a whole program. Assertion and whole-program joins remain separate.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAEffectsEvaluator

open S31
open S31.Functional.Correspondence.GeneralLinearSSAProgramEvaluate

def namedConstantNode (name lhs : String) (multiply : Bool)
    (value : Nat) : S31.Node :=
  { name, op := if multiply then .mul_const else .add_const,
    lhs := some lhs, constant := some value }

private theorem lookup_shapes (env : S31.Env) (name : String) :
    S31.lookup (env.map (fun (key, value) => (key, value.shape))) name =
      (S31.lookup env name).map S31.Value.shape := by
  simp [S31.lookup, List.find?_map, Function.comp_def]

/-- Every canonical constant step evaluates identically in any named
environment that carries its operand. This is the constant case needed by
an effectful named SSA induction. -/
theorem named_constant_node_eval {n : Nat} (env : S31.Env)
    (name lhs : String) (multiply : Bool) (value : Nat)
    (left : Lanes n) (hcanonical : value < S31.modulus)
    (hlhs : S31.lookup env lhs =
      some ⟨.m31, List.ofFn left⟩) :
    S31.evaluateNode env (namedConstantNode name lhs multiply value) =
      .ok ⟨.m31, List.ofFn (fun i =>
        if multiply then left i * RiscvRefinement.M31.reduce value
        else left i + RiscvRefinement.M31.reduce value)⟩ := by
  have hshapeL :
      S31.lookup (env.map (fun (key, result) => (key, result.shape))) lhs =
        some ⟨.m31, n⟩ := by
    rw [lookup_shapes, hlhs]
    simp [S31.Value.shape]
  have hinfer :
      S31.inferNode (env.map (fun (key, result) => (key, result.shape)))
        (namedConstantNode name lhs multiply value) = .ok ⟨.m31, n⟩ := by
    have hkind : (S31.Kind.m31 == S31.Kind.m31) = true := rfl
    cases multiply <;>
      simp [namedConstantNode, S31.inferNode,
        S31.Node.metadataValid, S31.Node.fields,
        S31.shapeOperand, S31.expectShape, S31.need, S31.require,
        hshapeL, hkind, hcanonical, Bind.bind, Except.bind, Except.map,
        Pure.pure, Except.pure]
  unfold S31.evaluateNode
  rw [hinfer]
  have hshape : ((⟨.m31, n⟩ : S31.Shape) == ⟨.m31, n⟩) = true := by
    change ((S31.Kind.m31 == S31.Kind.m31) && (n == n)) = true
    simp [show (S31.Kind.m31 == S31.Kind.m31) = true by rfl]
  cases multiply <;>
    simp [namedConstantNode, S31.valueOperand, hlhs, S31.require,
      S31.Value.shape, S31.Value.valid, List.map_ofFn, Function.comp_def,
      Bind.bind, Except.bind, Pure.pure, Except.pure, hshape]

def namedEffectNode (names : List String) :
    GeneralLinearSSAEffects.Step → S31.Node
  | .binary id lhs rhs op =>
      namedBinaryNode (nameAt names id) (nameAt names lhs)
        (nameAt names rhs) op
  | .constant id lhs value multiply =>
      namedConstantNode (nameAt names id) (nameAt names lhs)
        multiply value

/-- Every accepted effectful arithmetic row, whether binary or constant,
executes as the same value in the actual named normalized evaluator.
Only prior value lookup alignment is assumed; no final-output comparison is
used. This is a local step theorem, not whole-program correspondence. -/
theorem named_effect_node_of_air {n : Nat}
    (names : List String) (env : S31.Env)
    (values : List (Lanes n))
    (step : GeneralLinearSSAEffects.Step) (output : Lanes n)
    (tailA tailB : Nat → Fin 4 → S31.M31)
    (hrow : GeneralLinearSSAEffects.acceptsRow
      values step output tailA tailB)
    (hcarries : Carries names env values) :
    S31.evaluateNode env (namedEffectNode names step) =
      .ok (laneValue output) := by
  cases step with
  | binary id lhs rhs op =>
      obtain ⟨left, right, _, hleft, hright, hpacked⟩ := hrow
      have hvalue : output =
          (fun i => op.eval (left i) (right i)) := by
        funext i
        exact (SourceFunctionBytes.packed_iff_eval op left right
          output tailA tailB).mp hpacked i
      change S31.evaluateNode env
        (namedBinaryNode (nameAt names id) (nameAt names lhs)
          (nameAt names rhs) op) = .ok (laneValue output)
      rw [hvalue]
      exact named_binary_node_eval env _ _ _ op left right
        (hcarries lhs left hleft) (hcarries rhs right hright)
  | constant id lhs value multiply =>
      obtain ⟨hcanonical, left, _, hleft, hpacked⟩ := hrow
      have hvalue : output =
          (fun i => if multiply then
            left i * RiscvRefinement.M31.reduce value
          else left i + RiscvRefinement.M31.reduce value) := by
        cases multiply with
        | false =>
            funext i
            exact (SourceFunctionBytes.packed_iff_eval
              SourceFunctionBytes.Op.add left
              (fun _ => RiscvRefinement.M31.reduce value)
              output tailA tailB).mp hpacked i
        | true =>
            funext i
            exact (SourceFunctionBytes.packed_iff_eval
              SourceFunctionBytes.Op.mul left
              (fun _ => RiscvRefinement.M31.reduce value)
              output tailA tailB).mp hpacked i
      change S31.evaluateNode env
        (namedConstantNode (nameAt names id) (nameAt names lhs)
          multiply value) = .ok (laneValue output)
      rw [hvalue]
      exact named_constant_node_eval env _ _ multiply value left
        hcanonical (hcarries lhs left hleft)

/-- The body of the normalized interpreter's assertion loop, isolated for
one pair of named values. -/
def checkNamedAssertion (env : S31.Env) (lhs rhs : String) :
    S31.Result Unit := do
  let left ← S31.need (S31.lookup env lhs) .unknownOperand
  let right ← S31.need (S31.lookup env rhs) .unknownOperand
  S31.require (left == right) .assertionFailed

/-- The modeled zero polynomial is equivalent to acceptance by the actual
normalized assertion check, once its named operands are aligned. -/
theorem named_assertion_iff_air {n : Nat} (env : S31.Env)
    (lhs rhs : String) (left right : Lanes n)
    (hlhs : S31.lookup env lhs = some (laneValue left))
    (hrhs : S31.lookup env rhs = some (laneValue right)) :
    checkNamedAssertion env lhs rhs = .ok () ↔
      GeneralLinearSSAEffects.assertionPoly left right := by
  rw [GeneralLinearSSAEffects.assertion_poly_iff_eq]
  simp [checkNamedAssertion, hlhs, hrhs, S31.need, S31.require,
    Bind.bind, Except.bind, laneValue, S31.instBEqValue.beq,
    S31.instBEqKind.beq, BEq.beq]
  change (List.ofFn left == List.ofFn right) = true ↔ left = right
  rw [beq_iff_eq]
  exact ⟨fun h => List.ofFn_injective h, congrArg List.ofFn⟩

def namedEffectStep (names : List String) (env : S31.Env)
    (step : GeneralLinearSSAEffects.Step) : S31.Result S31.Env := do
  let node := namedEffectNode names step
  return env ++ [(node.name, ← S31.evaluateNode env node)]

theorem named_effect_step_of_air {n maximum : Nat}
    (names : List String) (env : S31.Env)
    (values : List (Lanes n))
    (step : GeneralLinearSSAEffects.Step) (output : Lanes n)
    (tailA tailB : Nat → Fin 4 → S31.M31)
    (hrow : GeneralLinearSSAEffects.acceptsRow
      values step output tailA tailB)
    (hcarries : Carries names env values)
    (habent : Absent names env values.length maximum)
    (hdistinct : Distinct names maximum)
    (hbudget : values.length < maximum) :
    ∃ nextEnv,
      namedEffectStep names env step = .ok nextEnv ∧
      Carries names nextEnv (values ++ [output]) ∧
      Absent names nextEnv (values.length + 1) maximum := by
  have hid : step.id = values.length := by
    cases step with
    | binary id lhs rhs op =>
        obtain ⟨_, _, h, _, _, _⟩ := hrow
        exact h
    | constant id lhs value multiply =>
        obtain ⟨_, _, h, _, _⟩ := hrow
        exact h
  have heval := named_effect_node_of_air names env values step output
    tailA tailB hrow hcarries
  let nextEnv := env ++ [(nameAt names step.id, laneValue output)]
  have hstep : namedEffectStep names env step = .ok nextEnv := by
    have hname : (namedEffectNode names step).name =
        nameAt names step.id := by cases step <;> rfl
    simp [namedEffectStep, heval, hname, nextEnv]
  refine ⟨nextEnv, hstep, ?_, ?_⟩
  · intro id value hfound
    by_cases hold : id < values.length
    · have hprior : values[id]? = some value := by
        rw [List.getElem?_append_left hold] at hfound
        exact hfound
      exact lookup_append_some env _ (nameAt names id)
        (laneValue value) (hcarries id value hprior)
    · have hindex : id = values.length := by
        have hlt : id < (values ++ [output]).length :=
          (List.getElem?_eq_some_iff.mp hfound).1
        simp at hlt
        omega
      subst id
      have hsame : value = output := by
        simpa using hfound.symm
      subst value
      have hfresh : S31.lookup env (nameAt names step.id) = none := by
        rw [hid]
        exact habent values.length (by omega) hbudget
      simpa [nextEnv, hid] using lookup_append_fresh env
        (nameAt names step.id) (laneValue output) hfresh
  · intro id hnext hmax
    have hnone : S31.lookup env (nameAt names id) = none :=
      habent id (by omega) hmax
    have hne : nameAt names id ≠ nameAt names step.id := by
      intro heq
      have hsame := hdistinct id step.id hmax
        (by rw [hid]; exact hbudget) heq
      omega
    exact lookup_append_other env (nameAt names id)
      (nameAt names step.id) (laneValue output) hnone hne

/-- A complete effectful arithmetic AIR trace executes identically through
the actual named normalized node fold. Assertions are checked separately by
`named_assertion_iff_air`. -/
theorem named_effect_fold_of_air {n maximum : Nat}
    (names : List String)
    {values final : List (Lanes n)}
    {steps : List GeneralLinearSSAEffects.Step}
    (env : S31.Env)
    (hrows : GeneralLinearSSAEffects.AcceptsTrace values steps final)
    (hbudget : values.length + steps.length = maximum)
    (hdistinct : Distinct names maximum)
    (hcarries : Carries names env values)
    (habent : Absent names env values.length maximum) :
    ∃ finalEnv,
      steps.foldlM (namedEffectStep names) env = .ok finalEnv ∧
      Carries names finalEnv final ∧
      Absent names finalEnv final.length maximum := by
  induction hrows generalizing env with
  | done values =>
      exact ⟨env, rfl, hcarries, habent⟩
  | @next values final step rest output tailA tailB hrow hrest ih =>
      have hlt : values.length < maximum := by
        simp at hbudget
        omega
      obtain ⟨nextEnv, hstep, hcarryNext, habsentNext⟩ :=
        named_effect_step_of_air names env values step output tailA tailB
          hrow hcarries habent hdistinct hlt
      have hbudgetNext :
          (values ++ [output]).length + rest.length = maximum := by
        simp at hbudget ⊢
        omega
      obtain ⟨finalEnv, hfold, hcarryFinal, habsentFinal⟩ :=
        ih nextEnv hbudgetNext hcarryNext (by simpa using habsentNext)
      refine ⟨finalEnv, ?_, hcarryFinal, habsentFinal⟩
      simpa [List.foldlM_cons, hstep] using hfold

/-- Ordered assertion effects, with exactly the same per-assertion check as
the normalized `Program.environment` loop. -/
def checkNamedAssertions (env : S31.Env) :
    List (String × String) → S31.Result Unit
  | [] => .ok ()
  | (lhs, rhs) :: rest => do
      checkNamedAssertion env lhs rhs
      checkNamedAssertions env rest

/-- This recursive checker is definitionally the assertion loop used by
`Program.environment`, written here as a reusable theorem boundary. -/
theorem normalized_assertion_loop_eq (env : S31.Env)
    (assertions : List (String × String)) :
    (do
      for (lhs, rhs) in assertions do
        let left ← S31.need (S31.lookup env lhs) .unknownOperand
        let right ← S31.need (S31.lookup env rhs) .unknownOperand
        S31.require (left == right) .assertionFailed
      pure ()) = checkNamedAssertions env assertions := by
  induction assertions with
  | nil => rfl
  | cons pair rest ih =>
      obtain ⟨lhs, rhs⟩ := pair
      cases hleft : S31.need (S31.lookup env lhs) .unknownOperand with
      | error err =>
          simp [checkNamedAssertions, checkNamedAssertion, hleft,
            Bind.bind, Except.bind]
      | ok left =>
          cases hright : S31.need (S31.lookup env rhs) .unknownOperand with
          | error err =>
              simp [checkNamedAssertions, checkNamedAssertion,
                hleft, hright, Bind.bind, Except.bind]
          | ok right =>
              cases hcheck : S31.require (left == right) .assertionFailed with
              | error err =>
                  simp [checkNamedAssertions, checkNamedAssertion,
                    hleft, hright, hcheck, Bind.bind, Except.bind]
              | ok _ =>
                  simp [checkNamedAssertions, checkNamedAssertion,
                    hleft, hright, hcheck, Bind.bind, Except.bind,
                    Pure.pure, Except.pure]
                  exact ih

def namedAssertions (names : List String) :
    List (Nat × Nat) → List (String × String) :=
  List.map fun (lhs, rhs) => (nameAt names lhs, nameAt names rhs)

/-- Every modeled assertion polynomial is enforced by the corresponding
named normalized assertion sequence, including assertions on dead producers.
`Carries` is the explicit indexed-to-named environment invariant. -/
theorem named_assertions_of_air {n : Nat}
    (names : List String) (env : S31.Env)
    (final : List (Lanes n)) (assertions : List (Nat × Nat))
    (hcarries : Carries names env final)
    (hassert : GeneralLinearSSAEffects.assertionsAir final assertions) :
    checkNamedAssertions env (namedAssertions names assertions) = .ok () := by
  obtain ⟨pairs, hresolve, hpoly⟩ := hassert
  induction assertions generalizing pairs with
  | nil =>
      simp [checkNamedAssertions, namedAssertions]
  | cons pair rest ih =>
      obtain ⟨lhs, rhs⟩ := pair
      simp only [GeneralLinearSSAEffects.resolveAssertions,
        List.mapM_cons] at hresolve
      cases hleft : final[lhs]? with
      | none => simp [hleft] at hresolve
      | some left =>
          cases hright : final[rhs]? with
          | none => simp [hleft, hright] at hresolve
          | some right =>
              simp only [hleft, hright, Option.bind_some] at hresolve
              change (GeneralLinearSSAEffects.resolveAssertions final rest).bind
                (fun tail => some ((left, right) :: tail)) = some pairs at hresolve
              cases hrest : GeneralLinearSSAEffects.resolveAssertions
                  final rest with
              | none => simp [hrest] at hresolve
              | some tail =>
                  have hpairs : pairs = (left, right) :: tail := by
                    simpa [hrest] using hresolve.symm
                  subst pairs
                  have hfirst : GeneralLinearSSAEffects.assertionPoly
                      left right := hpoly (left, right) (by simp)
                  have htail : ∀ p ∈ tail,
                      GeneralLinearSSAEffects.assertionPoly p.1 p.2 := by
                    intro p hmem
                    exact hpoly p (by simp [hmem])
                  have hsingle :=
                    (named_assertion_iff_air env
                      (nameAt names lhs) (nameAt names rhs)
                      left right
                      (hcarries lhs left hleft)
                      (hcarries rhs right hright)).mpr hfirst
                  simpa [checkNamedAssertions, namedAssertions,
                    hsingle] using ih tail hrest htail

/-- Conversely, an accepted normalized assertion sequence constrains every
resolved indexed pair. This direction makes actual interpreter acceptance
usable for soundness without assuming assertion polynomials in advance. -/
theorem assertion_air_of_named_checks {n : Nat}
    (names : List String) (env : S31.Env)
    (final : List (Lanes n)) (assertions : List (Nat × Nat))
    (pairs : List (Lanes n × Lanes n))
    (hcarries : Carries names env final)
    (hresolved : GeneralLinearSSAEffects.resolveAssertions final assertions =
      some pairs)
    (hcheck : checkNamedAssertions env (namedAssertions names assertions) =
      .ok ()) :
    ∀ pair ∈ pairs,
      GeneralLinearSSAEffects.assertionPoly pair.1 pair.2 := by
  induction assertions generalizing pairs with
  | nil =>
      have hnil : pairs = [] := by
        simpa [GeneralLinearSSAEffects.resolveAssertions] using
          hresolved.symm
      subst pairs
      simp
  | cons first rest ih =>
      obtain ⟨lhs, rhs⟩ := first
      simp only [GeneralLinearSSAEffects.resolveAssertions,
        List.mapM_cons] at hresolved
      cases hleft : final[lhs]? with
      | none => simp [hleft] at hresolved
      | some left =>
          cases hright : final[rhs]? with
          | none => simp [hleft, hright] at hresolved
          | some right =>
              simp only [hleft, hright, Option.bind_some] at hresolved
              change (GeneralLinearSSAEffects.resolveAssertions final rest).bind
                (fun tail => some ((left, right) :: tail)) = some pairs
                at hresolved
              cases hrest : GeneralLinearSSAEffects.resolveAssertions final rest with
              | none => simp [hrest] at hresolved
              | some tail =>
                  have hpairs : pairs = (left, right) :: tail := by
                    simpa [hrest] using hresolved.symm
                  subst pairs
                  have hsingle : checkNamedAssertion env
                      (nameAt names lhs) (nameAt names rhs) = .ok () := by
                    unfold checkNamedAssertions namedAssertions at hcheck
                    cases hfirst : checkNamedAssertion env
                        (nameAt names lhs) (nameAt names rhs) with
                    | error err =>
                        simp [hfirst, Bind.bind, Except.bind] at hcheck
                    | ok result => cases result; rfl
                  have htailCheck :
                      checkNamedAssertions env
                        (namedAssertions names rest) = .ok () := by
                    simpa [checkNamedAssertions, namedAssertions, hsingle]
                      using hcheck
                  have hfirstPoly :=
                    (named_assertion_iff_air env
                      (nameAt names lhs) (nameAt names rhs)
                      left right
                      (hcarries lhs left hleft)
                      (hcarries rhs right hright)).mp hsingle
                  intro pair hmem
                  rcases List.mem_cons.mp hmem with heq | htail
                  · subst pair
                    exact hfirstPoly
                  · exact ih tail hrest htailCheck pair htail

private theorem named_effect_fold_eq_nodes (names : List String)
    (steps : List GeneralLinearSSAEffects.Step) (env : S31.Env) :
    (steps.map (namedEffectNode names)).foldlM
      (fun env node => do
        return env ++ [(node.name, ← S31.evaluateNode env node)]) env =
      steps.foldlM (namedEffectStep names) env := by
  rw [List.foldlM_map]
  rfl

/-- Accepted modeled effectful rows and assertion polynomials execute
through the real normalized `Program.environment`. The exact source graph,
typed input state and fresh-name invariants remain explicit premises. -/
theorem effect_program_environment_follows_air {n : Nat}
    (program : S31.Program) (assignment : S31.Assignment)
    (names : List String) (certificate : GeneralLinearSSAEffects.Certificate)
    (initial final : List (Lanes n)) (inputEnv : S31.Env)
    (hvalid : ∃ shapes, program.validate = .ok shapes)
    (hprivate : S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true)
    (hinputs : program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then
        assignment.publicInputs else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv)
    (hnodes : program.nodes =
      certificate.steps.map (namedEffectNode names))
    (hassertions : program.assertions =
      namedAssertions names certificate.assertions)
    (hrows : GeneralLinearSSAEffects.AcceptsTrace initial
      certificate.steps final)
    (hassert : GeneralLinearSSAEffects.assertionsAir final
      certificate.assertions)
    (hcarries : Carries names inputEnv initial)
    (habent : Absent names inputEnv initial.length
      (initial.length + certificate.steps.length))
    (hdistinct : Distinct names
      (initial.length + certificate.steps.length)) :
    ∃ finalEnv,
      program.environment assignment = .ok finalEnv ∧
      Carries names finalEnv final := by
  obtain ⟨shapes, hvalidate⟩ := hvalid
  obtain ⟨finalEnv, hfold, hcarryFinal, _⟩ :=
    named_effect_fold_of_air names inputEnv hrows rfl hdistinct
      hcarries habent
  have hnodesFold :
      program.nodes.foldlM
        (fun env node => do
          return env ++ [(node.name, ← S31.evaluateNode env node)]) inputEnv =
        .ok finalEnv := by
    rw [hnodes]
    rw [named_effect_fold_eq_nodes]
    exact hfold
  have hassertRun := named_assertions_of_air names finalEnv final
    certificate.assertions hcarryFinal hassert
  have hloop :
      ((do
        for (lhs, rhs) in program.assertions do
          let left ← S31.need (S31.lookup finalEnv lhs) .unknownOperand
          let right ← S31.need (S31.lookup finalEnv rhs) .unknownOperand
          S31.require (left == right) .assertionFailed
        pure ()) : S31.Result Unit) = .ok () := by
    rw [hassertions]
    rw [normalized_assertion_loop_eq]
    exact hassertRun
  refine ⟨finalEnv, ?_, hcarryFinal⟩
  unfold S31.Program.environment
  rw [hvalidate]
  simp only [hprivate, hinputs]
  simp only [S31.require, ↓reduceIte,
    Bind.bind, Except.bind, Pure.pure, Except.pure] at hnodesFold ⊢
  simp only [hnodesFold]
  let body : (String × String) → PUnit →
      S31.Result (ForInStep PUnit) := fun (lhs, rhs) _ => do
    let left ← S31.need (S31.lookup finalEnv lhs) .unknownOperand
    let right ← S31.need (S31.lookup finalEnv rhs) .unknownOperand
    S31.require (left == right) .assertionFailed
    pure (.yield .unit)
  have hloop' :
      (do let _ ← forIn program.assertions PUnit.unit body
          pure ()) = .ok () := by
    simpa [body] using hloop
  have hfor : forIn program.assertions PUnit.unit body =
      (.ok PUnit.unit : S31.Result PUnit) := by
    cases hrun : forIn program.assertions PUnit.unit body with
    | error err => simp [hrun] at hloop'
    | ok result => cases result; rfl
  simp only [body, S31.require, ↓reduceIte, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at hfor
  simpa only [hfor]

/-- Reverse assertion direction: acceptance by the actual normalized
environment, together with arbitrary accepted arithmetic AIR rows, forces
all modeled assertion polynomials. The resolved-pair premise is structural
certificate well-formedness, not an assertion-success premise. -/
theorem effect_program_environment_implies_assertions_air {n : Nat}
    (program : S31.Program) (assignment : S31.Assignment)
    (names : List String) (certificate : GeneralLinearSSAEffects.Certificate)
    (initial final : List (Lanes n)) (inputEnv observed : S31.Env)
    (pairs : List (Lanes n × Lanes n))
    (hvalid : ∃ shapes, program.validate = .ok shapes)
    (hprivate : S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true)
    (hinputs : program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then
        assignment.publicInputs else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv)
    (hnodes : program.nodes =
      certificate.steps.map (namedEffectNode names))
    (hassertions : program.assertions =
      namedAssertions names certificate.assertions)
    (hrows : GeneralLinearSSAEffects.AcceptsTrace initial
      certificate.steps final)
    (hresolved : GeneralLinearSSAEffects.resolveAssertions final
      certificate.assertions = some pairs)
    (hcarries : Carries names inputEnv initial)
    (habent : Absent names inputEnv initial.length
      (initial.length + certificate.steps.length))
    (hdistinct : Distinct names
      (initial.length + certificate.steps.length))
    (henv : program.environment assignment = .ok observed) :
    GeneralLinearSSAEffects.assertionsAir final certificate.assertions := by
  obtain ⟨shapes, hvalidate⟩ := hvalid
  obtain ⟨finalEnv, hfold, hcarryFinal, _⟩ :=
    named_effect_fold_of_air names inputEnv hrows rfl hdistinct
      hcarries habent
  have hnodesFold :
      program.nodes.foldlM
        (fun env node => do
          return env ++ [(node.name, ← S31.evaluateNode env node)]) inputEnv =
        .ok finalEnv := by
    rw [hnodes, named_effect_fold_eq_nodes]
    exact hfold
  unfold S31.Program.environment at henv
  rw [hvalidate] at henv
  simp only [hprivate, hinputs] at henv
  simp only [S31.require, ↓reduceIte, Bind.bind, Except.bind,
    Pure.pure, Except.pure] at hnodesFold henv
  simp only [hnodesFold] at henv
  let body : (String × String) → PUnit →
      S31.Result (ForInStep PUnit) := fun (lhs, rhs) _ => do
    let left ← S31.need (S31.lookup finalEnv lhs) .unknownOperand
    let right ← S31.need (S31.lookup finalEnv rhs) .unknownOperand
    S31.require (left == right) .assertionFailed
    pure (.yield .unit)
  have hloopRaw : forIn program.assertions PUnit.unit body =
      (.ok PUnit.unit : S31.Result PUnit) := by
    cases hrun : forIn program.assertions PUnit.unit body with
    | error err =>
        simp only [body, S31.require, ↓reduceIte, Bind.bind,
          Except.bind, Pure.pure, Except.pure] at hrun
        rw [hrun] at henv
        cases henv
    | ok result => cases result; rfl
  have hloop :
      ((do
        for (lhs, rhs) in program.assertions do
          let left ← S31.need (S31.lookup finalEnv lhs) .unknownOperand
          let right ← S31.need (S31.lookup finalEnv rhs) .unknownOperand
          S31.require (left == right) .assertionFailed
        pure ()) : S31.Result Unit) = .ok () := by
    have hloopRaw' := hloopRaw
    simp only [body, S31.require, ↓reduceIte, Bind.bind,
      Except.bind, Pure.pure, Except.pure] at hloopRaw'
    simp only [S31.require, ↓reduceIte, Bind.bind,
      Except.bind, Pure.pure, Except.pure] at ⊢
    simpa only [hloopRaw', Bind.bind, Except.bind,
      Pure.pure, Except.pure]
  rw [normalized_assertion_loop_eq] at hloop
  rw [hassertions] at hloop
  exact ⟨pairs, hresolved,
    assertion_air_of_named_checks names finalEnv final
      certificate.assertions pairs hcarryFinal hresolved hloop⟩

/-- The accepted normalized interpreter cannot silently drop an effectful
source assertion. Arithmetic AIR rows and the exact indexed/named graph are
explicit premises; assertion polynomials are derived from the interpreter's
own successful assertion loop, never assumed. -/
theorem effectful_interpreter_preserves_source_assertions {n : Nat}
    (program : S31.Program) (assignment : S31.Assignment)
    (names : List String) (certificate : GeneralLinearSSAEffects.Certificate)
    (source : GeneralLinearSSAEffects.Source)
    (inputs : Nat → Lanes n) (inputEnv : S31.Env)
    (final : List (Lanes n)) (words : List S31.M31)
    (hcertificate : GeneralLinearSSAEffects.check certificate source =
      some ())
    (hvalid : ∃ shapes, program.validate = .ok shapes)
    (hprivate : S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true)
    (hinputs : program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then
        assignment.publicInputs else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv)
    (hnodes : program.nodes =
      certificate.steps.map (namedEffectNode names))
    (hassertions : program.assertions =
      namedAssertions names certificate.assertions)
    (hrows : GeneralLinearSSAEffects.AcceptsTrace
      (GeneralLinearSSAEffects.initialValues certificate.inputs inputs)
      certificate.steps final)
    (hcarries : Carries names inputEnv
      (GeneralLinearSSAEffects.initialValues certificate.inputs inputs))
    (habent : Absent names inputEnv
      (GeneralLinearSSAEffects.initialValues certificate.inputs inputs).length
      ((GeneralLinearSSAEffects.initialValues certificate.inputs inputs).length +
        certificate.steps.length))
    (hdistinct : Distinct names
      ((GeneralLinearSSAEffects.initialValues certificate.inputs inputs).length +
        certificate.steps.length))
    (haccept : program.evaluate assignment = .ok words) :
    source.accepts inputs (source.output.eval inputs) := by
  have hsem := GeneralLinearSSAEffects.checked_execution
    certificate source inputs hcertificate
  have hrun := GeneralLinearSSAEffects.accepted_trace_executes hrows
  unfold GeneralLinearSSAEffects.execute at hsem
  rw [hrun] at hsem
  cases hout : final[certificate.output]? with
  | none => simp [hout] at hsem
  | some output =>
      cases hass : GeneralLinearSSAEffects.resolveAssertions final
          certificate.assertions with
      | none => simp [hout, hass] at hsem
      | some pairs =>
          have hpair : (output, pairs) =
              (source.output.eval inputs,
                source.assertions.map fun pair =>
                  (pair.1.eval inputs, pair.2.eval inputs)) :=
            Option.some.inj (by simpa [hout, hass] using hsem)
          have houtput : final[certificate.output]? =
              some (source.output.eval inputs) := by
            have houtputVal : output = source.output.eval inputs :=
              congrArg Prod.fst hpair
            simpa [houtputVal] using hout
          have henv : ∃ observed,
              program.environment assignment = .ok observed := by
            unfold S31.Program.evaluate at haccept
            cases h : program.environment assignment with
            | error err =>
                simp [h, Bind.bind, Except.bind] at haccept
            | ok observed => exact ⟨observed, rfl⟩
          obtain ⟨observed, henv⟩ := henv
          have hassert := effect_program_environment_implies_assertions_air
            program assignment names certificate
            (GeneralLinearSSAEffects.initialValues certificate.inputs inputs)
            final inputEnv observed pairs hvalid hprivate hinputs hnodes
            hassertions hrows hass hcarries habent hdistinct henv
          exact GeneralLinearSSAEffects.checked_air_sound certificate
            source inputs (source.output.eval inputs) final hcertificate
            hrows houtput hassert

/-- For a checked effectful source certificate, accepted arithmetic rows and
the actual normalized evaluator force the assigned public output to equal the
source value. Successful evaluation supplies assertion acceptance; its AIR
assertion polynomials are derived from that success, not assumed. Exact graph,
input-state, and output-name alignment remain explicit premises. -/
theorem effectful_interpreter_public_output_claim {n : Nat}
    (program : S31.Program) (assignment : S31.Assignment)
    (names : List String) (certificate : GeneralLinearSSAEffects.Certificate)
    (source : GeneralLinearSSAEffects.Source)
    (inputs : Nat → Lanes n) (inputEnv : S31.Env)
    (final : List (Lanes n)) (words : List S31.M31)
    (hcertificate : GeneralLinearSSAEffects.check certificate source =
      some ())
    (hvalid : ∃ shapes, program.validate = .ok shapes)
    (hprivate : S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true)
    (hinputs : program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then
        assignment.publicInputs else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv)
    (hnodes : program.nodes =
      certificate.steps.map (namedEffectNode names))
    (hassertions : program.assertions =
      namedAssertions names certificate.assertions)
    (houtputs : program.outputs = [nameAt names certificate.output])
    (hrows : GeneralLinearSSAEffects.AcceptsTrace
      (GeneralLinearSSAEffects.initialValues certificate.inputs inputs)
      certificate.steps final)
    (hcarries : Carries names inputEnv
      (GeneralLinearSSAEffects.initialValues certificate.inputs inputs))
    (habent : Absent names inputEnv
      (GeneralLinearSSAEffects.initialValues certificate.inputs inputs).length
      ((GeneralLinearSSAEffects.initialValues certificate.inputs inputs).length +
        certificate.steps.length))
    (hdistinct : Distinct names
      ((GeneralLinearSSAEffects.initialValues certificate.inputs inputs).length +
        certificate.steps.length))
    (haccept : program.evaluate assignment = .ok words) :
    S31.assigned assignment.publicOutputs
      (nameAt names certificate.output) ⟨.m31, n⟩ =
        .ok (laneValue (source.output.eval inputs)) := by
  have hsem := GeneralLinearSSAEffects.checked_execution
    certificate source inputs hcertificate
  have hrun := GeneralLinearSSAEffects.accepted_trace_executes hrows
  unfold GeneralLinearSSAEffects.execute at hsem
  rw [hrun] at hsem
  cases hout : final[certificate.output]? with
  | none => simp [hout] at hsem
  | some output =>
      cases hass : GeneralLinearSSAEffects.resolveAssertions final
          certificate.assertions with
      | none => simp [hout, hass] at hsem
      | some pairs =>
          have hpair : (output, pairs) =
              (source.output.eval inputs,
                source.assertions.map fun pair =>
                  (pair.1.eval inputs, pair.2.eval inputs)) :=
            Option.some.inj (by simpa [hout, hass] using hsem)
          have houtput : final[certificate.output]? =
              some (source.output.eval inputs) := by
            have houtputVal : output = source.output.eval inputs :=
              congrArg Prod.fst hpair
            simpa [houtputVal] using hout
          have henv : ∃ observed,
              program.environment assignment = .ok observed := by
            unfold S31.Program.evaluate at haccept
            cases h : program.environment assignment with
            | error err =>
                simp [h, Bind.bind, Except.bind] at haccept
            | ok observed => exact ⟨observed, rfl⟩
          obtain ⟨observed, henv⟩ := henv
          have hassert := effect_program_environment_implies_assertions_air
            program assignment names certificate
            (GeneralLinearSSAEffects.initialValues certificate.inputs inputs)
            final inputEnv observed pairs hvalid hprivate hinputs hnodes
            hassertions hrows hass hcarries habent hdistinct henv
          obtain ⟨finalEnv, henvFinal, hcarryFinal⟩ :=
            effect_program_environment_follows_air program assignment names
              certificate
              (GeneralLinearSSAEffects.initialValues certificate.inputs inputs)
              final inputEnv hvalid hprivate hinputs hnodes hassertions
              hrows hassert hcarries habent hdistinct
          exact public_output_claim_of_environment program assignment
            finalEnv (nameAt names certificate.output)
            (source.output.eval inputs) words henvFinal houtputs
            (hcarryFinal certificate.output
              (source.output.eval inputs) houtput) haccept

end S31.Functional.Correspondence.GeneralLinearSSAEffectsEvaluator
