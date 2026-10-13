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

end S31.Functional.Correspondence.GeneralLinearSSAEffectsEvaluator
