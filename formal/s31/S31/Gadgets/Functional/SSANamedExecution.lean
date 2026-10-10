import S31.Gadgets.Functional.SSANamedProgram

/-!
Generic execution agreement for validated canonical named programs in the
four-lane add/mul/static-let fragment. This module reasons about the actual
normalized Program.environment fold and evaluateNode, with explicit finite
canonical-name injectivity and accepted-assignment premises.
-/

namespace S31.Functional.SSANamedExecution

open S31
open S31.Functional.SSACertificate
open S31.Functional.SSANamedProgram
open S31.Functional.SSAEmitterProof

def laneValue (value : Lanes) : Value :=
  ⟨.m31, List.ofFn value⟩

private theorem lookup_shapes (env : S31.Env) (name : String) :
    lookup (env.map (fun (key, value) => (key, value.shape))) name =
      (lookup env name).map Value.shape := by
  simp [lookup, List.find?_map, Function.comp_def]

private theorem named_node_eval (instruction : Instruction)
    (env : S31.Env) (lhs rhs : Lanes)
    (hlhs : lookup env (wireName instruction.lhs) = some (laneValue lhs))
    (hrhs : lookup env (wireName instruction.rhs) = some (laneValue rhs)) :
    evaluateNode env (SSANamedProgram.Instruction.toNode instruction) =
      .ok (laneValue (instructionValue instruction.multiply lhs rhs)) := by
  have hshapeL :
      lookup (env.map (fun (name, value) => (name, value.shape)))
        (wireName instruction.lhs) = some ⟨.m31, 4⟩ := by
    rw [lookup_shapes, hlhs]
    rfl
  have hshapeR :
      lookup (env.map (fun (name, value) => (name, value.shape)))
        (wireName instruction.rhs) = some ⟨.m31, 4⟩ := by
    rw [lookup_shapes, hrhs]
    rfl
  have hinfer :
      inferNode (env.map (fun (name, value) => (name, value.shape)))
        (SSANamedProgram.Instruction.toNode instruction) =
        .ok ⟨.m31, 4⟩ := by
    have hkind : (Kind.m31 == Kind.m31) = true := rfl
    cases hm : instruction.multiply <;>
      simp [SSANamedProgram.Instruction.toNode, hm,
        inferNode, Node.metadataValid, Node.fields, shapeOperand,
        expectShape, need, require, hshapeL, hshapeR, hkind,
        Bind.bind, Except.bind, Except.map]
    all_goals rfl
  unfold evaluateNode
  rw [hinfer]
  cases hm : instruction.multiply <;>
    simp [SSANamedProgram.Instruction.toNode, hm,
      valueOperand, hlhs, hrhs, Value.shape, Value.valid,
      laneValue, instructionValue, Bind.bind, Except.bind]
  all_goals rfl

private def namedStep (env : S31.Env) (instruction : Instruction) :
    S31.Result S31.Env := do
  let node := SSANamedProgram.Instruction.toNode instruction
  return env ++ [(node.name, ← evaluateNode env node)]

private def Carries (env : S31.Env) (terms : List Term)
    (input : Lanes) : Prop :=
  ∀ index term, terms[index]? = some term →
    lookup env (wireName index) = some (laneValue (term.eval input))

private def Absent (env : S31.Env) (next maximum : Nat) : Prop :=
  ∀ index, next ≤ index → index < maximum →
    lookup env (wireName index) = none

def Distinct (maximum : Nat) : Prop :=
  ∀ i j, i < maximum → j < maximum →
    wireName i = wireName j → i = j

/-- A finite, executable bound on canonical wire-name collisions. -/
def namesDistinct (certificate : Certificate) : Prop :=
  ((List.range (certificate.instructions.length + 1)).map wireName).Nodup

def checkBounded (source : Source 1) (certificate : Certificate)
    (program : Program) : Option Unit :=
  letI : Decidable (namesDistinct certificate) := by
    unfold namesDistinct
    infer_instance
  if namesDistinct certificate then checkNamed source certificate program
  else none

theorem namesDistinct_implies_distinct (certificate : Certificate)
    (h : namesDistinct certificate) :
    Distinct (certificate.instructions.length + 1) := by
  intro i j hi hj heq
  exact (List.nodup_map_iff_inj_on List.nodup_range).mp h
    i ((List.mem_range).mpr hi) j ((List.mem_range).mpr hj) heq

theorem checkBounded_named (source : Source 1)
    (certificate : Certificate) (program : Program)
    (h : checkBounded source certificate program = some ()) :
    checkNamed source certificate program = some () := by
  unfold checkBounded at h
  by_cases hname : namesDistinct certificate
  · simpa [hname] using h
  · simp [hname] at h

theorem checkBounded_distinct (source : Source 1)
    (certificate : Certificate) (program : Program)
    (h : checkBounded source certificate program = some ()) :
    Distinct (certificate.instructions.length + 1) := by
  unfold checkBounded at h
  by_cases hname : namesDistinct certificate
  · exact namesDistinct_implies_distinct certificate hname
  · simp [hname] at h

private theorem lookup_append_some (env suffix : S31.Env)
    (name : String) (value : Value)
    (h : lookup env name = some value) :
    lookup (env ++ suffix) name = some value := by
  unfold lookup at h ⊢
  rw [List.find?_append]
  cases hfind : env.find? (fun pair => pair.1 == name) with
  | none => simp [hfind] at h
  | some pair =>
      simp [hfind] at h ⊢
      exact h

private theorem lookup_append_fresh (env : S31.Env)
    (name : String) (value : Value)
    (h : lookup env name = none) :
    lookup (env ++ [(name, value)]) name = some value := by
  unfold lookup at h ⊢
  rw [List.find?_append]
  cases hfind : env.find? (fun pair => pair.1 == name) with
  | none => simp
  | some pair => simp [hfind] at h

private theorem lookup_append_other (env : S31.Env)
    (name newName : String) (value : Value)
    (h : lookup env name = none) (hne : name ≠ newName) :
    lookup (env ++ [(newName, value)]) name = none := by
  unfold lookup at h ⊢
  rw [List.find?_append]
  cases hfind : env.find? (fun pair => pair.1 == name) with
  | none => simp [Ne.symm hne]
  | some pair => simp [hfind] at h

private theorem initial_carries (input : Lanes) :
    Carries [("x", laneValue input)] [Term.input] input := by
  intro index term h
  cases index with
  | zero =>
      have ht : term = Term.input := by
        simpa using h.symm
      subst term
      rfl
  | succ index =>
      simp at h

private theorem initial_absent (input : Lanes) (maximum : Nat)
    (hDistinct : Distinct maximum) (hmax : 0 < maximum) :
    Absent [("x", laneValue input)] 1 maximum := by
  intro index hnext hindex
  have hne : wireName index ≠ "x" := by
    intro heq
    have hzero : wireName 0 = "x" := rfl
    have hi : index = 0 :=
      hDistinct index 0 hindex hmax (heq.trans hzero.symm)
    omega
  simp [lookup, Ne.symm hne]

private theorem named_step_correct (terms : List Term)
    (env : S31.Env) (instruction : Instruction)
    (input : Lanes) (maximum : Nat)
    (hbudget : terms.length < maximum)
    (hdistinct : Distinct maximum)
    (hcarries : Carries env terms input)
    (habent : Absent env terms.length maximum)
    (next : List Term)
    (hstep : checkStep terms instruction = some next) :
    ∃ nextEnv,
      namedStep env instruction = .ok nextEnv ∧
      Carries nextEnv next input ∧
      Absent nextEnv next.length maximum ∧
      next.length = terms.length + 1 := by
  have hid : instruction.id = terms.length := by
    by_contra hne
    simp [checkStep, hne] at hstep
  cases hleft : terms[instruction.lhs]? with
  | none => simp [checkStep, hid, hleft] at hstep
  | some left =>
      cases hright : terms[instruction.rhs]? with
      | none => simp [checkStep, hid, hleft, hright] at hstep
      | some right =>
          have hnext : next =
              terms ++ [instructionTerm instruction.multiply left right] := by
            simpa [checkStep, hid, hleft, hright] using hstep.symm
          let newTerm :=
            instructionTerm instruction.multiply left right
          let newValue := newTerm.eval input
          have hlookupLeft := hcarries instruction.lhs left hleft
          have hlookupRight := hcarries instruction.rhs right hright
          have heval :
              evaluateNode env
                  (SSANamedProgram.Instruction.toNode instruction) =
                .ok (laneValue newValue) := by
            simpa [newValue, newTerm, instruction_term_eval] using
              named_node_eval instruction env (left.eval input)
                (right.eval input) hlookupLeft hlookupRight
          have hnamed :
              namedStep env instruction =
                .ok (env ++ [(wireName instruction.id,
                  laneValue newValue)]) := by
            change (do
              let out ← evaluateNode env
                (SSANamedProgram.Instruction.toNode instruction)
              pure (env ++ [(wireName instruction.id, out)])) = _
            rw [heval]
            rfl
          refine ⟨env ++ [(wireName instruction.id, laneValue newValue)],
            hnamed, ?_, ?_, ?_⟩
          · intro index term hterm
            by_cases hold : index < terms.length
            · have htermOld : terms[index]? = some term := by
                rw [hnext, List.getElem?_append_left hold] at hterm
                exact hterm
              exact lookup_append_some env _ (wireName index)
                (laneValue (term.eval input))
                (hcarries index term htermOld)
            · have hindex : index = terms.length := by
                have hindexBound :
                    index < next.length :=
                  (List.getElem?_eq_some_iff.mp hterm).1
                simp [hnext] at hindexBound
                omega
              subst index
              have hsame : term = newTerm := by
                simpa [hnext, newTerm] using hterm.symm
              subst term
              have hfresh : lookup env (wireName instruction.id) = none := by
                rw [hid]
                exact habent terms.length (by omega) hbudget
              simpa [newValue, newTerm, hid] using
                lookup_append_fresh env (wireName instruction.id)
                  (laneValue newValue) hfresh
          · intro index hindex hmax
            have hlast : next.length = terms.length + 1 := by
              simp [hnext]
            have holdIndex : terms.length ≤ index := by omega
            have hnone : lookup env (wireName index) = none :=
              habent index holdIndex hmax
            have hne : wireName index ≠ wireName instruction.id := by
              intro heq
              have hsame := hdistinct index instruction.id hmax
                (by rw [hid]; exact hbudget) heq
              omega
            exact lookup_append_other env (wireName index)
              (wireName instruction.id) (laneValue newValue) hnone hne
          · simp [hnext]

private theorem folds_correct (instructions : List Instruction)
    (terms finalTerms : List Term) (env : S31.Env)
    (input : Lanes) (maximum : Nat)
    (hbudget : terms.length + instructions.length ≤ maximum)
    (hdistinct : Distinct maximum)
    (hcarries : Carries env terms input)
    (habent : Absent env terms.length maximum)
    (hcheck : instructions.foldlM checkStep terms = some finalTerms) :
    ∃ finalEnv,
      instructions.foldlM namedStep env = .ok finalEnv ∧
      Carries finalEnv finalTerms input ∧
      Absent finalEnv finalTerms.length maximum := by
  induction instructions generalizing terms env with
  | nil =>
      have hfinal : finalTerms = terms := by
        simpa using hcheck.symm
      subst finalTerms
      exact ⟨env, rfl, hcarries, habent⟩
  | cons instruction rest ih =>
      have hstepBudget : terms.length < maximum := by
        simp at hbudget
        omega
      cases hstep : checkStep terms instruction with
      | none =>
          simp [List.foldlM_cons, hstep] at hcheck
      | some next =>
          obtain ⟨nextEnv, hnamed, hcarryNext, habsentNext,
            hlength⟩ := named_step_correct terms env instruction input
              maximum hstepBudget hdistinct hcarries habent next hstep
          have hrestBudget : next.length + rest.length ≤ maximum := by
            simp at hbudget
            omega
          have hrestCheck :
              rest.foldlM checkStep next = some finalTerms := by
            simpa [List.foldlM_cons, hstep] using hcheck
          obtain ⟨finalEnv, hrestNamed, hcarryFinal, habsentFinal⟩ :=
            ih next nextEnv hrestBudget hcarryNext
              habsentNext hrestCheck
          refine ⟨finalEnv, ?_, hcarryFinal, habsentFinal⟩
          simpa [List.foldlM_cons, hnamed] using hrestNamed

private theorem named_fold_eq_nodes (instructions : List Instruction)
    (env : S31.Env) :
    (instructions.map SSANamedProgram.Instruction.toNode).foldlM
      (fun env node => do
        return env ++ [(node.name, ← evaluateNode env node)]) env =
      instructions.foldlM namedStep env := by
  rw [List.foldlM_map]
  rfl

/-- Every checked positional SSA certificate has the same source value when
its canonical named nodes are evaluated with actual name lookup and
`evaluateNode`. The finite injectivity premise states the exact name bound
needed by the normalized validator. -/
theorem checked_named_nodes_sound (source : Source 1)
    (certificate : Certificate) (input : Lanes)
    (hdistinct : Distinct (certificate.instructions.length + 1))
    (hcheck : check source certificate = some ()) :
    ∃ finalEnv,
      (encode certificate).nodes.foldlM
        (fun env node => do
          return env ++ [(node.name, ← evaluateNode env node)])
        [("x", laneValue input)] = .ok finalEnv ∧
      lookup finalEnv (wireName certificate.output) =
        some (laneValue (source.value (fun _ => input))) := by
  unfold check at hcheck
  cases hterms :
      certificate.instructions.foldlM checkStep [Term.input] with
  | none => simp [hterms] at hcheck
  | some finalTerms =>
      cases houtput : finalTerms[certificate.output]? with
      | none => simp [hterms, houtput] at hcheck
      | some outputTerm =>
          have hterm :
              outputTerm = source.elaborate (fun _ => Term.input) := by
            have hdec :
                (outputTerm ==
                  source.elaborate (fun _ => Term.input)) = true := by
              simpa [hterms, houtput] using hcheck
            exact of_decide_eq_true hdec
          have hmax : 0 < certificate.instructions.length + 1 := by omega
          obtain ⟨finalEnv, hfold, hcarries, _⟩ :=
            folds_correct certificate.instructions [Term.input]
              finalTerms [("x", laneValue input)] input
              (certificate.instructions.length + 1)
              (by simp [Nat.add_comm]) hdistinct (initial_carries input)
              (initial_absent input _ hdistinct hmax) hterms
          refine ⟨finalEnv, ?_, ?_⟩
          · change (certificate.instructions.map
                SSANamedProgram.Instruction.toNode).foldlM
                (fun env node => do
                  return env ++ [(node.name, ← evaluateNode env node)])
                [("x", laneValue input)] = .ok finalEnv
            rw [named_fold_eq_nodes]
            exact hfold
          · have hlook := hcarries certificate.output outputTerm houtput
            simpa [hterm, Source.elaborate_eval, Term.eval] using hlook

/-- The actual normalized program environment agrees with source semantics
for every checked canonical named certificate and accepted four-lane input.
The explicit finite-name condition prevents aliases among serialized wires.
The validator premise comes from `checkNamed`; no claim about the Python
serializer or Zig AIR emitter is made. -/
theorem checked_program_environment_sound (source : Source 1)
    (certificate : Certificate) (program : Program)
    (assignment : Assignment) (input : Lanes)
    (hNamed : checkNamed source certificate program = some ())
    (hdistinct : Distinct (certificate.instructions.length + 1))
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs "x" ⟨.m31, 4⟩ =
      .ok (laneValue input)) :
    ∃ finalEnv,
      program.environment assignment = .ok finalEnv ∧
      lookup finalEnv (wireName certificate.output) =
        some (laneValue (source.value (fun _ => input))) := by
  have hcanonical := checkNamed_canonical source certificate program hNamed
  have hcheck := checkNamed_positional source certificate program hNamed
  obtain ⟨shapes, hvalid⟩ :=
    checkNamed_valid source certificate program hNamed
  obtain ⟨finalEnv, hfold, hlookup⟩ :=
    checked_named_nodes_sound source certificate input hdistinct hcheck
  have hprivateFields :
      exactFields assignment.privateInputs
        ((program.inputs.filter (fun i => i.visibility == .private)).map
          (·.name)) = true := by
    rw [hcanonical, hprivate]
    have hpubprivate :
        (Visibility.«public» == Visibility.private) = false := by decide
    simp [encode, exactFields, hpubprivate]
  have hmap :
      program.inputs.mapM (fun i => do
        let raw := if i.visibility == Visibility.«public» then
          assignment.publicInputs else assignment.privateInputs
        return (i.name, ← assigned raw i.name i.shape)) =
        .ok [("x", laneValue input)] := by
    rw [hcanonical]
    have hpublic :
        (Visibility.«public» == Visibility.«public») = true := by decide
    simp [encode, List.mapM, List.mapM.loop, hpublic, hinput]
  have hfoldProgram :
      program.nodes.foldlM
        (fun env node => do
          return env ++ [(node.name, ← evaluateNode env node)])
        [("x", laneValue input)] = .ok finalEnv := by
    rw [hcanonical]
    exact hfold
  have hassertions : program.assertions = [] := by
    simp [hcanonical, encode]
  refine ⟨finalEnv, ?_, hlookup⟩
  unfold Program.environment
  rw [hvalid]
  simp only [hprivateFields, hmap, hassertions]
  simpa [require, hfoldProgram] using hfoldProgram

/-- The finite name check discharges the injectivity premise of the generic
named-environment theorem. -/
theorem checked_bounded_environment_sound (source : Source 1)
    (certificate : Certificate) (program : Program)
    (assignment : Assignment) (input : Lanes)
    (hBounded : checkBounded source certificate program = some ())
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs "x" ⟨.m31, 4⟩ =
      .ok (laneValue input)) :
    ∃ finalEnv,
      program.environment assignment = .ok finalEnv ∧
      lookup finalEnv (wireName certificate.output) =
        some (laneValue (source.value (fun _ => input))) :=
  checked_program_environment_sound source certificate program
    assignment input (checkBounded_named source certificate program hBounded)
    (checkBounded_distinct source certificate program hBounded)
    hprivate hinput

/-- Every supported source is accepted by the canonical named checker when
its finite name set is collision-free and its canonical Program validates.
Those are executable, explicit bounds rather than axioms about serialization. -/
theorem compiled_bounded_accepted (source : Source 1)
    (hnames : namesDistinct (compile source))
    (hvalid : ∃ shapes, (encode (compile source)).validate = .ok shapes) :
    checkBounded source (compile source)
      (encode (compile source)) = some () := by
  obtain ⟨shapes, hvalid⟩ := hvalid
  have hcheck := compile_checked source
  unfold checkBounded
  simp [hnames, checkNamed, hcheck, hvalid]

theorem compiled_bounded_environment_sound (source : Source 1)
    (assignment : Assignment) (input : Lanes)
    (hnames : namesDistinct (compile source))
    (hvalid : ∃ shapes, (encode (compile source)).validate = .ok shapes)
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs "x" ⟨.m31, 4⟩ =
      .ok (laneValue input)) :
    ∃ finalEnv,
      (encode (compile source)).environment assignment = .ok finalEnv ∧
      lookup finalEnv (wireName (compile source).output) =
        some (laneValue (source.value (fun _ => input))) :=
  checked_bounded_environment_sound source (compile source)
    (encode (compile source)) assignment input
    (compiled_bounded_accepted source hnames hvalid) hprivate hinput

theorem shared_square_bounded_accepted :
    checkBounded sharedSquare sharedSquareCertificate
      sharedSquareProgram = some () := by decide

end S31.Functional.SSANamedExecution
