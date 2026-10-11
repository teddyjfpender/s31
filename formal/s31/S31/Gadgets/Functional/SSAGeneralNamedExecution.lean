import S31.Gadgets.Functional.SSAGeneralNamedTopology
import S31.Gadgets.Functional.SSANamedExecution
import Mathlib.Data.List.GetD

/-!
Actual normalized `Program.environment` execution for arbitrary checked wire
names in the bounded four-lane SSA fragment. This proves a general named-fold
semantics, not production Python serialization or native AIR authentication.
-/

namespace S31.Functional.SSAGeneralNamedExecution

open S31
open S31.Functional.SSACertificate
open S31.Functional.SSAGeneralNamedTopology
open S31.Functional.SSANativeTopologyCheck
open S31.Functional.SSANamedExecution (laneValue)

variable (names : List String)

private theorem lookup_shapes (env : S31.Env) (name : String) :
    lookup (env.map (fun (key, value) => (key, value.shape))) name =
      (lookup env name).map Value.shape := by
  simp [lookup, List.find?_map, Function.comp_def]

private theorem named_node_eval (instruction : Instruction)
    (env : S31.Env) (lhs rhs : Lanes)
    (hlhs : lookup env (nameAt names instruction.lhs) = some (laneValue lhs))
    (hrhs : lookup env (nameAt names instruction.rhs) = some (laneValue rhs)) :
    evaluateNode env (instructionNode names instruction) =
      .ok (laneValue (instructionValue instruction.multiply lhs rhs)) := by
  have hshapeL :
      lookup (env.map (fun (name, value) => (name, value.shape)))
        (nameAt names instruction.lhs) = some ⟨.m31, 4⟩ := by
    rw [lookup_shapes, hlhs]
    rfl
  have hshapeR :
      lookup (env.map (fun (name, value) => (name, value.shape)))
        (nameAt names instruction.rhs) = some ⟨.m31, 4⟩ := by
    rw [lookup_shapes, hrhs]
    rfl
  have hinfer :
      inferNode (env.map (fun (name, value) => (name, value.shape)))
        (instructionNode names instruction) =
        .ok ⟨.m31, 4⟩ := by
    have hkind : (Kind.m31 == Kind.m31) = true := rfl
    cases hm : instruction.multiply <;>
      simp [instructionNode, hm,
        inferNode, Node.metadataValid, Node.fields, shapeOperand,
        expectShape, need, require, hshapeL, hshapeR, hkind,
        Bind.bind, Except.bind, Except.map]
    all_goals rfl
  unfold evaluateNode
  rw [hinfer]
  cases hm : instruction.multiply <;>
    simp [instructionNode, hm,
      valueOperand, hlhs, hrhs, Value.shape, Value.valid,
      laneValue, instructionValue, Bind.bind, Except.bind]
  all_goals rfl

private def namedStep (env : S31.Env) (instruction : Instruction) :
    S31.Result S31.Env := do
  let node := instructionNode names instruction
  return env ++ [(node.name, ← evaluateNode env node)]

private def Carries (env : S31.Env) (terms : List Term)
    (input : Lanes) : Prop :=
  ∀ index term, terms[index]? = some term →
    lookup env (nameAt names index) = some (laneValue (term.eval input))

private def Absent (env : S31.Env) (next maximum : Nat) : Prop :=
  ∀ index, next ≤ index → index < maximum →
    lookup env (nameAt names index) = none

def Distinct (maximum : Nat) : Prop :=
  ∀ i j, i < maximum → j < maximum →
    nameAt names i = nameAt names j → i = j

/-- The accepted name table supplies the exact finite injectivity needed by
the named execution induction. This works for arbitrary valid source names. -/
theorem name_table_distinct (certificate : Certificate)
    (hvalid : NameTableValid names certificate) :
    Distinct names (certificate.instructions.length + 1) := by
  intro i j hi hj heq
  have hi' : i < names.length := by rw [hvalid.1]; exact hi
  have hj' : j < names.length := by rw [hvalid.1]; exact hj
  have hnames : names[i] = names[j] := by
    simpa only [nameAt, List.getD_eq_getElem names "" hi',
      List.getD_eq_getElem names "" hj'] using heq
  exact (List.Nodup.getElem_inj_iff hvalid.2.1).mp hnames


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
    Carries names [(nameAt names 0, laneValue input)] [Term.input] input := by
  intro index term h
  cases index with
  | zero =>
      have ht : term = Term.input := by
        simpa using h.symm
      subst term
      simp [lookup, Term.eval]
  | succ index =>
      simp at h

private theorem initial_absent (input : Lanes) (maximum : Nat)
    (hDistinct : Distinct names maximum) (hmax : 0 < maximum) :
    Absent names [(nameAt names 0, laneValue input)] 1 maximum := by
  intro index hnext hindex
  have hne : nameAt names index ≠ nameAt names 0 := by
    intro heq
    have hzero : nameAt names 0 = nameAt names 0 := rfl
    have hi : index = 0 :=
      hDistinct index 0 hindex hmax (heq.trans hzero.symm)
    omega
  simp [lookup, Ne.symm hne]

private theorem named_step_correct (terms : List Term)
    (env : S31.Env) (instruction : Instruction)
    (input : Lanes) (maximum : Nat)
    (hbudget : terms.length < maximum)
    (hdistinct : Distinct names maximum)
    (hcarries : Carries names env terms input)
    (habent : Absent names env terms.length maximum)
    (next : List Term)
    (hstep : checkStep terms instruction = some next) :
    ∃ nextEnv,
      namedStep names env instruction = .ok nextEnv ∧
      Carries names nextEnv next input ∧
      Absent names nextEnv next.length maximum ∧
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
                  (instructionNode names instruction) =
                .ok (laneValue newValue) := by
            simpa [newValue, newTerm, instruction_term_eval] using
              named_node_eval names instruction env (left.eval input)
                (right.eval input) hlookupLeft hlookupRight
          have hnamed :
              namedStep names env instruction =
                .ok (env ++ [(nameAt names instruction.id,
                  laneValue newValue)]) := by
            change (do
              let out ← evaluateNode env
                (instructionNode names instruction)
              pure (env ++ [(nameAt names instruction.id, out)])) = _
            rw [heval]
            rfl
          refine ⟨env ++ [(nameAt names instruction.id, laneValue newValue)],
            hnamed, ?_, ?_, ?_⟩
          · intro index term hterm
            by_cases hold : index < terms.length
            · have htermOld : terms[index]? = some term := by
                rw [hnext, List.getElem?_append_left hold] at hterm
                exact hterm
              exact lookup_append_some env _ (nameAt names index)
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
              have hfresh : lookup env (nameAt names instruction.id) = none := by
                rw [hid]
                exact habent terms.length (by omega) hbudget
              simpa [newValue, newTerm, hid] using
                lookup_append_fresh env (nameAt names instruction.id)
                  (laneValue newValue) hfresh
          · intro index hindex hmax
            have hlast : next.length = terms.length + 1 := by
              simp [hnext]
            have holdIndex : terms.length ≤ index := by omega
            have hnone : lookup env (nameAt names index) = none :=
              habent index holdIndex hmax
            have hne : nameAt names index ≠ nameAt names instruction.id := by
              intro heq
              have hsame := hdistinct index instruction.id hmax
                (by rw [hid]; exact hbudget) heq
              omega
            exact lookup_append_other env (nameAt names index)
              (nameAt names instruction.id) (laneValue newValue) hnone hne
          · simp [hnext]

private theorem folds_correct (instructions : List Instruction)
    (terms finalTerms : List Term) (env : S31.Env)
    (input : Lanes) (maximum : Nat)
    (hbudget : terms.length + instructions.length ≤ maximum)
    (hdistinct : Distinct names maximum)
    (hcarries : Carries names env terms input)
    (habent : Absent names env terms.length maximum)
    (hcheck : instructions.foldlM checkStep terms = some finalTerms) :
    ∃ finalEnv,
      instructions.foldlM (namedStep names) env = .ok finalEnv ∧
      Carries names finalEnv finalTerms input ∧
      Absent names finalEnv finalTerms.length maximum := by
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
            hlength⟩ := named_step_correct names terms env instruction input
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
    (instructions.map (instructionNode names)).foldlM
      (fun env node => do
        return env ++ [(node.name, ← evaluateNode env node)]) env =
      instructions.foldlM (namedStep names) env := by
  rw [List.foldlM_map]
  rfl

/-- Any checked SSA certificate computes the source value under arbitrary
distinct names when its actual normalized nodes use `evaluateNode`. -/
theorem checked_named_nodes_sound (source : Source 1)
    (certificate : Certificate) (input : Lanes)
    (hdistinct : Distinct names (certificate.instructions.length + 1))
    (hcheck : check source certificate = some ()) :
    ∃ finalEnv,
      (certificate.instructions.map (instructionNode names)).foldlM
        (fun env node => do
          return env ++ [(node.name, ← evaluateNode env node)])
        [(nameAt names 0, laneValue input)] = .ok finalEnv ∧
      lookup finalEnv (nameAt names certificate.output) =
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
            folds_correct names certificate.instructions [Term.input]
              finalTerms [(nameAt names 0, laneValue input)] input
              (certificate.instructions.length + 1)
              (by simp [Nat.add_comm]) hdistinct (initial_carries names input)
              (initial_absent names input _ hdistinct hmax) hterms
          refine ⟨finalEnv, ?_, ?_⟩
          · change (certificate.instructions.map
                (instructionNode names)).foldlM
                (fun env node => do
                  return env ++ [(node.name, ← evaluateNode env node)])
                [(nameAt names 0, laneValue input)] = .ok finalEnv
            rw [named_fold_eq_nodes names]
            exact hfold
          · have hlook := hcarries certificate.output outputTerm houtput
            simpa [hterm, Source.elaborate_eval, Term.eval] using hlook

/-- The real `Program.environment` fold agrees with the checked source
semantics for any accepted name table and full named-Program/topology check.
The gate list is checked structurally; this theorem makes no claim about
cryptographic authentication of native row values. -/
theorem checked_named_environment_sound (source : Source 1)
    (certificate : Certificate) (programName : String)
    (program : Program) (gates : List S31.Functional.SSANativeTopologyCheck.Gate)
    (addresses : List Nat) (assignment : Assignment) (input : Lanes)
    (hcheck : checkNamedSourceRows source certificate programName names
      program gates = some addresses)
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs (nameAt names 0) ⟨.m31, 4⟩ =
      .ok (laneValue input)) :
    ∃ finalEnv,
      program.environment assignment = .ok finalEnv ∧
      lookup finalEnv (nameAt names certificate.output) =
        some (laneValue (source.value (fun _ => input))) := by
  obtain ⟨hnames, hprogram, ⟨shapes, hvalid⟩, hsource⟩ :=
    checked_named_structure source certificate programName names program
      gates addresses hcheck
  have hcertificate :=
    (S31.Functional.SSANativeTopologyCheck.checkSourceRows_implies_certificate
      source certificate gates addresses hsource).1
  obtain ⟨finalEnv, hfold, hlookup⟩ :=
    checked_named_nodes_sound names source certificate input
      (name_table_distinct names certificate hnames) hcertificate
  have hprivateFields :
      exactFields assignment.privateInputs
        ((program.inputs.filter (fun i => i.visibility == .private)).map
          (·.name)) = true := by
    rw [hprogram, hprivate]
    have hpubprivate :
        (Visibility.«public» == Visibility.private) = false := by decide
    simp [encodeNamed, exactFields, hpubprivate]
  have hmap :
      program.inputs.mapM (fun i => do
        let raw := if i.visibility == Visibility.«public» then
          assignment.publicInputs else assignment.privateInputs
        return (i.name, ← assigned raw i.name i.shape)) =
        .ok [(nameAt names 0, laneValue input)] := by
    rw [hprogram]
    have hpublic :
        (Visibility.«public» == Visibility.«public») = true := by decide
    simp [encodeNamed, List.mapM, List.mapM.loop, hpublic, hinput]
  have hfoldProgram :
      program.nodes.foldlM
        (fun env node => do
          return env ++ [(node.name, ← evaluateNode env node)])
        [(nameAt names 0, laneValue input)] = .ok finalEnv := by
    rw [hprogram]
    exact hfold
  have hassertions : program.assertions = [] := by
    simp [hprogram, encodeNamed]
  refine ⟨finalEnv, ?_, hlookup⟩
  unfold Program.environment
  rw [hvalid]
  simp only [hprivateFields, hmap, hassertions]
  simpa [require, hfoldProgram] using hfoldProgram

private theorem value_beq_eq (a b : Value) (h : (a == b) = true) : a = b := by
  cases a with
  | mk ak aw =>
    cases b with
    | mk bk bw =>
      change instBEqValue.beq ⟨ak, aw⟩ ⟨bk, bw⟩ = true at h
      cases ak <;> cases bk
      · have hw : aw = bw := (beq_iff_eq).mp
          (by simpa [BEq.beq, instBEqValue.beq, instBEqKind.beq] using h)
        simp [hw]
      · simp only [instBEqValue.beq, BEq.beq, instBEqKind.beq,
          Bool.and_eq_true] at h
        cases h.1
      · simp only [instBEqValue.beq, BEq.beq, instBEqKind.beq,
          Bool.and_eq_true] at h
        cases h.1
      · have hw : aw = bw := (beq_iff_eq).mp
          (by simpa [BEq.beq, instBEqValue.beq, instBEqKind.beq] using h)
        simp [hw]

/-- Accepted normalized evaluation also fixes the public result value for
any checked user names. This is over real `Program.evaluate`, not a modeled
positional interpreter. -/
theorem checked_named_public_claim_sound (source : Source 1)
    (certificate : Certificate) (programName : String)
    (program : Program) (gates : List S31.Functional.SSANativeTopologyCheck.Gate)
    (addresses : List Nat) (assignment : Assignment) (input : Lanes)
    (hcheck : checkNamedSourceRows source certificate programName names
      program gates = some addresses)
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs (nameAt names 0) ⟨.m31, 4⟩ =
      .ok (laneValue input))
    (haccept : ∃ words, program.evaluate assignment = .ok words) :
    assigned assignment.publicOutputs (nameAt names certificate.output)
      ⟨.m31, 4⟩ =
      .ok (laneValue (source.value (fun _ => input))) := by
  obtain ⟨env, henv, houtput⟩ :=
    checked_named_environment_sound names source certificate programName
      program gates addresses assignment input hcheck hprivate hinput
  obtain ⟨words, haccept⟩ := haccept
  have hagree : program.outputsAgree assignment env = .ok () := by
    unfold Program.evaluate at haccept
    rw [henv] at haccept
    change (do
      let claimed ← program.claimedWords assignment
      program.outputsAgree assignment env
      pure claimed) = .ok words at haccept
    cases hclaimed : program.claimedWords assignment with
    | error err =>
        rw [hclaimed] at haccept
        change Except.error err = Except.ok words at haccept
        cases haccept
    | ok claim =>
        cases hout : program.outputsAgree assignment env with
        | error err =>
            rw [hclaimed, hout] at haccept
            change Except.error err = Except.ok words at haccept
            cases haccept
        | ok witness =>
            cases witness
            simpa using hout
  have hprogram := (checked_named_structure source certificate programName
    names program gates addresses hcheck).2.1
  rw [hprogram] at hagree
  unfold Program.outputsAgree at hagree
  simp only [encodeNamed, outputsAgreeNames, houtput] at hagree
  cases hassigned : assigned assignment.publicOutputs
      (nameAt names certificate.output)
      (laneValue (source.value (fun _ => input))).shape with
  | error err => simp [hassigned] at hagree
  | ok expected =>
      have heq : laneValue (source.value (fun _ => input)) = expected := by
        have hbeq :
            (laneValue (source.value (fun _ => input)) == expected) = true := by
          simpa [hassigned] using hagree
        exact value_beq_eq _ _ hbeq
      rw [← heq] at hassigned
      simpa [laneValue, Value.shape] using hassigned

/-- Once native addressed rows have been authenticated separately, their
selected result and the normalized public result agree with the source for
any accepted name table. The `AuthenticatedRows` premise is not discharged
by this theorem or by the package correspondence checker. -/
theorem checked_named_public_native_agree (source : Source 1)
    (certificate : Certificate) (programName : String)
    (program : Program) (rows : List Row)
    (addresses : List Nat) (values : List Lanes)
    (assignment : Assignment) (input claimed : Lanes)
    (hcheck : checkNamedSourceRows source certificate programName names
      program (rows.map Row.gate) = some addresses)
    (hauth : AuthenticatedRows [0] [input] rows addresses values)
    (hselected : values[certificate.output]? = some claimed)
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs (nameAt names 0) ⟨.m31, 4⟩ =
      .ok (laneValue input))
    (haccept : ∃ words, program.evaluate assignment = .ok words) :
    claimed = source.value (fun _ => input) ∧
    assigned assignment.publicOutputs (nameAt names certificate.output)
      ⟨.m31, 4⟩ = .ok (laneValue claimed) := by
  have hsource := checked_named_source_value source certificate programName
    names program input claimed rows addresses values hcheck hauth hselected
  constructor
  · exact hsource
  · rw [hsource]
    exact checked_named_public_claim_sound names source certificate
      programName program (rows.map Row.gate) addresses assignment input
      hcheck hprivate hinput haccept

/-- Executable positive control: a shared let is evaluated under user-chosen
names by the actual normalized environment. -/
def renamedSquareAssignment : Assignment :=
  { publicInputs := [("input", [2, 3, 4, 5])],
    publicOutputs := [("fourth", [16, 81, 256, 625])] }

theorem renamed_square_evaluates :
    renamedSquareProgram.evaluate renamedSquareAssignment =
      .ok ([2, 3, 4, 5, 16, 81, 256, 625].map
        RiscvRefinement.M31.reduce) := by decide

/-- Negative controls apply to the exact same source, names, and gate list:
an output substitution, a forward read, or a duplicate name is rejected. -/
theorem renamed_square_mutations_rejected :
    checkNamedSourceRows sharedSquare sharedSquareCertificate "pow4"
      ["input", "square", "fourth"]
      { renamedSquareProgram with outputs := ["square"] }
      sharedSquareGates = none ∧
    checkNamedSourceRows sharedSquare sharedSquareCertificate "pow4"
      ["input", "square", "fourth"]
      { renamedSquareProgram with nodes :=
        [{ name := "square", op := .mul, lhs := some "fourth",
           rhs := some "input" },
         { name := "fourth", op := .mul, lhs := some "square",
           rhs := some "square" }] }
      sharedSquareGates = none ∧
    checkNamedSourceRows sharedSquare sharedSquareCertificate "pow4"
      ["input", "square", "square"] renamedSquareProgram
      sharedSquareGates = none := by decide


end S31.Functional.SSAGeneralNamedExecution
