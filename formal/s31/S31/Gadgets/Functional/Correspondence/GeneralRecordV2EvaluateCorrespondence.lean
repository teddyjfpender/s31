import S31.Gadgets.Functional.Correspondence.GeneralRecordV2ValueCorrespondence

/-!
Run-time admission for the full bounded record-v2 value fragment. It checks
the public/private input partition against source-ordered canonical words,
then carries the resulting proof into the independent scalar-to-typed fold.
No native AIR or PCS witness is read here.
-/

namespace S31.Functional.Correspondence.GeneralRecordV2EvaluateCorrespondence

open GeneralRecordV2SourceCorrespondence
open GeneralRecordV2ValueCorrespondence

def scalarInputEnv (source : Source) (inputWords : List Nat) : S31.Env :=
  (List.zip (inputWires source) inputWords).map
    (fun (name, value) => (name, singleton value))

/-- Mapping canonical scalar input pairs to typed singleton inputs preserves
all named lookups, even before proving input names distinct. -/
theorem scalar_input_related (source : Source) (inputWords : List Nat) :
    GeneralRecordV2ValueCorrespondence.Related
      (List.zip (inputWires source) inputWords)
      (scalarInputEnv source inputWords) := by
  intro name
  simp [scalarInputEnv, S31.lookup, lookupValue,
    List.find?_map, Function.comp_def]

private def inputLoad (source : Source) (assignment : S31.Assignment) :
    S31.Result S31.Env :=
  (GeneralRecordV2ProgramAdmission.sourceProgram source).inputs.mapM
    (fun i => (i.name, ·) <$> S31.assigned
      (if i.visibility == S31.Visibility.public then assignment.publicInputs
       else assignment.privateInputs) i.name i.shape)

/-- The input part is checked without executing arithmetic nodes. A failure
means the caller's source-ordered words or public/private assignment disagree,
or a freshness condition is absent. Successful checks produce all premises
needed by the general node-fold theorem. -/
def checkInputAlignment (source : Source) (assignment : S31.Assignment)
    (inputWords : List Nat) : Bool :=
  S31.exactFields assignment.privateInputs
      (((GeneralRecordV2ProgramAdmission.sourceProgram source).inputs.filter
        (fun i => i.visibility == .private)).map (·.name)) &&
  decide (inputLoad source assignment =
    .ok (scalarInputEnv source inputWords)) &&
  decide (source.nodes.map Arithmetic.name).Nodup &&
  decide (∀ node ∈ source.nodes,
    S31.lookup (scalarInputEnv source inputWords) node.name = none)

theorem checked_input_alignment (source : Source)
    (assignment : S31.Assignment) (inputWords : List Nat)
    (h : checkInputAlignment source assignment inputWords = true) :
    InputAlignment source assignment inputWords
      (scalarInputEnv source inputWords) := by
  unfold checkInputAlignment at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, scalar_input_related source inputWords,
    h.1.2, h.2⟩

/-- The public output claim is checked against the *source* scalar result at
each distinct output wire. Aliased record fields contribute one normalized
public output claim. -/
def OutputClaims (source : Source) (values : List (String × Nat))
    (assignment : S31.Assignment) : Prop :=
  ∀ name ∈ (resultWires source).eraseDups,
    match lookupValue values name with
    | none => False
    | some word => S31.assigned assignment.publicOutputs name
        ⟨.m31, 1⟩ = .ok (singleton word)

def checkOutputClaims (source : Source) (values : List (String × Nat))
    (assignment : S31.Assignment) : Bool :=
  ((resultWires source).eraseDups).all fun name =>
    match lookupValue values name with
    | none => false
    | some word => decide (S31.assigned assignment.publicOutputs name
        ⟨.m31, 1⟩ = .ok (singleton word))

theorem checked_output_claims (source : Source)
    (values : List (String × Nat)) (assignment : S31.Assignment)
    (h : checkOutputClaims source values assignment = true) :
    OutputClaims source values assignment := by
  intro name hmem
  have hpoint := (List.all_eq_true.mp h) name hmem
  cases hword : lookupValue values name with
  | none => simp [hword] at hpoint
  | some word => simpa [hword] using hpoint

private theorem outputs_agree_of_source (names : List String)
    (values : List (String × Nat)) (env : S31.Env)
    (assignment : S31.Assignment)
    (hrelated : GeneralRecordV2ValueCorrespondence.Related values env)
    (hclaims : ∀ name ∈ names,
      match lookupValue values name with
      | none => False
      | some word => S31.assigned assignment.publicOutputs name
          ⟨.m31, 1⟩ = .ok (singleton word)) :
    S31.outputsAgreeNames assignment env names = .ok () := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      have hhead := hclaims name (by simp)
      cases hword : lookupValue values name with
      | none => simp [hword] at hhead
      | some word =>
          have hlookup := hrelated name
          rw [hword] at hlookup
          have hassign : S31.assigned assignment.publicOutputs name
              ⟨.m31, 1⟩ = .ok (singleton word) := by
            simpa [hword] using hhead
          have htail : ∀ next ∈ rest,
              match lookupValue values next with
              | none => False
              | some value => S31.assigned assignment.publicOutputs next
                  ⟨.m31, 1⟩ = .ok (singleton value) := by
            intro next hmem
            exact hclaims next (by simp [hmem])
          have hshape : (singleton word).shape = ⟨.m31, 1⟩ := rfl
          have hbeq : (singleton word == singleton word) = true := by
            change ((S31.Kind.m31 == S31.Kind.m31) &&
              ([RiscvRefinement.M31.reduce word] ==
                [RiscvRefinement.M31.reduce word])) = true
            simp
            rfl
          simpa [S31.outputsAgreeNames, hlookup, hshape, hassign, hbeq]
            using ih htail

/-- The complete normalized evaluator accepts the source result and returns
its canonical claimed public words. This theorem never assumes a successful
typed arithmetic run: that run follows from the scalar fold simulation and
the checked input/output partitions. -/
theorem source_fold_program_evaluate
    {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (accepted : GeneralRecordV2ProgramAdmission.Static
      sourceBytes treeBytes relationBytes abiBytes)
    (assignment : S31.Assignment) (inputWords : List Nat)
    (finalValues : List (String × Nat)) (claimed : List S31.M31)
    (hinput : checkInputAlignment accepted.checked.source assignment
      inputWords = true)
    (hfold : accepted.checked.source.nodes.foldlM evalNode
      (List.zip (inputWires accepted.checked.source) inputWords) =
        some finalValues)
    (houtput : checkOutputClaims accepted.checked.source finalValues
      assignment = true)
    (hclaimed : accepted.program.claimedWords assignment = .ok claimed) :
    accepted.program.evaluate assignment = .ok claimed := by
  let source := accepted.checked.source
  have haligned := checked_input_alignment source assignment inputWords hinput
  have hvalidated : ∃ shapes,
      (GeneralRecordV2ProgramAdmission.sourceProgram source).validate =
        .ok shapes := by
    rcases accepted.validated with ⟨shapes, hv⟩
    rw [accepted.aligned] at hv
    exact ⟨shapes, hv⟩
  obtain ⟨finalEnv, henv, hrelated⟩ :=
    source_nodes_program_environment source assignment inputWords
      (scalarInputEnv source inputWords) finalValues hvalidated
      haligned.privateExact haligned.loaded haligned.initialRelated
      haligned.namesUnique haligned.fresh hfold
  have hout :
      (GeneralRecordV2ProgramAdmission.sourceProgram source).outputsAgree
        assignment finalEnv = .ok () := by
    change S31.outputsAgreeNames assignment finalEnv
      ((resultWires source).eraseDups) = .ok ()
    exact outputs_agree_of_source ((resultWires source).eraseDups)
      finalValues finalEnv assignment hrelated
      (checked_output_claims source finalValues assignment houtput)
  rw [accepted.aligned] at hclaimed ⊢
  unfold S31.Program.evaluate
  rw [henv]
  dsimp [source] at hout
  simp [hclaimed, hout, Bind.bind, Except.bind,
    Pure.pure, Except.pure]

structure CheckedRun where
  sourceResults : List Nat
  claimed : List S31.M31
deriving Repr

/-- Executable general record-v2 value check. It reads the scalar source graph
and the canonical public claim decoder, but never calls `Program.environment`
or `Program.evaluate`. Both successful semantics follow from the theorem
below. -/
def checkSourceRun
    {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (accepted : GeneralRecordV2ProgramAdmission.Static
      sourceBytes treeBytes relationBytes abiBytes)
    (assignment : S31.Assignment) (inputWords : List Nat) :
    Option CheckedRun :=
  let source := accepted.checked.source
  if checkInputAlignment source assignment inputWords = true then
    if inputWords.length = (inputWires source).length ∧
        ∀ word ∈ inputWords, word < S31.modulus then
      match source.nodes.foldlM evalNode
          (List.zip (inputWires source) inputWords) with
      | none => none
      | some finalValues =>
          match (resultWires source).mapM (lookupValue finalValues) with
          | none => none
          | some results =>
              if checkOutputClaims source finalValues assignment = true then
                match accepted.program.claimedWords assignment with
                | .error _ => none
                | .ok claimed => some ⟨results, claimed⟩
              else none
    else none
  else none

/-- A successful source-only run proves both the ordered source record and
the actual normalized typed public claim. The native AIR join is separate. -/
theorem checked_source_run_evaluate
    {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (accepted : GeneralRecordV2ProgramAdmission.Static
      sourceBytes treeBytes relationBytes abiBytes)
    (assignment : S31.Assignment) (inputWords : List Nat)
    (run : CheckedRun)
    (h : checkSourceRun accepted assignment inputWords = some run) :
    evaluate accepted.checked.source inputWords = some run.sourceResults ∧
    accepted.program.evaluate assignment = .ok run.claimed := by
  let source := accepted.checked.source
  by_cases hinput : checkInputAlignment source assignment inputWords = true
  · by_cases hcanonical : inputWords.length = (inputWires source).length ∧
        ∀ word ∈ inputWords, word < S31.modulus
    · cases hfold : source.nodes.foldlM evalNode
          (List.zip (inputWires source) inputWords) with
      | none => simp [checkSourceRun, source, hinput, hcanonical, hfold] at h
      | some finalValues =>
          cases hresult : (resultWires source).mapM
              (lookupValue finalValues) with
          | none =>
              simp [checkSourceRun, source, hinput, hcanonical, hfold, hresult] at h
          | some results =>
              by_cases houtput : checkOutputClaims source finalValues
                  assignment = true
              · cases hclaim : accepted.program.claimedWords assignment with
                | error err =>
                    simp [checkSourceRun, source, hinput, hcanonical, hfold,
                      hresult, houtput, hclaim] at h
                | ok claimed =>
                    have heq : (⟨results, claimed⟩ : CheckedRun) = run := by
                      have hparts := h
                      simp [checkSourceRun, source, hinput, hcanonical,
                        hfold, hresult, houtput, hclaim] at hparts
                      exact hparts.2
                    cases heq
                    constructor
                    · simp [evaluate, source, hcanonical.1,
                        hfold, hresult]
                      exact hcanonical.2
                    · exact source_fold_program_evaluate accepted assignment
                        inputWords finalValues claimed hinput hfold houtput hclaim
              · simp [checkSourceRun, source, hinput, hcanonical, hfold,
                  hresult, houtput] at h
    · simp [checkSourceRun, source, hinput, hcanonical] at h
  · simp [checkSourceRun, source, hinput] at h

/-- Read source-ordered one-word inputs directly from the assignment's public
and private partitions. The subsequent `checkSourceRun` verifies this list
against the independently reconstructed source input names. -/
def inputWordsFromAssignment (source : Source) (assignment : S31.Assignment) :
    Option (List Nat) :=
  (GeneralRecordV2ProgramAdmission.sourceProgram source).inputs.mapM fun i => do
    let raw := if i.visibility == .public then assignment.publicInputs
      else assignment.privateInputs
    let words ← S31.lookup raw i.name
    match words with
    | [word] => if word < S31.modulus then some word else none
    | _ => none

def checkSourceAssignment
    {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (accepted : GeneralRecordV2ProgramAdmission.Static
      sourceBytes treeBytes relationBytes abiBytes)
    (assignment : S31.Assignment) : Option CheckedRun := do
  let inputWords ← inputWordsFromAssignment accepted.checked.source assignment
  checkSourceRun accepted assignment inputWords

theorem checked_source_assignment_evaluate
    {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (accepted : GeneralRecordV2ProgramAdmission.Static
      sourceBytes treeBytes relationBytes abiBytes)
    (assignment : S31.Assignment) (run : CheckedRun)
    (h : checkSourceAssignment accepted assignment = some run) :
    ∃ inputWords,
      inputWordsFromAssignment accepted.checked.source assignment =
        some inputWords ∧
      evaluate accepted.checked.source inputWords =
        some run.sourceResults ∧
      accepted.program.evaluate assignment = .ok run.claimed := by
  unfold checkSourceAssignment at h
  cases hwords : inputWordsFromAssignment accepted.checked.source assignment with
  | none => simp [hwords] at h
  | some inputWords =>
      have hrun : checkSourceRun accepted assignment inputWords =
          some run := by simpa [hwords] using h
      obtain ⟨hsource, htyped⟩ := checked_source_run_evaluate
        accepted assignment inputWords run hrun
      exact ⟨inputWords, rfl, hsource, htyped⟩

/-! Two public fields, two private fields, and an aliased result. The private
fields are loaded but not copied into the public claim. -/

private def exampleSource :=
  GeneralRecordV2ValueCorrespondence.workedSource

private def exampleAssignment :=
  GeneralRecordV2ValueCorrespondence.workedAssignment

theorem worked_input_alignment_check :
    checkInputAlignment exampleSource exampleAssignment [2, 3, 4, 5] =
      true := by decide

theorem worked_assignment_input_order :
    inputWordsFromAssignment exampleSource exampleAssignment =
      some [2, 3, 4, 5] := by decide

theorem worked_output_alignment_check :
    checkOutputClaims exampleSource
      (("product", 18) :: ("sum", 6) ::
        List.zip (inputWires exampleSource) [2, 3, 4, 5])
      exampleAssignment = true := by decide

private def aliasSource : Source :=
  { exampleSource with
    result := [
      ⟨"left", ⟨"product", Lean.Json.null⟩⟩,
      ⟨"right", ⟨"product", Lean.Json.null⟩⟩] }

private def aliasAssignment : S31.Assignment :=
  { exampleAssignment with publicOutputs := [("product", [18])] }

theorem alias_source_result_repeats :
    evaluate aliasSource [2, 3, 4, 5] = some [18, 18] := by decide

theorem alias_public_claim_deduplicates :
    (GeneralRecordV2ProgramAdmission.sourceProgram aliasSource).evaluate
      aliasAssignment = .ok
        ([2, 3, 18, 0, 0, 0, 0, 0].map RiscvRefinement.M31.reduce) := by
  decide

theorem alias_input_alignment_check :
    checkInputAlignment aliasSource aliasAssignment [2, 3, 4, 5] =
      true := by decide

theorem alias_assignment_input_order :
    inputWordsFromAssignment aliasSource aliasAssignment =
      some [2, 3, 4, 5] := by decide

theorem alias_output_alignment_check :
    checkOutputClaims aliasSource
      (("product", 18) :: ("sum", 6) ::
        List.zip (inputWires aliasSource) [2, 3, 4, 5])
      aliasAssignment = true := by decide

theorem wrong_private_mapping_rejected :
    checkInputAlignment exampleSource exampleAssignment [2, 3, 5, 4] =
      false := by decide

theorem inconsistent_alias_claim_rejected :
    (GeneralRecordV2ProgramAdmission.sourceProgram aliasSource).claimedWords
      { aliasAssignment with publicOutputs :=
        [("product", [18]), ("sum", [6])] } =
      .error .publicMismatch := by decide

end S31.Functional.Correspondence.GeneralRecordV2EvaluateCorrespondence
