import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAProgramEvaluate

/-!
Executable finite admission for the initial named environment of the pure
SSA interpreter bridge. This checks the exact typed `Assignment` and all
indexed input/future-name lookups. Connecting canonical assignment JSON bytes
to this typed assignment remains a separate parser correspondence step.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAInputState

open S31.Functional.Correspondence
open GeneralLinearSSAProgramEvaluate

private def assignedInput (assignment : S31.Assignment)
    (input : S31.Input) : S31.Result (String × S31.Value) := do
  let raw := if input.visibility == S31.Visibility.«public» then
    assignment.publicInputs else assignment.privateInputs
  return (input.name, ← S31.assigned raw input.name input.shape)

def checkInputState {n : Nat} (program : S31.Program)
    (assignment : S31.Assignment) (names : List String)
    (certificate : GeneralLinearSSA.Certificate)
    (values : Nat → Lanes n) : Option S31.Env :=
  match program.inputs.mapM (assignedInput assignment) with
  | .error _ => none
  | .ok inputEnv =>
      let initial := GeneralLinearSSA.initialValues certificate.inputs values
      let privateOK := S31.exactFields assignment.privateInputs
        ((program.inputs.filter (fun i => i.visibility == .private)).map
          (·.name))
      let carriesOK := (List.range initial.length).all fun id =>
        match initial[id]? with
        | none => false
        | some value => decide (S31.lookup inputEnv (nameAt names id) =
            some (laneValue value))
      let absentOK := (List.range certificate.instructions.length).all
        fun offset => decide (S31.lookup inputEnv
          (nameAt names (initial.length + offset)) = none)
      if privateOK && carriesOK && absentOK then some inputEnv else none

/-- This executable finite checker discharges every initial-state premise
used by the general normalized interpreter induction. It compares neither
the final interpreter value nor the source term's final value. -/
theorem checked_input_state {n : Nat} (program : S31.Program)
    (assignment : S31.Assignment) (names : List String)
    (certificate : GeneralLinearSSA.Certificate)
    (values : Nat → Lanes n) (inputEnv : S31.Env)
    (hcheck : checkInputState program assignment names certificate values =
      some inputEnv) :
    S31.exactFields assignment.privateInputs
      ((program.inputs.filter (fun i => i.visibility == .private)).map
        (·.name)) = true ∧
    program.inputs.mapM (fun (i : S31.Input) => do
      let raw := if i.visibility == S31.Visibility.«public» then
        assignment.publicInputs else assignment.privateInputs
      return (i.name, ← S31.assigned raw i.name i.shape)) = .ok inputEnv ∧
    Carries names inputEnv
      (GeneralLinearSSA.initialValues certificate.inputs values) ∧
    Absent names inputEnv
      (GeneralLinearSSA.initialValues certificate.inputs values).length
      ((GeneralLinearSSA.initialValues certificate.inputs values).length +
        certificate.instructions.length) := by
  unfold checkInputState at hcheck
  cases hmap : program.inputs.mapM (assignedInput assignment) with
  | error err => simp [hmap] at hcheck
  | ok env =>
      let initial := GeneralLinearSSA.initialValues certificate.inputs values
      let privateOK := S31.exactFields assignment.privateInputs
        ((program.inputs.filter (fun i => i.visibility == .private)).map
          (·.name))
      let carriesOK := (List.range initial.length).all fun id =>
        match initial[id]? with
        | none => false
        | some value => decide (S31.lookup env (nameAt names id) =
            some (laneValue value))
      let absentOK := (List.range certificate.instructions.length).all
        fun offset => decide (S31.lookup env
          (nameAt names (initial.length + offset)) = none)
      simp [hmap] at hcheck
      have henv : env = inputEnv := hcheck.2
      subst env
      refine ⟨hcheck.1.1.1, ?_, ?_, ?_⟩
      · simpa [assignedInput] using hmap
      · intro id value hfound
        change initial[id]? = some value at hfound
        have hid : id < initial.length :=
          (List.getElem?_eq_some_iff.mp hfound).1
        have hpoint : (match initial[id]? with
            | none => false
            | some actual => decide (S31.lookup inputEnv
                (nameAt names id) = some (laneValue actual))) = true :=
          hcheck.1.1.2 id hid
        rw [hfound] at hpoint
        exact of_decide_eq_true hpoint
      · intro id hnext hmax
        change initial.length ≤ id at hnext
        change id < initial.length + certificate.instructions.length at hmax
        have hoffset : id - initial.length < certificate.instructions.length := by
          omega
        have hpoint : decide (S31.lookup inputEnv
            (nameAt names (initial.length + (id - initial.length))) = none) =
              true := by
          simpa using hcheck.1.2 (id - initial.length) hoffset
        have hid : initial.length + (id - initial.length) = id := by omega
        rw [hid] at hpoint
        exact of_decide_eq_true hpoint

/-- The source/graph and finite input-state gates imply the interpreter's
selected public output for arbitrary field assignments. -/
theorem checked_pure_source_program_evaluate_with_state_check {n : Nat}
    (sourceBytes : List Nat) (certificateBytes relationBytes : String)
    (ssa : GeneralLinearSSA.EmittedSSA)
    (meaning : GeneralLinearSSA.Term)
    (certificate : GeneralLinearSSA.Certificate)
    (program : S31.Program) (assignment : S31.Assignment)
    (inputEnv : S31.Env) (values : Nat → Lanes n)
    (words : List S31.M31)
    (hsource : GeneralLinearSSASourceBytes.checkSourceCertificate
      sourceBytes certificateBytes = .ok (ssa, meaning, certificate))
    (hrelation : GeneralLinearSSAPublicABI.checkPureSourceRelationSSA
      sourceBytes relationBytes ssa = .ok program)
    (halign : checkPureAlignment ssa certificate = true)
    (hstate : checkInputState program assignment ssa.names certificate values =
      some inputEnv)
    (haccept : program.evaluate assignment = .ok words) :
    GeneralLinearSSASourceBytes.denotation sourceBytes values =
      some (meaning.eval values) ∧
    ∃ outputName,
      ssa.names[ssa.output]? = some outputName ∧
      GeneralLinearSSAPublicABI.expectedPureNodes ssa = some program.nodes ∧
      S31.assigned assignment.publicOutputs outputName ⟨.m31, n⟩ =
        .ok (laneValue (meaning.eval values)) := by
  obtain ⟨hprivate, hinputs, hcarries, habent⟩ :=
    checked_input_state program assignment ssa.names certificate values
      inputEnv hstate
  exact checked_pure_source_program_evaluate sourceBytes certificateBytes
    relationBytes ssa meaning certificate program assignment inputEnv
    values words hsource hrelation halign hprivate hinputs hcarries habent
    haccept

private def sampleProgram : S31.Program :=
  { name := "subtraction_twice",
    inputs := [
      { name := "a", shape := ⟨.m31, 1⟩, visibility := .private },
      { name := "b", shape := ⟨.m31, 1⟩, visibility := .private }],
    nodes := [], assertions := [], outputs := [] }

private def sampleAssignment : S31.Assignment :=
  { publicInputs := [], privateInputs := [("a", [3]), ("b", [2])],
    publicOutputs := [] }

private def sampleValues : Nat → Lanes 1 :=
  fun id _ => RiscvRefinement.M31.reduce (if id == 0 then 3 else 2)

private def sampleNames : List String :=
  ["a", "b", "delta", "doubled"]

theorem input_state_positive :
    (checkInputState sampleProgram sampleAssignment sampleNames
      GeneralLinearSSA.subtractionThenDouble sampleValues).isSome = true := by
  decide

theorem input_state_wrong_value_rejected :
    checkInputState sampleProgram
      { sampleAssignment with privateInputs := [("a", [3]), ("b", [7])] }
      sampleNames GeneralLinearSSA.subtractionThenDouble sampleValues = none := by
  decide

theorem input_state_future_name_rejected :
    checkInputState sampleProgram sampleAssignment
      ["a", "b", "a", "doubled"]
      GeneralLinearSSA.subtractionThenDouble sampleValues = none := by
  decide

theorem input_state_missing_input_rejected :
    checkInputState sampleProgram
      { sampleAssignment with privateInputs := [("a", [3])] }
      sampleNames GeneralLinearSSA.subtractionThenDouble sampleValues = none := by
  decide

end S31.Functional.Correspondence.GeneralLinearSSAInputState
