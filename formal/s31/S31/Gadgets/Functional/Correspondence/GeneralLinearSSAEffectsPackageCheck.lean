import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsByteRun

/-!
Operational admission for the bounded effectful source grammar. Static
package checks do not need a witness; dynamic checks derive all indexed M31
values and the output claim from the same typed assignment bytes supplied to
the exact-byte theorem. Caller-supplied values cannot bypass this gate.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck

open S31.Functional.Correspondence
open GeneralLinearSSAPublicABI
open GeneralLinearSSAEffectsByteRun

abbrev Check := Except String

structure StaticPackage where
  ssa : GeneralLinearSSAEffects.EmittedSSA
  meaning : GeneralLinearSSAEffects.Source
  certificate : GeneralLinearSSAEffects.Certificate
  program : S31.Program
  outputName : String
  leanAbi : String

/-- The generic Gate package has the same v1 M31 field layout but uses a
different, less specific encoding label from direct Gate packages. Admit only
these two exact descriptors. The existing byte-run theorem consumes the
canonical-label rendering, so the generic label is replaced only after its
original bytes and every field have been checked. -/
private def checkPackageAbi (bytes : String) (laneCount : Nat)
    (inputs : List GeneralLinearSSA.EmittedInput)
    (outputName : String) : Check String := do
  let found ← parseDescriptor bytes
  let expected := expectedDescriptor laneCount inputs outputName
  if found = expected then return bytes
  let generic := { expected with
    encoding := "eight little-endian u32 words; unused words are zero" }
  if found = generic then
    let normalized := bytes.replace generic.encoding expected.encoding
    checkDescriptor normalized laneCount inputs outputName
    return normalized
  throw "public ABI differs from source-derived SSA layout"

/-- Exact source, certificate, normalized relation, and public ABI bytes.
This does not assert satisfiability of source assertions. -/
def checkStatic (sourceBytes : List Nat) (certificateBytes relationBytes
    abiBytes : String) : Check StaticPackage := do
  let (ssa, meaning, certificate) ←
    GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate sourceBytes
      certificateBytes
  let program ← checkEffectsSourceRelationSSA sourceBytes relationBytes ssa
  if !checkEffectsAlignment ssa certificate then
    throw "effects SSA alignment differs"
  let outputName ← match ssa.names[ssa.output]? with
    | none => throw "selected output name missing"
    | some name => pure name
  let leanAbi ← checkPackageAbi abiBytes ssa.lane_count ssa.inputs outputName
  return ⟨ssa, meaning, certificate, program, outputName, leanAbi⟩

private def rawLanes (raw : S31.RawValues) (name : String) (n : Nat) :
    Check (GeneralLinearSSA.Lanes n) := do
  let words ← match S31.lookup raw name with
    | none => throw s!"assignment input {name} missing"
    | some words => pure words
  if words.length != n || !words.all (· < S31.modulus) then
    throw s!"assignment input {name} is not a canonical M31 array"
  return fun i => RiscvRefinement.M31.reduce (words[i.val]?.getD 0)

private def inputLanes (assignment : S31.Assignment)
    (input : GeneralLinearSSA.EmittedInput) (n : Nat) :
    Check (Nat × GeneralLinearSSA.Lanes n) := do
  let raw := if input.visibility == "public" then
    assignment.publicInputs else assignment.privateInputs
  return (input.id, ← rawLanes raw input.name n)

private def indexedValues {n : Nat}
    (values : List (Nat × GeneralLinearSSA.Lanes n))
    (id : Nat) : GeneralLinearSSA.Lanes n :=
  match values.find? (fun pair => pair.1 == id) with
  | none => fun _ => 0
  | some pair => pair.2

/-- This is the theorem-backed dynamic gate from exact package bytes to the
actual interpreter. It derives inputs and public claim internally from the
canonical typed assignment and then lets the full byte-run checker bind
those values to the independent ABI and public statement. -/
def checkRun (sourceBytes : List Nat) (certificateBytes relationBytes
    abiBytes assignmentBytes : String) (rawPublicBytes : List Nat) :
    Check EffectsByteRun := do
  let static ← checkStatic sourceBytes certificateBytes relationBytes abiBytes
  let assignment ← GeneralLinearSSAByteRun.parseTypedAssignment assignmentBytes
  let inputValues ← static.ssa.inputs.mapM
    (fun input => inputLanes assignment input static.ssa.lane_count)
  let claimed ← rawLanes assignment.publicOutputs static.outputName
    static.ssa.lane_count
  checkEffectsByteRun sourceBytes certificateBytes relationBytes static.leanAbi
    assignmentBytes rawPublicBytes (indexedValues inputValues) claimed

/-- Successful generic runtime admission inherits the exact-byte semantic
theorem, with values and claim derived internally from typed assignment bytes.
The existential witnesses are the actual checked field values, not an
unchecked caller-supplied interpretation of the assignment. -/
theorem checked_run_sound (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (run : EffectsByteRun)
    (hcheck : checkRun sourceBytes certificateBytes relationBytes abiBytes
      assignmentBytes rawPublicBytes = .ok run) :
    ∃ (n : Nat) (values : Nat → GeneralLinearSSA.Lanes n)
      (claimed : GeneralLinearSSA.Lanes n),
      GeneralLinearSSAEffectsSourceBytes.denotation sourceBytes values claimed ∧
      rawPublicBytes = publicWordBytes
        (orderedPublicWords run.ssa.inputs values claimed) ∧
      GeneralLinearSSAByteRun.parseTypedAssignment assignmentBytes =
        .ok run.assignment ∧
      run.program.evaluate run.assignment = .ok run.words := by
  unfold checkRun at hcheck
  cases hstatic : checkStatic sourceBytes certificateBytes relationBytes abiBytes with
  | error err => simp [hstatic, Bind.bind, Except.bind] at hcheck
  | ok static =>
      cases hassignment : GeneralLinearSSAByteRun.parseTypedAssignment
          assignmentBytes with
      | error err =>
          simp [hstatic, hassignment, Bind.bind, Except.bind] at hcheck
      | ok assignment =>
          cases hinputs : static.ssa.inputs.mapM
              (fun input => inputLanes assignment input static.ssa.lane_count) with
          | error err =>
              simp [hstatic, hassignment, hinputs,
                Bind.bind, Except.bind] at hcheck
          | ok inputValues =>
              cases hclaimed : rawLanes assignment.publicOutputs
                  static.outputName static.ssa.lane_count with
              | error err =>
                  simp [hstatic, hassignment, hinputs, hclaimed,
                    Bind.bind, Except.bind] at hcheck
              | ok claimed =>
                  have hrun : checkEffectsByteRun sourceBytes certificateBytes
                      relationBytes static.leanAbi assignmentBytes rawPublicBytes
                      (indexedValues inputValues) claimed = .ok run := by
                    simpa [hstatic, hassignment, hinputs, hclaimed,
                      Bind.bind, Except.bind, Pure.pure, Except.pure]
                      using hcheck
                  refine ⟨static.ssa.lane_count, indexedValues inputValues,
                    claimed, ?_⟩
                  simpa [hassignment] using
                    checked_effects_byte_run sourceBytes certificateBytes
                      relationBytes static.leanAbi assignmentBytes rawPublicBytes
                      (indexedValues inputValues) claimed run hrun

structure StatementRun where
  run : EffectsByteRun
  statement : S31.Assignment
  publicBytes : List Nat

private structure StatementPrefix where
  assignment : S31.Assignment
  statement : S31.Assignment
  publicBytes : List Nat

/-- The ordinary version-1 public statement is canonical JSON with exactly
public inputs and outputs. Its parsed values must be the same ones in the
typed assignment, and its eight M31 words are encoded inside Lean. The
native verifier must subsequently consume these *same statement bytes*; this
checker alone does not authenticate that native consumption. -/
private def checkStatementPrefix (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes
      statementBytes : String) : Check StatementPrefix := do
  let static ← checkStatic sourceBytes certificateBytes relationBytes abiBytes
  let assignment ← GeneralLinearSSAByteRun.parseTypedAssignment assignmentBytes
  let statement ← GeneralLinearSSAByteRun.parseTypedAssignment statementBytes
  let statementJson ← Lean.Json.parse statementBytes
  if (statementJson.getObjVal? "private_inputs").isOk then
    throw "public statement contains private inputs"
  if statement.publicInputs != assignment.publicInputs ||
      statement.publicOutputs != assignment.publicOutputs then
    throw "public statement differs from typed assignment"
  let words ← match static.program.claimedWords assignment with
    | .error _ => throw "normalized program rejects claimed public words"
    | .ok words => pure words
  let publicBytes := publicWordBytes words
  return ⟨assignment, statement, publicBytes⟩

private theorem checked_statement_prefix (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes
      statementBytes : String) (checkedPrefix : StatementPrefix)
    (hcheck : checkStatementPrefix sourceBytes certificateBytes relationBytes
      abiBytes assignmentBytes statementBytes = .ok checkedPrefix) :
    GeneralLinearSSAByteRun.parseTypedAssignment assignmentBytes =
      .ok checkedPrefix.assignment ∧
    GeneralLinearSSAByteRun.parseTypedAssignment statementBytes =
      .ok checkedPrefix.statement ∧
    checkedPrefix.statement.publicInputs = checkedPrefix.assignment.publicInputs ∧
    checkedPrefix.statement.publicOutputs = checkedPrefix.assignment.publicOutputs := by
  unfold checkStatementPrefix at hcheck
  cases hstatic : checkStatic sourceBytes certificateBytes relationBytes abiBytes with
  | error error => simp [hstatic, Bind.bind, Except.bind,
      Pure.pure, Except.pure] at hcheck
  | ok static =>
      cases hassign : GeneralLinearSSAByteRun.parseTypedAssignment assignmentBytes with
      | error error => simp [hstatic, hassign, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at hcheck
      | ok assignment =>
          cases hstatement : GeneralLinearSSAByteRun.parseTypedAssignment statementBytes with
          | error error =>
              simp [hstatic, hassign, hstatement, Bind.bind, Except.bind,
                Pure.pure, Except.pure] at hcheck
          | ok statement =>
              cases hjson : Lean.Json.parse statementBytes with
              | error error =>
                  simp [hstatic, hassign, hstatement, hjson,
                    Bind.bind, Except.bind, Pure.pure, Except.pure] at hcheck
              | ok statementJson =>
                  by_cases hprivate : (statementJson.getObjVal? "private_inputs").isOk = true
                  · simp [hstatic, hassign, hstatement, hjson, hprivate,
                      Bind.bind, Except.bind, Pure.pure, Except.pure] at hcheck
                  · by_cases hdiff :
                      (statement.publicInputs != assignment.publicInputs ||
                        statement.publicOutputs != assignment.publicOutputs) = true
                    · simp [hstatic, hassign, hstatement, hjson, hprivate,
                        hdiff, Bind.bind, Except.bind, Pure.pure,
                        Except.pure] at hcheck
                    · cases hwords : static.program.claimedWords assignment with
                      | error error =>
                          simp [hstatic, hassign, hstatement, hjson,
                            hprivate, hdiff, hwords, Bind.bind, Except.bind,
                            Pure.pure, Except.pure] at hcheck
                      | ok words =>
                          have hprefixEq : checkedPrefix =
                              ⟨assignment, statement, publicWordBytes words⟩ := by
                            have heq : ((.ok
                                (⟨assignment, statement, publicWordBytes words⟩ :
                                  StatementPrefix)) : Check StatementPrefix) =
                                .ok checkedPrefix := by
                              simpa [hstatic, hassign, hstatement, hjson,
                                hprivate, hdiff, hwords, Bind.bind, Except.bind,
                                Pure.pure, Except.pure] using hcheck
                            injection heq with hvalue
                            exact hvalue.symm
                          subst checkedPrefix
                          have hfields : statement.publicInputs = assignment.publicInputs ∧
                              statement.publicOutputs = assignment.publicOutputs := by
                            simpa using hdiff
                          exact ⟨rfl, rfl, hfields.1, hfields.2⟩

def checkRunStatement (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes
      statementBytes : String) : Check StatementRun := do
  let checkedPrefix ← checkStatementPrefix sourceBytes certificateBytes relationBytes
    abiBytes assignmentBytes statementBytes
  let run ← checkRun sourceBytes certificateBytes relationBytes abiBytes
    assignmentBytes checkedPrefix.publicBytes
  return ⟨run, checkedPrefix.statement, checkedPrefix.publicBytes⟩

/-- The deployed statement entry point cannot report success without the
theorem-backed dynamic gate succeeding on the very public bytes it returns. -/
theorem checked_statement_projects (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes
      statementBytes : String) (result : StatementRun)
    (hcheck : checkRunStatement sourceBytes certificateBytes relationBytes
      abiBytes assignmentBytes statementBytes = .ok result) :
    checkRun sourceBytes certificateBytes relationBytes abiBytes
      assignmentBytes result.publicBytes = .ok result.run := by
  unfold checkRunStatement at hcheck
  cases hprefix : checkStatementPrefix sourceBytes certificateBytes
      relationBytes abiBytes assignmentBytes statementBytes with
  | error error =>
      simp [hprefix, Bind.bind, Except.bind] at hcheck
  | ok checkedPrefix =>
      cases hrun : checkRun sourceBytes certificateBytes relationBytes
          abiBytes assignmentBytes checkedPrefix.publicBytes with
      | error error =>
          simp [hprefix, hrun, Bind.bind, Except.bind] at hcheck
      | ok run =>
          have heq : (⟨run, checkedPrefix.statement, checkedPrefix.publicBytes⟩ :
              StatementRun) = result := by
            simpa [hprefix, hrun, Bind.bind, Except.bind, Pure.pure,
              Except.pure] using hcheck
          cases heq
          exact hrun

/-- Successful production statement admission inherits the arbitrary-input
effectful source/interpreter theorem and exact ordered public-word bytes. -/
theorem checked_statement_sound (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes
      statementBytes : String) (result : StatementRun)
    (hcheck : checkRunStatement sourceBytes certificateBytes relationBytes
      abiBytes assignmentBytes statementBytes = .ok result) :
    ∃ (n : Nat) (values : Nat → GeneralLinearSSA.Lanes n)
      (claimed : GeneralLinearSSA.Lanes n),
      GeneralLinearSSAEffectsSourceBytes.denotation sourceBytes values claimed ∧
      result.publicBytes = publicWordBytes
        (orderedPublicWords result.run.ssa.inputs values claimed) ∧
      GeneralLinearSSAByteRun.parseTypedAssignment assignmentBytes =
        .ok result.run.assignment ∧
      result.run.program.evaluate result.run.assignment =
        .ok result.run.words :=
  checked_run_sound sourceBytes certificateBytes relationBytes abiBytes
    assignmentBytes result.publicBytes result.run
    (checked_statement_projects sourceBytes certificateBytes relationBytes
      abiBytes assignmentBytes statementBytes result hcheck)

/-- The parsed public statement has exactly the same named public input and
output arrays as the assignment that the normalized interpreter accepted. -/
theorem checked_statement_fields (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes
      statementBytes : String) (result : StatementRun)
    (hcheck : checkRunStatement sourceBytes certificateBytes relationBytes
      abiBytes assignmentBytes statementBytes = .ok result) :
    GeneralLinearSSAByteRun.parseTypedAssignment statementBytes =
      .ok result.statement ∧
    result.statement.publicInputs = result.run.assignment.publicInputs ∧
    result.statement.publicOutputs = result.run.assignment.publicOutputs := by
  unfold checkRunStatement at hcheck
  cases hprefix : checkStatementPrefix sourceBytes certificateBytes
      relationBytes abiBytes assignmentBytes statementBytes with
  | error error =>
      simp [hprefix, Bind.bind, Except.bind] at hcheck
  | ok checkedPrefix =>
      cases hrun : checkRun sourceBytes certificateBytes relationBytes
          abiBytes assignmentBytes checkedPrefix.publicBytes with
      | error error =>
          simp [hprefix, hrun, Bind.bind, Except.bind] at hcheck
      | ok run =>
          have heq : (⟨run, checkedPrefix.statement,
              checkedPrefix.publicBytes⟩ : StatementRun) = result := by
            simpa [hprefix, hrun, Bind.bind, Except.bind, Pure.pure,
              Except.pure] using hcheck
          cases heq
          obtain ⟨hassignment, hstatement, hinputs, houtputs⟩ :=
            checked_statement_prefix sourceBytes certificateBytes relationBytes
              abiBytes assignmentBytes statementBytes checkedPrefix hprefix
          obtain ⟨_, _, _, _, _, hrunAssignment, _⟩ :=
            checked_run_sound sourceBytes certificateBytes relationBytes
              abiBytes assignmentBytes checkedPrefix.publicBytes run hrun
          rw [hassignment] at hrunAssignment
          have hsame : checkedPrefix.assignment = run.assignment := by
            injection hrunAssignment with hvalue
          exact ⟨hstatement, hinputs.trans (congrArg S31.Assignment.publicInputs hsame),
            houtputs.trans (congrArg S31.Assignment.publicOutputs hsame)⟩

end S31.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck
