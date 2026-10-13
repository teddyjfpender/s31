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
  publicBytes : List Nat

/-- The ordinary version-1 public statement is canonical JSON with exactly
public inputs and outputs. Its parsed values must be the same ones in the
typed assignment, and its eight M31 words are encoded inside Lean. The
native verifier must subsequently consume these *same statement bytes*; this
checker alone does not authenticate that native consumption. -/
def checkRunStatement (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes
      statementBytes : String) : Check StatementRun := do
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
  let run ← checkRun sourceBytes certificateBytes relationBytes abiBytes
    assignmentBytes publicBytes
  return ⟨run, publicBytes⟩

end S31.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck
