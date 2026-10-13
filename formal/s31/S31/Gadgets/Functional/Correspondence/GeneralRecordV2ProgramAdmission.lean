import S31.Gadgets.Functional.Correspondence.GeneralRecordV2SourceCorrespondence
import S31.Semantics.Json

/-!
The bounded record-v2 source fragment is erased to the *actual* normalized
`S31.Program` evaluator. The source checker has already reconstructed every
relation field from exact source bytes. Here the v2 public record metadata is
removed only after that check; the remaining core is decoded with the same
typed Lean `S31.Json.program` parser used for v1 relations. The core must
equal a `Program` constructed independently from the parsed record source.

The static theorem is for every assignment to that checked program. The
statement theorem below is deliberately narrower: a one-field, one-public-
root, one-node record has no private witness, so its typed assignment is
derived entirely from the public statement bytes. Other record shapes do
not enter this proof admission.
-/

namespace S31.Functional.Correspondence.GeneralRecordV2ProgramAdmission

open Lean
open GeneralRecordV2SourceCorrespondence
open GeneralLinearSSABytes (Parse pythonCanonical fields field string nat array digest)

private def visibility (name : String) : S31.Visibility :=
  if name == "public" then .public else .private

def sourceProgram (source : Source) : S31.Program :=
  let inputs := (source.roots.zipIdx).flatMap fun (root, rootIndex) =>
    (source.fields.zipIdx).map fun (_, fieldIndex) =>
      ({ name := s!"_s31_abi_input_{rootIndex * source.fields.length + fieldIndex}",
         shape := ⟨.m31, 1⟩,
         visibility := visibility root.visibility } : S31.Input)
  let nodes := source.nodes.map fun node =>
    ({ name := node.name,
       op := if node.op == "+" then .add else .mul,
       lhs := some node.lhs.wire, rhs := some node.rhs.wire } : S31.Node)
  { version := 1, name := source.circuit, proofMode := .transparent,
    inputs, nodes, assertions := [], outputs := (resultWires source).eraseDups }

private def coreRelation (full : Json) : Parse Json := do
  fields full ["version", "name", "inputs", "nodes", "assertions",
    "public_outputs", "public_abi"]
  let version ← nat (← field full "version")
  if version != 2 then throw "record relation is not version 2"
  return Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("name", ← field full "name"),
    ("inputs", ← field full "inputs"),
    ("nodes", ← field full "nodes"),
    ("assertions", ← field full "assertions"),
    ("public_outputs", ← field full "public_outputs")]

structure Static (sourceBytes : List Nat) (treeBytes relationBytes abiBytes : String) where
  checked : GeneralRecordV2SourceCorrespondence.Checked
  sourceChecked : GeneralRecordV2SourceCorrespondence.check
    sourceBytes treeBytes relationBytes abiBytes = .ok checked
  program : S31.Program
  aligned : program = sourceProgram checked.source

/-- The original exact-byte validator runs first. No v2 field is silently
ignored: it has already been reconstructed from source before erasure. -/
def checkStatic (sourceBytes : List Nat) (treeBytes relationBytes abiBytes : String) :
    Parse (Static sourceBytes treeBytes relationBytes abiBytes) := do
  match sourceChecked : GeneralRecordV2SourceCorrespondence.check
      sourceBytes treeBytes relationBytes abiBytes with
  | .error message => throw message
  | .ok checked =>
      let full ← Json.parse relationBytes
      let core ← coreRelation full
      let program ← S31.Json.program core
      if aligned : program = sourceProgram checked.source then
        match program.validate with
        | .error _ => throw "source-derived normalized Program fails validation"
        | .ok _ => return ⟨checked, sourceChecked, program, aligned⟩
      else
        throw "record source and normalized Program differ"

/-- Accepted static packages use the actual normalized evaluator on the
source-derived typed program for *every* assignment, not merely test values.
This is a translation-validation identity; it does not prove the native AIR. -/
theorem checked_program_evaluate (sourceBytes : List Nat)
    (treeBytes relationBytes abiBytes : String)
    (accepted : Static sourceBytes treeBytes relationBytes abiBytes)
    (assignment : S31.Assignment) :
    GeneralRecordV2SourceCorrespondence.check
      sourceBytes treeBytes relationBytes abiBytes = .ok accepted.checked ∧
    accepted.program.evaluate assignment =
      (sourceProgram accepted.checked.source).evaluate assignment := by
  exact ⟨accepted.sourceChecked,
    congrArg (fun p : S31.Program => p.evaluate assignment) accepted.aligned⟩

private def canonicalStatement (bytes : String) : Parse Json := do
  if bytes.utf8ByteSize > 65536 then throw "record statement exceeds byte bound"
  let json ← Json.parse bytes
  if json.compress ++ "\n" != bytes then
    throw "noncanonical record statement JSON"
  return json

private def oneWord (json : Json) : Parse Nat := do
  let values ← array nat json
  match values with
  | [value] =>
      if value < S31.modulus then return value
      else throw "noncanonical record M31 claim"
  | _ => throw "record claim needs one M31 word"

private def checkLeaf (json : Json) (root fieldName : String) : Parse Nat := do
  fields json ["path", "words"]
  let path ← field json "path"
  let expected := toJson [Json.mkObj [("root", Json.str root)],
    Json.mkObj [("field", Json.str fieldName)]]
  if path != expected then throw "record statement path differs"
  oneWord (← field json "words")

structure Run (sourceBytes : List Nat) (treeBytes relationBytes abiBytes : String) where
  static : Static sourceBytes treeBytes relationBytes abiBytes
  assignment : S31.Assignment
  values : List S31.M31
  evaluated : static.program.evaluate assignment = .ok values

def Run.words {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (run : Run sourceBytes treeBytes relationBytes abiBytes) : List Nat :=
  run.values.map (·.val)

/-- The admitted statement is checked by the actual typed normalized
evaluator on an assignment constructed from public leaves only. -/
theorem checked_public_run_source_evaluate
    {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (run : Run sourceBytes treeBytes relationBytes abiBytes) :
    (sourceProgram run.static.checked.source).evaluate run.assignment =
      .ok run.values := by
  rw [← run.static.aligned]
  exact run.evaluated

/-- This is an opt-in proof preflight for the no-private, single-field record
class. All assigned values come from the same canonical statement bytes that
the caller must pass to the native verifier. -/
def checkPublicRun (sourceBytes : List Nat) (treeBytes relationBytes abiBytes
    statementBytes : String) :
    Parse (Run sourceBytes treeBytes relationBytes abiBytes) := do
  let static ← checkStatic sourceBytes treeBytes relationBytes abiBytes
  let source := static.checked.source
  let (root, fieldName, node) ← match source.roots, source.fields, source.nodes with
    | [root], [fieldName], [node] => pure (root, fieldName, node)
    | _, _, _ => throw "record public run is outside one-field one-node class"
  if root.visibility != "public" then
    throw "record public run requires public input"
  let output ← match resultWires source with
    | [name] => pure name
    | _ => throw "record public result shape differs"
  if output != node.name then
    throw "record public result must be arithmetic node"
  let rootName := root.name
  let statement ← canonicalStatement statementBytes
  fields statement ["version", "abi_sha256", "leaves"]
  if (← nat (← field statement "version")) != 2 then
    throw "record statement version differs"
  let sidecar ← Json.parse abiBytes
  let expectedDigest ← string (← field sidecar "boundary_sha256")
  if (← string (← field statement "abi_sha256")) != expectedDigest then
    throw "record statement ABI digest differs"
  let leaves ← array (fun value => pure value) (← field statement "leaves")
  let [inputLeaf, resultLeaf] := leaves |
    throw "record statement leaf count differs"
  let inputWord ← checkLeaf inputLeaf rootName fieldName
  let resultWord ← checkLeaf resultLeaf "result" fieldName
  let assignment : S31.Assignment :=
    { publicInputs := [((inputWires source).head!, [inputWord])],
      privateInputs := [], publicOutputs := [(output, [resultWord])] }
  match evaluated : static.program.evaluate assignment with
  | .error error =>
      throw s!"source-derived Program rejected public claim: {repr error}"
  | .ok values => return ⟨static, assignment, values, evaluated⟩

end S31.Functional.Correspondence.GeneralRecordV2ProgramAdmission
