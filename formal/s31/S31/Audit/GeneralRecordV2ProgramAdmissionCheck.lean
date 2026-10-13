import S31.Gadgets.Functional.Correspondence.GeneralRecordV2ProgramAdmission
import S31.Gadgets.Functional.Correspondence.GeneralRecordV2EvaluateCorrespondence
import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAByteRun

/-! Executable exact-byte record-v2 source-to-Program and value-run checker. -/

namespace S31.Audit.GeneralRecordV2ProgramAdmissionCheck

open S31.Functional.Correspondence.GeneralRecordV2ProgramAdmission
open S31.Functional.Correspondence.GeneralRecordV2EvaluateCorrespondence

private def readSource (path : String) : IO (Option (List Nat)) := do
  let bytes ← IO.FS.readBinFile path
  if bytes.size > 16384 then
    IO.eprintln "rejected: source exceeds 16384 bytes"
    return none
  return some (bytes.toList.map UInt8.toNat)

private def readText (path : String) (limit : Nat) : IO (Option String) := do
  let bytes ← IO.FS.readFile path
  if bytes.utf8ByteSize > limit then
    IO.eprintln s!"rejected: {path} exceeds {limit} bytes"
    return none
  return some bytes

def run (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, treePath, relationPath, abiPath] =>
      let some source ← readSource sourcePath | return 1
      let some tree ← readText treePath 131072 | return 1
      let some relation ← readText relationPath 65536 | return 1
      let some abi ← readText abiPath 65536 | return 1
      match checkStatic source tree relation abi with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok _ =>
          IO.println "accepted: record-v2 source/typed Program correspondence"
          return 0
  | [sourcePath, treePath, relationPath, abiPath, statementPath] =>
      let some source ← readSource sourcePath | return 1
      let some tree ← readText treePath 131072 | return 1
      let some relation ← readText relationPath 65536 | return 1
      let some abi ← readText abiPath 65536 | return 1
      let some statement ← readText statementPath 65536 | return 1
      match checkPublicRun source tree relation abi statement with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok checked =>
          IO.println s!"accepted: record-v2 public Program run {checked.words}"
          return 0
  | [sourcePath, treePath, relationPath, abiPath, "--assignment", assignmentPath] =>
      let some source ← readSource sourcePath | return 1
      let some tree ← readText treePath 131072 | return 1
      let some relation ← readText relationPath 65536 | return 1
      let some abi ← readText abiPath 65536 | return 1
      let some assignmentBytes ← readText assignmentPath 65536 | return 1
      let accepted ← match checkStatic source tree relation abi with
        | .error message =>
            IO.eprintln s!"rejected: {message}"
            return 1
        | .ok static => pure static
      let assignment ← match S31.Functional.Correspondence.GeneralLinearSSAByteRun.parseTypedAssignment
          assignmentBytes with
        | .error message =>
            IO.eprintln s!"rejected: {message}"
            return 1
        | .ok parsed => pure parsed
      match checkSourceAssignment accepted assignment with
      | none =>
          IO.eprintln "rejected: source-ordered assignment or public claim differs"
          return 1
      | some checked =>
          IO.println s!"accepted: record-v2 source results {checked.sourceResults}; public words {checked.claimed.map (·.val)}"
          return 0
  | _ =>
      IO.eprintln "usage: SOURCE STRUCTURAL_TREE RELATION ABI [STATEMENT | --assignment ASSIGNMENT]"
      return 2

end S31.Audit.GeneralRecordV2ProgramAdmissionCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.GeneralRecordV2ProgramAdmissionCheck.run args
