import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck

/-! Generic bounded effectful package and per-statement runtime gate. -/

namespace S31.Audit.GeneralLinearSSAEffectsPackageCheck

open S31.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck

private def readBytes (path : String) : IO (Option (List Nat)) := do
  let bytes ← IO.FS.readBinFile path
  if bytes.size > 65536 then
    IO.eprintln s!"rejected: {path} exceeds 65536 bytes"
    return none
  return some (bytes.toList.map UInt8.toNat)

private def readText (path : String) : IO (Option String) := do
  let bytes ← IO.FS.readFile path
  if bytes.utf8ByteSize > 65536 then
    IO.eprintln s!"rejected: {path} exceeds 65536 bytes"
    return none
  return some bytes

def run (args : List String) : IO UInt32 := do
  match args with
  | ["static", sourcePath, certificatePath, relationPath, abiPath] =>
      let some source ← readBytes sourcePath | return 1
      let some certificate ← readText certificatePath | return 1
      let some relation ← readText relationPath | return 1
      let some abi ← readText abiPath | return 1
      match checkStatic source certificate relation abi with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok _ =>
          IO.println "accepted: effectful source/certificate/relation/ABI"
          return 0
  | ["run", sourcePath, certificatePath, relationPath, abiPath,
      assignmentPath, publicPath] =>
      let some source ← readBytes sourcePath | return 1
      let some certificate ← readText certificatePath | return 1
      let some relation ← readText relationPath | return 1
      let some abi ← readText abiPath | return 1
      let some assignment ← readText assignmentPath | return 1
      let some publicBytes ← readBytes publicPath | return 1
      if publicBytes.length != 32 then
        IO.eprintln "rejected: public statement must be 32 bytes"
        return 1
      match checkRun source certificate relation abi assignment publicBytes with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok _ =>
          IO.println "accepted: effectful source/ABI/typed assignment/interpreter"
          return 0
  | ["statement", sourcePath, certificatePath, relationPath, abiPath,
      assignmentPath, statementPath] =>
      let some source ← readBytes sourcePath | return 1
      let some certificate ← readText certificatePath | return 1
      let some relation ← readText relationPath | return 1
      let some abi ← readText abiPath | return 1
      let some assignment ← readText assignmentPath | return 1
      let some statement ← readText statementPath | return 1
      match checkRunStatement source certificate relation abi assignment
          statement with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok _ =>
          IO.println "accepted: effectful source and exact public statement"
          return 0
  | _ =>
      IO.eprintln "usage: static SOURCE CERT RELATION ABI | run SOURCE CERT RELATION ABI ASSIGNMENT PUBLIC_WORDS | statement SOURCE CERT RELATION ABI ASSIGNMENT PUBLIC_STATEMENT_JSON"
      return 2

end S31.Audit.GeneralLinearSSAEffectsPackageCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.GeneralLinearSSAEffectsPackageCheck.run args
