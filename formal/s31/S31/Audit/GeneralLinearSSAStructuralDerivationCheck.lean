import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAStructuralDerivation

/-! Exact-byte M31 typed structural tree to source/relation/ABI validator. -/

namespace S31.Audit.GeneralLinearSSAStructuralDerivationCheck

open S31.Functional.Correspondence.GeneralLinearSSAStructuralDerivation

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
  | [sourcePath, treePath, certificatePath, relationPath, abiPath] =>
      let some source ← readSource sourcePath | return 1
      let some tree ← readText treePath 131072 | return 1
      let some certificate ← readText certificatePath 65536 | return 1
      let some relation ← readText relationPath 65536 | return 1
      let some abi ← readText abiPath 65536 | return 1
      match checkPackage source tree certificate relation abi with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok _ =>
          IO.println "accepted: structural tree/source/relation/public ABI"
          return 0
  | _ =>
      IO.eprintln "usage: SOURCE STRUCTURAL_TREE CERTIFICATE RELATION ABI"
      return 2

end S31.Audit.GeneralLinearSSAStructuralDerivationCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.GeneralLinearSSAStructuralDerivationCheck.run args
