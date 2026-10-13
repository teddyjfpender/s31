import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAByteRun

/-! Runtime fixture gate for the exact pure source-to-interpreter byte join. -/

namespace S31.Audit.GeneralLinearSSAByteRunCheck

open S31.Functional.Correspondence.GeneralLinearSSAByteRun
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)

def values : Nat → Lanes 5
  | 0 => fun i => (([3, 4, 5, 6, 7] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | 1 => fun i => (([2, 1, 0, 4, 3] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | _ => fun _ => 0

def claimed : Lanes 5 :=
  fun i => (([2, 6, 10, 4, 8] : List Nat).map
    RiscvRefinement.M31.reduce)[i.val]?.getD 0

def run (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, certificatePath, relationPath, abiPath,
      assignmentPath, publicPath] =>
      let source ← IO.FS.readBinFile sourcePath
      let sourceBytes := source.toList.map UInt8.toNat
      let certificate ← IO.FS.readFile certificatePath
      let relation ← IO.FS.readFile relationPath
      let abi ← IO.FS.readFile abiPath
      let assignment ← IO.FS.readFile assignmentPath
      let raw ← IO.FS.readBinFile publicPath
      let publicBytes := raw.toList.map UInt8.toNat
      match checkPureByteRun sourceBytes certificate relation abi assignment
          publicBytes values claimed with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok checked =>
          if checked.ssa =
              S31.Functional.Correspondence.GeneralLinearSSA.subtractionThenDoubleEmitted then
            IO.println "accepted: pure source, typed assignment, ABI, interpreter"
            return 0
          else
            IO.eprintln "rejected: reviewed fixture roster differs"
            return 1
  | _ =>
      IO.eprintln "usage: SOURCE CERT RELATION ABI ASSIGNMENT PUBLIC_WORDS"
      return 2

end S31.Audit.GeneralLinearSSAByteRunCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.GeneralLinearSSAByteRunCheck.run args
