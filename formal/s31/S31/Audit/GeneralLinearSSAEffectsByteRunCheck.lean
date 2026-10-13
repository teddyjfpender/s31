import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsByteRun

/-! Runtime fixture gate for the exact effectful source-to-interpreter join. -/

namespace S31.Audit.GeneralLinearSSAEffectsByteRunCheck

open S31.Functional.Correspondence.GeneralLinearSSAEffectsByteRun
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)

def values : Nat → Lanes 3
  | 0 => fun i => (([1, 2, 3] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | 1 => fun i => (([72, 81, 90] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | _ => fun _ => 0

def claimed : Lanes 3 :=
  fun i => (([71, 79, 87] : List Nat).map
    RiscvRefinement.M31.reduce)[i.val]?.getD 0

def expectedSSA :
    S31.Functional.Correspondence.GeneralLinearSSAEffects.EmittedSSA :=
  { lane_count := 3,
    inputs := [
      { id := 0, name := "x", visibility := "public" },
      { id := 1, name := "y", visibility := "private" }],
    nodes := [
      { id := 2, name := "shifted", op := "add_const", lhs := 0,
        rhs := none, constant := some 7 },
      { id := 3, name := "scaled", op := "mul_const", lhs := 2,
        rhs := none, constant := some 9 },
      { id := 4, name := "out", op := "sub", lhs := 1,
        rhs := some 0, constant := none }],
    assertions := [(1, 3)], output := 4 }

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
      match checkEffectsByteRun sourceBytes certificate relation abi
          assignment publicBytes values claimed with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok checked =>
          if checked.ssa = expectedSSA then
            IO.println "accepted: effects source, typed assignment, ABI, interpreter"
            return 0
          else
            IO.eprintln "rejected: reviewed effects fixture roster differs"
            return 1
  | _ =>
      IO.eprintln "usage: SOURCE CERT RELATION ABI ASSIGNMENT PUBLIC_WORDS"
      return 2

end S31.Audit.GeneralLinearSSAEffectsByteRunCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.GeneralLinearSSAEffectsByteRunCheck.run args
