import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAPublicABI

/-! Runtime control for three independently reviewed certificate/ABI/statement
fixtures. This runner checks exact bytes against handwritten field values; it
does not infer native public-pin ownership from proof verification. -/

namespace S31.Audit.GeneralLinearSSAPublicABICheck

open S31.Functional.Correspondence.GeneralLinearSSAPublicABI
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)

def pureValues : Nat → Lanes 5
  | 0 => fun i => (([3, 4, 5, 6, 7] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | 1 => fun i => (([2, 1, 0, 4, 3] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | _ => fun _ => 0

def pureClaimed : Lanes 5 :=
  fun i => (([2, 6, 10, 4, 8] : List Nat).map
    RiscvRefinement.M31.reduce)[i.val]?.getD 0

def effectsValues : Nat → Lanes 3
  | 0 => fun i => (([1, 2, 3] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | 1 => fun i => (([72, 81, 90] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | _ => fun _ => 0

def effectsClaimed : Lanes 3 :=
  fun i => (([71, 79, 87] : List Nat).map
    RiscvRefinement.M31.reduce)[i.val]?.getD 0

def orderedValues : Nat → Lanes 2
  | 0 => fun i => (([1, 2] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | 1 => fun i => (([3, 4] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | 2 => fun i => (([99, 100] : List Nat).map
      RiscvRefinement.M31.reduce)[i.val]?.getD 0
  | _ => fun _ => 0

def orderedClaimed : Lanes 2 :=
  fun i => (([4, 6] : List Nat).map
    RiscvRefinement.M31.reduce)[i.val]?.getD 0

def expectedOrderedSSA :
    S31.Functional.Correspondence.GeneralLinearSSA.EmittedSSA :=
  { lane_count := 2,
    inputs := [
      { id := 0, name := "x", visibility := "public" },
      { id := 1, name := "y", visibility := "public" },
      { id := 2, name := "salt", visibility := "private" }],
    nodes := [{ id := 3, name := "sum", op := "add", lhs := 0, rhs := 1 }],
    assertions := [], output := 3 }

def expectedEffectsSSA :
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
  | [mode, sourcePath, certificatePath, relationPath, abiPath,
      assignmentPath, publicPath] =>
      let source ← IO.FS.readBinFile sourcePath
      let sourceBytes := source.toList.map UInt8.toNat
      let certificate ← IO.FS.readFile certificatePath
      let relation ← IO.FS.readFile relationPath
      let abi ← IO.FS.readFile abiPath
      let assignment ← IO.FS.readFile assignmentPath
      let raw ← IO.FS.readBinFile publicPath
      let words := raw.toList.map UInt8.toNat
      if mode == "pure" then
        match S31.Functional.Correspondence.GeneralLinearSSASourceBytes.checkSourceCertificate
            sourceBytes certificate with
        | .error message =>
            IO.eprintln s!"rejected: {message}"
            return 1
        | .ok (sourceSSA, meaning, _) =>
            match checkPure certificate abi assignment words meaning
                pureValues pureClaimed with
            | .error message =>
                IO.eprintln s!"rejected: {message}"
                return 1
            | .ok (ssa, _) =>
                if ssa = sourceSSA &&
                    ssa = S31.Functional.Correspondence.GeneralLinearSSA.subtractionThenDoubleEmitted &&
                    (checkRelationSSA relation ssa.lane_count ssa.inputs
                      ssa.names ssa.output).isOk then
                  IO.println "accepted: pure source-derived M31 public ABI"
                  return 0
                else
                  IO.eprintln "rejected: pure fixture roster differs"
                  return 1
      else if mode == "effects" then
        match S31.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate
            sourceBytes certificate with
        | .error message =>
            IO.eprintln s!"rejected: {message}"
            return 1
        | .ok (sourceSSA, meaning, _) =>
            match checkEffects certificate abi assignment words meaning
                effectsValues effectsClaimed with
            | .error message =>
                IO.eprintln s!"rejected: {message}"
                return 1
            | .ok (ssa, _) =>
                if ssa = sourceSSA && ssa = expectedEffectsSSA &&
                    (checkRelationSSA relation ssa.lane_count ssa.inputs
                      ssa.names ssa.output).isOk then
                  IO.println "accepted: effects source-derived M31 public ABI"
                  return 0
                else
                  IO.eprintln "rejected: effects fixture roster differs"
                  return 1
      else if mode == "ordered" then
        match S31.Functional.Correspondence.GeneralLinearSSASourceBytes.checkSourceCertificate
            sourceBytes certificate with
        | .error message =>
            IO.eprintln s!"rejected: {message}"
            return 1
        | .ok (sourceSSA, meaning, _) =>
            match checkPure certificate abi assignment words meaning
                orderedValues orderedClaimed with
            | .error message =>
                IO.eprintln s!"rejected: {message}"
                return 1
            | .ok (ssa, _) =>
                if ssa = sourceSSA && ssa = expectedOrderedSSA &&
                    (checkRelationSSA relation ssa.lane_count ssa.inputs
                      ssa.names ssa.output).isOk then
                  IO.println "accepted: ordered two-public-input M31 ABI"
                  return 0
                else
                  IO.eprintln "rejected: ordered fixture roster differs"
                  return 1
      else
        IO.eprintln "usage: MODE pure|effects|ordered SOURCE CERT RELATION ABI ASSIGNMENT PUBLIC_WORDS"
        return 2
  | _ =>
      IO.eprintln "usage: MODE pure|effects|ordered SOURCE CERT RELATION ABI ASSIGNMENT PUBLIC_WORDS"
      return 2

end S31.Audit.GeneralLinearSSAPublicABICheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.GeneralLinearSSAPublicABICheck.run args
