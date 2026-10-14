import S31.Gadgets.Functional.Correspondence.StructuralNativeTraceDecoder

/-!
Runtime control for the composed exact-source/certificate/native-graph Lean
checker. The value file is a concrete test input, not a proof commitment.
-/

namespace S31.Audit.StructuralNativeTraceDecoderCheck

open S31.Functional.Correspondence.StructuralNativeTraceDecoder
open S31.Functional.Correspondence.GeneralLinearSSABytes
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)
open Lean

private def readWords (bytes : String) : Except String (List (List Nat) × List Nat) := do
  let json ← Json.parse bytes
  fields json ["inputs", "claimed"]
  let inputs ← array (array nat) (← field json "inputs")
  let claimed ← array nat (← field json "claimed")
  return (inputs, claimed)

private def checkN (n : Nat) (hn : n ≤ 4) (sourceBytes : List Nat)
    (certificate graphBytes : String) (rows : List (List Nat))
    (claim : List Nat) : IO UInt32 := do
  if !rows.all (fun row => row.length == n && row.all (· < S31.modulus)) ||
      claim.length != n || claim.any (· ≥ S31.modulus) then
    IO.eprintln "rejected: input or claim has wrong width or noncanonical M31 word"
    return 1
  let inputs : Nat → Lanes n := fun id lane =>
    RiscvRefinement.M31.reduce (((rows[id]?).getD [])[lane.val]?.getD 0)
  let claimed : Lanes n := fun lane =>
    RiscvRefinement.M31.reduce (claim[lane.val]?.getD 0)
  match checkSourceNativeGraph hn sourceBytes certificate graphBytes inputs claimed with
  | .error message =>
      IO.eprintln s!"rejected: {message}"
      return 1
  | .ok checked =>
      IO.println s!"accepted: {checked.ssa.inputs.length} inputs, {checked.ssa.nodes.length} source nodes, {n} lanes"
      return 0

def run (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, certificatePath, graphPath, wordsPath] =>
      let source ← IO.FS.readBinFile sourcePath
      if source.size > 16384 then
        IO.eprintln "rejected: source exceeds 16384 bytes"
        return 1
      let certificate ← IO.FS.readFile certificatePath
      if certificate.utf8ByteSize > 65536 then
        IO.eprintln "rejected: certificate exceeds 65536 bytes"
        return 1
      let graph ← IO.FS.readFile graphPath
      let words ← IO.FS.readFile wordsPath
      match readWords words with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok (rows, claim) =>
          match claim.length with
          | 1 => checkN 1 (by decide) (source.toList.map UInt8.toNat) certificate graph rows claim
          | 2 => checkN 2 (by decide) (source.toList.map UInt8.toNat) certificate graph rows claim
          | 3 => checkN 3 (by decide) (source.toList.map UInt8.toNat) certificate graph rows claim
          | 4 => checkN 4 (by decide) (source.toList.map UInt8.toNat) certificate graph rows claim
          | _ =>
              IO.eprintln "rejected: expected one to four M31 lanes"
              return 1
  | _ =>
      IO.eprintln "usage: SOURCE.s31 CERTIFICATE.json GRAPH.json WORDS.json"
      return 2

end S31.Audit.StructuralNativeTraceDecoderCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.StructuralNativeTraceDecoderCheck.run args
