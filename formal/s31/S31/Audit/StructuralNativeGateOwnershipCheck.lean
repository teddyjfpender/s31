import S31.Gadgets.Functional.Correspondence.StructuralNativeGateOwnership

/-! Concrete runtime control for direct gate ownership on supplied graph data. -/

namespace S31.Audit.StructuralNativeGateOwnershipCheck

open S31.Functional.Correspondence.StructuralNativeGateOwnership
open S31.Functional.Correspondence.StructuralNativeTraceDecoder
open S31.Functional.Correspondence.StructuralNativeGateCertificate
open S31.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes
open S31.Functional.Correspondence.GeneralLinearSSABytes
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)
open Lean

private def readWords (bytes : String) : Except String (List (List Nat) × List Nat) := do
  let json ← Json.parse bytes
  fields json ["inputs", "claimed"]
  let rows ← array (array nat) (← field json "inputs")
  let claim ← array nat (← field json "claimed")
  return (rows, claim)

private def checkN (n : Nat) (hn : n ≤ 4) (sourceBytes : List Nat)
    (certificateBytes graphBytes : String) (rows : List (List Nat))
    (claim : List Nat) : IO UInt32 := do
  match checkSourceCertificate sourceBytes certificateBytes with
  | .error message =>
      IO.eprintln s!"rejected: {message}"
      return 1
  | .ok (ssa, _, certificate) =>
      if ssa.lane_count != n || rows.length != ssa.inputs.length ||
          !rows.all (fun row => row.length == n && row.all (· < S31.modulus)) ||
          claim.length != n || claim.any (· ≥ S31.modulus) then
        IO.eprintln "rejected: lane count or concrete input/claim roster differs"
        return 1
      let inputs : Nat → Lanes n := fun id lane =>
        RiscvRefinement.M31.reduce (((rows[id]?).getD [])[lane.val]?.getD 0)
      let claimed : Lanes n := fun lane =>
        RiscvRefinement.M31.reduce (claim[lane.val]?.getD 0)
      match decodeExportedGraph graphBytes with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok graph =>
          if graph.sourceNames != ssa.names ||
              graph.addresses.length != certificate.inputs + certificate.steps.length then
            IO.eprintln "rejected: graph source-map roster differs from parsed SSA"
            return 1
          if !checkInputPorts hn graph.wire graph.addresses certificate.inputs inputs then
            IO.eprintln "rejected: graph input ports differ"
            return 1
          match checkOwnedSteps hn graph.wire graph.gates graph.addresses
              (nativeInitial hn graph.wire graph.addresses certificate.inputs)
              certificate.steps with
          | none =>
              IO.eprintln "rejected: source step lacks a direct owning native gate"
              return 1
          | some final =>
              if !checkOutputPort hn graph.wire graph.addresses final
                  certificate.output claimed ||
                  !checkAssertions final certificate.assertions then
                IO.eprintln "rejected: output or source assertion differs"
                return 1
              if !checkGates graph.wire graph.gates then
                IO.eprintln "rejected: supplied concrete native gate equations differ"
                return 1
              IO.println s!"accepted: {ssa.inputs.length} inputs, {ssa.nodes.length} directly owned steps, {n} lanes"
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
      if words.utf8ByteSize > 65536 then
        IO.eprintln "rejected: concrete input words exceed 65536 bytes"
        return 1
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

end S31.Audit.StructuralNativeGateOwnershipCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.StructuralNativeGateOwnershipCheck.run args
