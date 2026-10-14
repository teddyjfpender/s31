import S31.Gadgets.Functional.Correspondence.StructuralNativeFixedConstant

/-! Concrete source, graph, and fixed-seven path control. No proof verifier. -/

namespace S31.Audit.StructuralNativeFixedConstantCheck

open S31.Functional.Correspondence.StructuralNativeFixedConstant
open S31.Functional.Correspondence.StructuralNativeGateOwnership
open S31.Functional.Correspondence.StructuralNativeGateCertificate
open S31.Functional.Correspondence.StructuralNativeTraceDecoder
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

private def checkMulGates (wire : Nat → Quad) (gates : List MulGate) : Bool :=
  gates.all fun gate =>
    decide (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.out) =
      S31.Gadgets.Packed.mul
        (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in0))
        (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in1)))

private def checkN (n : Nat) (hn : n ≤ 4) (sourceBytes : List Nat)
    (certificateBytes graphBytes pathBytes : String)
    (rows : List (List Nat)) (claim : List Nat) : IO UInt32 := do
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
      match decodeExportedGraph graphBytes, decodeMulProjection graphBytes,
          decodeSevenPath pathBytes with
      | .ok graph, .ok projection, .ok path =>
          if graph.sourceNames != ssa.names ||
              graph.addresses.length != certificate.inputs + certificate.steps.length then
            IO.eprintln "rejected: graph source-map roster differs from parsed SSA"
            return 1
          if !checkInputPorts hn graph.wire graph.addresses certificate.inputs inputs then
            IO.eprintln "rejected: graph input ports differ"
            return 1
          if !path.checkOwned graph.gates projection.gates then
            IO.eprintln "rejected: fixed-seven path lacks an exact native gate"
            return 1
          if !checkPublicU graph.wire projection.outputs then
            IO.eprintln "rejected: native public u anchor differs"
            return 1
          match checkOwnedStepsSeven hn graph.wire graph.gates projection
              graph.addresses path
              (nativeInitial hn graph.wire graph.addresses certificate.inputs)
              certificate.steps with
          | none =>
              IO.eprintln "rejected: source step lacks native fixed-chain ownership"
              return 1
          | some final =>
              if !checkOutputPort hn graph.wire graph.addresses final
                  certificate.output claimed ||
                  !checkAssertions final certificate.assertions then
                IO.eprintln "rejected: output or source assertion differs"
                return 1
              if !checkGates graph.wire graph.gates ||
                  !checkMulGates graph.wire projection.gates then
                IO.eprintln "rejected: concrete native AIR gate equations differ"
                return 1
              IO.println s!"accepted: fixed-seven path, {ssa.nodes.length} steps, {n} lanes"
              return 0
      | .error message, _, _ =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | _, .error message, _ =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | _, _, .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1

def run (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, certificatePath, graphPath, wordsPath, pathPath] =>
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
      let path ← IO.FS.readFile pathPath
      if words.utf8ByteSize > 65536 then
        IO.eprintln "rejected: concrete input words exceed 65536 bytes"
        return 1
      match readWords words with
      | .error message =>
          IO.eprintln s!"rejected: {message}"
          return 1
      | .ok (rows, claim) =>
          match claim.length with
          | 1 => checkN 1 (by decide) (source.toList.map UInt8.toNat) certificate graph path rows claim
          | 2 => checkN 2 (by decide) (source.toList.map UInt8.toNat) certificate graph path rows claim
          | 3 => checkN 3 (by decide) (source.toList.map UInt8.toNat) certificate graph path rows claim
          | 4 => checkN 4 (by decide) (source.toList.map UInt8.toNat) certificate graph path rows claim
          | _ =>
              IO.eprintln "rejected: expected one to four M31 lanes"
              return 1
  | _ =>
      IO.eprintln "usage: SOURCE.s31 CERTIFICATE.json GRAPH.json WORDS.json SEVEN_PATH.json"
      return 2

end S31.Audit.StructuralNativeFixedConstantCheck

def main (args : List String) : IO UInt32 :=
  S31.Audit.StructuralNativeFixedConstantCheck.run args
