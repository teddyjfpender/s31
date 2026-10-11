import S31.Gadgets.Functional.Correspondence.AliasCanonicalIrBytes

/-!
An optional, executable audit adapter for the proved bounded alias fragment.
It reads exact source, normalized relation, and optional canonical IR bytes
and calls the proved checker without reimplementing its parser or encoders.
This executable is not the native release verifier.
-/

namespace S31.Audit.AliasRelationCheck

open S31.Functional.SSACertificate
open S31.Functional.SSAAliasTextBytes
open S31.Functional.Correspondence.AliasCanonicalIrBytes

def gateJson (gate : Instruction) : Lean.Json :=
  Lean.Json.mkObj [
    ("id", Lean.toJson gate.id),
    ("lhs", Lean.toJson gate.lhs),
    ("rhs", Lean.toJson gate.rhs),
    ("op", Lean.Json.str (if gate.multiply then "mul" else "add"))]

def acceptedJson (checker : String) (certificate : Certificate) : Lean.Json :=
  Lean.Json.mkObj [
    ("accepted", Lean.toJson true),
    ("checker", Lean.Json.str checker),
    ("gate_count", Lean.toJson certificate.instructions.length),
    ("gates", Lean.toJson (certificate.instructions.map gateJson)),
    ("output_wire", Lean.toJson certificate.output)]

def rejectedJson (checker : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("accepted", Lean.toJson false),
    ("checker", Lean.Json.str checker),
    ("reason", Lean.Json.str "source or exact normalized bytes rejected")]

def ioErrorJson (message : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("accepted", Lean.toJson false),
    ("error", Lean.Json.str message)]

def fileBytes (path : System.FilePath) : IO (List Nat) := do
  let bytes ← IO.FS.readBinFile path
  return bytes.toList.map UInt8.toNat

def run (sourcePath normalizedPath : System.FilePath)
    (canonicalPath : Option System.FilePath) : IO UInt32 := do
  try
    let source ← fileBytes sourcePath
    let normalized ← fileBytes normalizedPath
    let checker := if canonicalPath.isSome then
      "AliasCanonicalIrBytes.checkAliasCanonical" else
      "SSAAliasTextBytes.checkAliasRelation"
    let result ← match canonicalPath with
      | some path => do
          let canonical ← fileBytes path
          pure (checkAliasCanonical source normalized canonical)
      | none => pure (checkAliasRelation source normalized)
    IO.println (match result with
      | some certificate => (acceptedJson checker certificate).compress
      | none => (rejectedJson checker).compress)
    return if result.isSome then 0 else 1
  catch error =>
    IO.println (ioErrorJson error.toString).compress
    return 2

end S31.Audit.AliasRelationCheck

def main (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, normalizedPath] =>
      S31.Audit.AliasRelationCheck.run sourcePath normalizedPath none
  | [sourcePath, normalizedPath, canonicalPath] =>
      S31.Audit.AliasRelationCheck.run sourcePath normalizedPath canonicalPath
  | _ =>
      IO.println (S31.Audit.AliasRelationCheck.ioErrorJson
        "usage: s31-alias-relation-check SOURCE.s31 NORMALIZED.s31.json [CANONICAL-IR.json]").compress
      return 2
