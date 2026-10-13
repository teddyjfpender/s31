import S31.Gadgets.Functional.Correspondence.SourceFunctionCanonicalBytes

/-!
Optional audit adapter for the proved bounded named-function fragment. It
reads exact source and normalized relation bytes, then calls the Lean checker
without reimplementing its parser or canonical encoder. Successful output
means that the files match the modeled source semantics and packed AIR row
relation. This executable does not authenticate a native STARK proof.
-/

namespace S31.Audit.SourceFunctionCheck

open S31.Functional.Correspondence.SourceFunctionBytes

def checkerName (canonical : Bool) : String :=
  if canonical then "SourceFunctionCanonicalBytes.checkCanonical"
  else "SourceFunctionBytes.checkRelation"

def operation : S31.Functional.Correspondence.SourceFunctionBytes.Op → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"

def acceptedJson (parsed : Parsed) (canonical : Bool) : Lean.Json :=
  Lean.Json.mkObj [
    ("accepted", Lean.toJson true),
    ("checker", Lean.Json.str (checkerName canonical)),
    ("canonical_ir_checked", Lean.toJson canonical),
    ("length", Lean.toJson parsed.length),
    ("operation", Lean.Json.str (operation parsed.op)),
    ("packed_rows", Lean.toJson ((parsed.length + 3) / 4))]

def rejectedJson (reason : String) (canonical : Bool) : Lean.Json :=
  Lean.Json.mkObj [
    ("accepted", Lean.toJson false),
    ("checker", Lean.Json.str (checkerName canonical)),
    ("reason", Lean.Json.str reason)]

def fileBytes (path : System.FilePath) : IO (List Nat) := do
  let bytes ← IO.FS.readBinFile path
  return bytes.toList.map UInt8.toNat

def run (sourcePath normalizedPath : System.FilePath)
    (canonicalPath : Option System.FilePath) : IO UInt32 := do
  try
    let source ← fileBytes sourcePath
    let normalized ← fileBytes normalizedPath
    let result ← match canonicalPath with
      | some path => do
          let canonical ← fileBytes path
          pure (S31.Functional.Correspondence.SourceFunctionCanonicalBytes.checkCanonical
            source normalized canonical)
      | none => pure (checkRelation source normalized)
    match result with
    | some parsed =>
        IO.println (acceptedJson parsed canonicalPath.isSome).compress
        return (0 : UInt32)
    | none =>
        IO.println (rejectedJson "source or exact relation/IR bytes rejected"
          canonicalPath.isSome).compress
        return (1 : UInt32)
  catch error =>
    IO.println (rejectedJson error.toString canonicalPath.isSome).compress
    return (2 : UInt32)

end S31.Audit.SourceFunctionCheck

def main (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, normalizedPath] =>
      S31.Audit.SourceFunctionCheck.run sourcePath normalizedPath none
  | [sourcePath, normalizedPath, canonicalPath] =>
      S31.Audit.SourceFunctionCheck.run sourcePath normalizedPath canonicalPath
  | _ =>
      IO.println (S31.Audit.SourceFunctionCheck.rejectedJson
        "usage: s31-source-function-check SOURCE.s31 NORMALIZED.s31.json [CANONICAL-IR.json]"
        false).compress
      return 2
