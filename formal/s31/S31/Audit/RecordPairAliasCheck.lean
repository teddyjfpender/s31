import S31.Gadgets.Functional.RecordPinnedPairAliasV2

/-!
Exact-byte audit adapter for the pinned record-valued `pair` example. The
Lean constants are checked against compiler-emitted source and ABI bytes; the
semantic typed flattening and alias theorems live in the imported module.
This adapter does not validate arbitrary v2 descriptors or native proofs.
-/

namespace S31.Audit.RecordPairAliasCheck

open S31.Functional.RecordPinnedPairAliasV2

def report (accepted : Bool) (reason : String) : Lean.Json :=
  Lean.Json.mkObj [
    ("accepted", Lean.toJson accepted),
    ("checker", Lean.Json.str "RecordPinnedPairAliasV2"),
    ("reason", Lean.Json.str reason)]

def run (sourcePath abiPath : System.FilePath) : IO UInt32 := do
  try
    let source ← IO.FS.readBinFile sourcePath
    let abi ← IO.FS.readBinFile abiPath
    if source != sourceBytes.toUTF8 then
      IO.println (report false "source bytes differ").compress
      return 1
    if abi != abiBytes.toUTF8 then
      IO.println (report false "canonical ABI bytes differ").compress
      return 1
    IO.println (report true "exact source and ABI bytes match").compress
    return 0
  catch error =>
    IO.println (report false error.toString).compress
    return 2

end S31.Audit.RecordPairAliasCheck

def main (args : List String) : IO UInt32 := do
  match args with
  | [sourcePath, abiPath] =>
      S31.Audit.RecordPairAliasCheck.run sourcePath abiPath
  | _ =>
      IO.println (S31.Audit.RecordPairAliasCheck.report false
        "usage: RecordPairAliasCheck SOURCE.s31 ABI.json").compress
      return 2
