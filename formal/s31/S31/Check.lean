import S31.Semantics.Json
import S31.Semantics.Graph
import S31.Semantics.Poseidon2
import S31.Semantics.Sha256
import S31.Semantics.Blake2s

namespace S31.ScheduleCheck

open Graph

/-- Supported fixed circuit profiles. This is executable regression evidence;
`Graph.Code.check_sound` proves the meaning of each successful Boolean check. -/
def profiles : List (String × Bool) :=
  [("poseidon_pair", Poseidon2.pairCode.check fieldArity 16)] ++
  ([4, 8, 12, 16] : List Nat).map (fun n =>
    (s!"poseidon_leaf_{n}", (Poseidon2.leafCode n).check fieldArity n)) ++
  [("sha256_compression", Sha256.compressionCode.check wordArity 24)] ++
  (List.range 17).flatMap (fun n =>
    [(s!"blake2s_{n}_plain", (Blake2s.code n []).check wordArity n),
     (s!"blake2s_{n}_leaf", (Blake2s.code n Blake2s.leafPersonalization).check wordArity n),
     (s!"blake2s_{n}_pair", (Blake2s.code n Blake2s.pairPersonalization).check wordArity n)])

def badWire : Code M31 FieldOp := ⟨[.apply .add [0, 7]], [1]⟩
def badArity : Code M31 FieldOp := ⟨[.apply .add [0]], [1]⟩

def check : IO UInt32 := do
  let failures := profiles.filter (fun row => !row.2)
  let malformedRejected := [!badWire.check fieldArity 1, !badArity.check fieldArity 1]
  let passed := failures.isEmpty && malformedRejected.all id && profiles.length == 57
  let report := Lean.Json.mkObj [
    ("checked", Lean.toJson profiles.length),
    ("profiles", Lean.toJson (profiles.map Prod.fst)),
    ("all_valid", Lean.toJson failures.isEmpty),
    ("malformed_rejected", Lean.toJson (malformedRejected.filter id).length),
    ("failed", Lean.toJson (failures.map Prod.fst))]
  IO.println report.compress
  return if passed then 0 else 1

end S31.ScheduleCheck

/-- Executable regression adapter, not a proof oracle. `eval` outputs never
enter a theorem or the axiom audit. One request per JSON line. -/
def main (args : List String) : IO UInt32 := do
  if args == ["--schedule-check"] then
    return ← S31.ScheduleCheck.check
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let result := do
      let request ← Lean.Json.parse line
      S31.Json.objectFields request ["program", "assignment"]
      S31.Json.evaluate (← request.getObjVal? "program") (← request.getObjVal? "assignment")
    let response := match result with
      | .ok words => Lean.Json.mkObj [("ok", Lean.toJson words)]
      | .error message => Lean.Json.mkObj [("error", Lean.Json.str message)]
    stdout.putStrLn response.compress
  return 0
