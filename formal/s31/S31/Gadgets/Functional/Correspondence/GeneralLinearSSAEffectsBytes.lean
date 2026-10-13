import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffects
import S31.Gadgets.Functional.Correspondence.GeneralLinearSSABytes
import Lean.Data.Json

/-!
Canonical byte admission for `linear-ssa-m31-effects-v1`. This decoder checks
the complete JSON shape and arithmetic/assertion graph, then compares that
graph with a separately supplied Lean source meaning. It checks digest syntax
but does not recompute SHA-256 or parse the `.s31` source text.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAEffectsBytes

open Lean
open GeneralLinearSSAEffects
open GeneralLinearSSA (Lanes)

open GeneralLinearSSABytes (Parse fields field string nat array digest exactString pythonCanonical)

private def input (json : Json) : Parse GeneralLinearSSA.EmittedInput := do
  fields json ["id", "name", "visibility"]
  let id ← nat (← field json "id")
  let name ← string (← field json "name")
  let visibility ← string (← field json "visibility")
  return { id, name, visibility }

private def node (json : Json) : Parse EmittedNode := do
  let op ← string (← field json "op")
  match op with
  | "add" | "sub" | "mul" =>
      fields json ["id", "name", "op", "lhs", "rhs"]
      let id ← nat (← field json "id")
      let name ← string (← field json "name")
      let lhs ← nat (← field json "lhs")
      let rhs ← nat (← field json "rhs")
      return { id, name, op, lhs, rhs := some rhs, constant := none }
  | "add_const" | "mul_const" =>
      fields json ["id", "name", "op", "lhs", "constant"]
      let id ← nat (← field json "id")
      let name ← string (← field json "name")
      let lhs ← nat (← field json "lhs")
      let constant ← nat (← field json "constant")
      return { id, name, op, lhs, rhs := none, constant := some constant }
  | _ => throw "operation outside effects profile"

private def assertion (json : Json) : Parse (Nat × Nat) := do
  let values ← array nat json
  match values with
  | [lhs, rhs] => return (lhs, rhs)
  | _ => throw "assertion must contain exactly two IDs"

private def ssa (json : Json) : Parse EmittedSSA := do
  fields json ["lane_count", "inputs", "nodes", "assertions", "output"]
  let lane_count ← nat (← field json "lane_count")
  let inputs ← array input (← field json "inputs")
  let nodes ← array node (← field json "nodes")
  let assertions ← array assertion (← field json "assertions")
  let output ← nat (← field json "output")
  return { lane_count, inputs, nodes, assertions, output }

/-- Parse a complete, canonical, bounded certificate byte string. Unknown
fields, duplicate keys, alternative whitespace, wrong operation operands,
and unsupported profiles are rejected before the semantic graph checker. -/
def decodeCertificate (bytes : String) : Parse EmittedSSA := do
  if bytes.utf8ByteSize > 65536 then
    throw "certificate JSON exceeds 65536 bytes"
  let json ← Json.parse bytes
  if pythonCanonical 0 json ++ "\n" != bytes then
    throw "noncanonical certificate JSON bytes"
  fields json ["schema", "capability", "source_sha256", "relation_sha256",
    "ssa", "lean_semantic_profile", "unmodeled_features"]
  exactString (← field json "schema")
    "s31-source-relation-certificate-v1"
  exactString (← field json "capability") "source-to-relation-only"
  digest (← field json "source_sha256")
  digest (← field json "relation_sha256")
  exactString (← field json "lean_semantic_profile")
    "linear-ssa-m31-effects-v1"
  let unmodeled ← array string (← field json "unmodeled_features")
  if !unmodeled.isEmpty then throw "unmodeled features outside effects profile"
  ssa (← field json "ssa")

def checkCertificate (bytes : String) (source : Source) :
    Parse (EmittedSSA × Certificate) :=
  match decodeCertificate bytes with
  | .error message => .error message
  | .ok parsed =>
      match checkEmittedSSA parsed source with
      | some certificate => .ok (parsed, certificate)
      | none => .error "effects SSA does not match source meaning"

theorem checked_certificate_parts (bytes : String) (source : Source)
    (parsed : EmittedSSA) (certificate : Certificate)
    (hcheck : checkCertificate bytes source = .ok (parsed, certificate)) :
    decodeCertificate bytes = .ok parsed ∧
    checkEmittedSSA parsed source = some certificate := by
  unfold checkCertificate at hcheck
  cases hdecode : decodeCertificate bytes with
  | error message => simp [hdecode] at hcheck
  | ok actual =>
      cases hgraph : checkEmittedSSA actual source with
      | none => simp [hdecode, hgraph] at hcheck
      | some found =>
          have heq : (actual, found) = (parsed, certificate) := by
            simpa [hdecode, hgraph] using hcheck
          cases Prod.mk.inj heq with
          | intro hparsed hcertificate =>
              subst parsed
              subst certificate
              exact ⟨rfl, hgraph⟩

theorem certificate_bytes_air_sound (bytes : String) (source : Source)
    (parsed : EmittedSSA) (certificate : Certificate)
    (inputs : Nat → Lanes parsed.lane_count)
    (claimed : Lanes parsed.lane_count)
    (final : List (Lanes parsed.lane_count))
    (hcheck : checkCertificate bytes source = .ok (parsed, certificate))
    (hrows : AcceptsTrace
      (initialValues certificate.inputs inputs) certificate.steps final)
    (houtput : final[certificate.output]? = some claimed)
    (hassert : assertionsAir final certificate.assertions) :
    source.accepts inputs claimed :=
  emitted_ssa_air_sound parsed source certificate inputs claimed final
    (checked_certificate_parts bytes source parsed certificate hcheck).2
    hrows houtput hassert

end S31.Functional.Correspondence.GeneralLinearSSAEffectsBytes
