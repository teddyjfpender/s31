import S31.Gadgets.Functional.Correspondence.GeneralLinearSSA
import Lean.Data.Json

/-!
Lean's independent JSON decoding of the complete emitted
`s31-source-relation-certificate-v1` document for the pure arithmetic profile.
This binds the kernel theorem to the bytes supplied to this decoder. It does
not compute or authenticate source/relation SHA-256, parse `.s31` source bytes,
or authenticate a package's actual file path or native proof.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSABytes

open Lean
open S31.Functional.Correspondence.GeneralLinearSSA

abbrev Parse := Except String

/-- Python's `json.dumps(..., indent=2, sort_keys=True, ensure_ascii=True)`
layout on the certificate's ASCII-only pure profile. Comparing the complete
input against this rendering also rejects duplicate keys discarded by
`Lean.Json.parse`, unusual number spellings, and insignificant whitespace. -/
partial def pythonCanonical (depth : Nat) : Json → String
  | .obj object =>
      let entries := object.toList.mergeSort (fun left right => left.1 ≤ right.1)
      if entries.isEmpty then "{}" else
        "{\n" ++ String.intercalate ",\n" (entries.map fun (key, value) =>
          String.ofList (List.replicate (2 * (depth + 1)) ' ') ++
          (Json.str key).compress ++ ": " ++ pythonCanonical (depth + 1) value) ++
        "\n" ++ String.ofList (List.replicate (2 * depth) ' ') ++ "}"
  | .arr values =>
      if values.isEmpty then "[]" else
        "[\n" ++ String.intercalate ",\n" (values.toList.map fun value =>
          String.ofList (List.replicate (2 * (depth + 1)) ' ') ++
          pythonCanonical (depth + 1) value) ++
        "\n" ++ String.ofList (List.replicate (2 * depth) ' ') ++ "]"
  | other => other.compress

def fields (json : Json) (allowed : List String) : Parse Unit := do
  let object ← json.getObj?
  for (name, _) in object.toList do
    if !allowed.contains name then throw s!"unknown field: {name}"

def field (json : Json) (name : String) : Parse Json :=
  json.getObjVal? name

def string (json : Json) : Parse String := json.getStr?
def nat (json : Json) : Parse Nat := json.getNat?

def array (decode : Json → Parse α) (json : Json) : Parse (List α) := do
  (← json.getArr?).toList.mapM decode

private def lowerHexChar (char : Char) : Bool :=
  ('0' ≤ char && char ≤ '9') || ('a' ≤ char && char ≤ 'f')

def digest (json : Json) : Parse Unit := do
  let value ← string json
  if value.toList.length != 64 || !value.toList.all lowerHexChar then
    throw "SHA-256 digest must be 64 lowercase hex digits"

def exactString (json : Json) (expected : String) : Parse Unit := do
  let actual ← string json
  if actual != expected then throw s!"expected {expected}"

private def input (json : Json) : Parse EmittedInput := do
  fields json ["id", "name", "visibility"]
  let id ← nat (← field json "id")
  let name ← string (← field json "name")
  let visibility ← string (← field json "visibility")
  return { id := id, name := name, visibility := visibility }

private def node (json : Json) : Parse EmittedNode := do
  fields json ["id", "name", "op", "lhs", "rhs"]
  let id ← nat (← field json "id")
  let name ← string (← field json "name")
  let op ← string (← field json "op")
  let lhs ← nat (← field json "lhs")
  let rhs ← nat (← field json "rhs")
  return { id := id, name := name, op := op, lhs := lhs, rhs := rhs }

private def assertion (json : Json) : Parse (Nat × Nat) := do
  let values ← array nat json
  match values with
  | [lhs, rhs] => return (lhs, rhs)
  | _ => throw "assertion must have exactly two IDs"

private def ssa (json : Json) : Parse EmittedSSA := do
  fields json ["lane_count", "inputs", "nodes", "assertions", "output"]
  let lane_count ← nat (← field json "lane_count")
  let inputs ← array input (← field json "inputs")
  let nodes ← array node (← field json "nodes")
  let assertions ← array assertion (← field json "assertions")
  let output ← nat (← field json "output")
  return { lane_count := lane_count, inputs := inputs, nodes := nodes, assertions := assertions, output := output }

/-- Decode every field of the pure-profile certificate, including the
version/capability/profile discriminants and digest *syntax*. Unknown decoded
fields, missing fields and unmodeled operation tags fail closed. -/
def decodeCertificate (bytes : String) : Parse EmittedSSA := do
  if bytes.utf8ByteSize > 65536 then
    throw "certificate JSON exceeds 65536 bytes"
  let json ← Json.parse bytes
  if pythonCanonical 0 json ++ "\n" != bytes then
    throw "noncanonical certificate JSON bytes"
  fields json ["schema", "capability", "source_sha256", "relation_sha256",
    "ssa", "lean_semantic_profile", "unmodeled_features"]
  exactString (← field json "schema") "s31-source-relation-certificate-v1"
  exactString (← field json "capability") "source-to-relation-only"
  digest (← field json "source_sha256")
  digest (← field json "relation_sha256")
  exactString (← field json "lean_semantic_profile") "linear-ssa-m31-v1"
  let unmodeled ← array string (← field json "unmodeled_features")
  if !unmodeled.isEmpty then throw "unmodeled features are outside the Lean profile"
  ssa (← field json "ssa")

/-- The parser consumes actual certificate JSON bytes, and the semantic
checker independently rebuilds the selected source term from their `ssa`.
The caller still has to establish that the separately supplied `source`
term denotes the actual `.s31` source bytes. -/
def checkCertificate (bytes : String) (source : GeneralLinearSSA.Term) :
    Parse (EmittedSSA × Certificate) :=
  match decodeCertificate bytes with
  | .error message => .error message
  | .ok parsed =>
      match checkEmittedSSA parsed source with
      | some certificate => .ok (parsed, certificate)
      | none => .error "decoded SSA does not match source term"

theorem checked_certificate_parts (bytes : String) (source : GeneralLinearSSA.Term)
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

/-- A checked *certificate byte string* with an admitted source term has
the same arbitrary-witness soundness statement as the core theorem. -/
theorem certificate_bytes_air_sound (bytes : String) (source : GeneralLinearSSA.Term)
    (parsed : EmittedSSA) (certificate : Certificate)
    (inputs : Nat → Lanes parsed.lane_count)
    (claimed : Lanes parsed.lane_count)
    (final : List (Lanes parsed.lane_count))
    (hcheck : checkCertificate bytes source = .ok (parsed, certificate))
    (hrows : AcceptsTrace
      (initialValues certificate.inputs inputs)
      certificate.instructions final)
    (houtput : final[certificate.output]? = some claimed) :
    claimed = source.eval inputs :=
  emitted_ssa_air_sound parsed source certificate inputs claimed final
    (checked_certificate_parts bytes source parsed certificate hcheck).2
    hrows houtput

end S31.Functional.Correspondence.GeneralLinearSSABytes
