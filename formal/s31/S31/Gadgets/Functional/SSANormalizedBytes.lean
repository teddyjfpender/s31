import S31.Gadgets.Functional.SSATextBytes

/-!
An exact byte encoder for the canonical normalized JSON relation of the
bounded direct-gate source grammar. This is deliberately a byte equality
check, not a permissive JSON parser: field order, whitespace, names, node
order, operations, visibility, lengths, outputs, and version must all match.
The production package checker separately checks that these are the actual
package bytes. This model does not prove the Python serializer or Zig JSON
parser correct, and does not authenticate committed AIR columns.
-/

namespace S31.Functional.SSANormalizedBytes

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes

def encodeNode (names : List Token) (instruction : Instruction) : Option Token := do
  let lhs ← names[instruction.lhs]?
  let name ← names[instruction.id]?
  let rhs ← names[instruction.rhs]?
  let operation := if instruction.multiply then token "mul" else token "add"
  return token "    {\n      \"lhs\": \"" ++ lhs ++
    token "\",\n      \"name\": \"" ++ name ++
    token "\",\n      \"op\": \"" ++ operation ++
    token "\",\n      \"rhs\": \"" ++ rhs ++ token "\"\n    }"

def joinNodes : List Token → Token
  | [] => []
  | [node] => node
  | node :: rest => node ++ token ",\n" ++ joinNodes rest

def encodeNormalized (parsed : Parsed) : Option Token := do
  let nodes ← parsed.certificate.instructions.mapM (encodeNode parsed.wireNames)
  return token "{\n  \"assertions\": [],\n  \"inputs\": [\n    {\n      \"kind\": \"m31\",\n      \"length\": 4,\n      \"name\": \"" ++
    parsed.inputName ++
    token "\",\n      \"visibility\": \"public\"\n    }\n  ],\n  \"name\": \"" ++
    parsed.circuitName ++
    token "\",\n  \"nodes\": [\n" ++ joinNodes nodes ++
    token "\n  ],\n  \"public_outputs\": [\n    \"" ++
    parsed.outputName ++
    token "\"\n  ],\n  \"version\": 1\n}\n"

/-- A single executable check binds the exact source bytes and exact
normalized relation bytes to the same positional certificate. -/
def checkRelation (sourceBytes normalizedBytes : List Nat) : Option Certificate := do
  let parsed ← parseBytes sourceBytes
  let expected ← encodeNormalized parsed
  if expected != normalizedBytes then none else some parsed.certificate

/-- Once the exact normalized bytes have passed this check, the checked
certificate computes the source-byte denotation on every four-lane input.
This is the semantic consequence of the byte check, not an AIR/PCS theorem. -/
theorem checked_relation_sound (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    executeNormalized certificate input = denotation sourceBytes input := by
  unfold checkRelation at hcheck
  cases hsource : parseBytes sourceBytes with
  | none => simp [hsource] at hcheck
  | some parsed =>
      cases hencoded : encodeNormalized parsed with
      | none => simp [hsource, hencoded] at hcheck
      | some expected =>
          by_cases hmatch : expected = normalizedBytes
          · have hcertificate : parsed.certificate = certificate := by
              simpa [hsource, hencoded, hmatch] using hcheck
            subst certificate
            exact parsed_bytes_normalized_sound sourceBytes input parsed hsource
          · simp [hsource, hencoded, hmatch] at hcheck

end S31.Functional.SSANormalizedBytes
