import S31.Gadgets.Functional.SSANormalizedBytes

/-!
The byte identity of Zig `canonical.build` for the deliberately bounded
one-input, add/mul SSA fragment. This models the legacy `Node` serialization
selected by the production compiler when there are no selector or index nodes.
The source grammar excludes constants, repeated expressions, noncanonical
operand order and other operations, so canonicalization retains one node per
source let. Zig and Python are checked against this model by generated fixture
instances and the independent package checker; this file alone does not prove
either implementation of JSON serialization or SHA-256 correct.

The canonical IR deliberately excludes the circuit name and local let names.
It includes the public input name and selected output name and ID. The
`-Ds31-version` build option is a backend selector and is not the normalized
relation's `version` field, which is exactly 1 here.
-/

namespace S31.Functional.SSACanonicalIrBytes

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes

/-- The exact `LegacyNode` field order, including optional null fields. -/
def inputNode (name : Token) : Token :=
  token "{\"tag\":\"input\",\"kind\":\"m31\",\"length\":4,\"lhs\":null,\"rhs\":null," ++
  token "\"constant\":null,\"rounds\":null,\"body\":null,\"input_name\":\"" ++
  name ++ token "\",\"visibility\":\"public\"}"

def instructionNode (instruction : Instruction) : Token :=
  token "{\"tag\":\"" ++
  (if instruction.multiply then token "mul" else token "add") ++
  token "\",\"kind\":\"m31\",\"length\":4,\"lhs\":" ++
  token (toString instruction.lhs) ++ token ",\"rhs\":" ++
  token (toString instruction.rhs) ++
  token ",\"constant\":null,\"rounds\":null,\"body\":null," ++
  token "\"input_name\":null,\"visibility\":null}"

def joinNodes : List Token → Token
  | [] => []
  | [node] => node
  | node :: rest => node ++ token "," ++ joinNodes rest

/-- Exact compact bytes hashed by the transparent v1 `canonical.build` path.
This is an encoder, so equality to captured bytes is a fully decidable check. -/
def encodeCanonical (parsed : Parsed) : Token :=
  token "{\"version\":1,\"nodes\":[" ++ inputNode parsed.inputName ++
  token "," ++ joinNodes
    (parsed.certificate.instructions.map instructionNode) ++
  token "],\"assertions\":[],\"public_outputs\":[{\"name\":\"" ++
  parsed.outputName ++ token "\",\"id\":" ++
  token (toString parsed.certificate.output) ++ token "}]}"

/-- Source bytes, normalized relation bytes and the compact canonical IR
bytes must all identify the same checked positional SSA. -/
def checkCanonical (sourceBytes normalizedBytes canonicalBytes : Token) :
    Option Certificate := do
  let certificate ← checkRelation sourceBytes normalizedBytes
  let parsed ← parseBytes sourceBytes
  if encodeCanonical parsed != canonicalBytes then none else some certificate

theorem checked_canonical_bytes_sound
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    checkRelation sourceBytes normalizedBytes = some certificate ∧
    (∃ parsed, parseBytes sourceBytes = some parsed ∧
      canonicalBytes = encodeCanonical parsed) ∧
    executeNormalized certificate input = denotation sourceBytes input := by
  unfold checkCanonical at hcheck
  cases hrelation : checkRelation sourceBytes normalizedBytes with
  | none => simp [hrelation] at hcheck
  | some accepted =>
      cases hparsed : parseBytes sourceBytes with
      | none => simp [hrelation, hparsed] at hcheck
      | some parsed =>
          by_cases hbytes : encodeCanonical parsed = canonicalBytes
          · have hcertificate : accepted = certificate := by
              simpa [hrelation, hparsed, hbytes] using hcheck
            subst accepted
            exact ⟨hrelation, ⟨parsed, hparsed, hbytes.symm⟩,
              checked_relation_sound sourceBytes normalizedBytes certificate
                input hrelation⟩
          · simp [hrelation, hparsed, hbytes] at hcheck

end S31.Functional.SSACanonicalIrBytes
