import S31.Gadgets.Functional.SSAAliasTextBytes
import S31.Gadgets.Functional.SSACanonicalIrBytes

/-!
Exact canonical-IR byte identity for the bounded direct-Gate source grammar
with zero-cost aliases and redundant parentheses. The checker parses source
bytes once, compares the pretty normalized relation bytes, and compares the
compact legacy canonical IR bytes. Both outputs are encoded from the same
producer-only `Parsed` value. An output alias resolves to its producer's name
and ID before either encoding.

This is a Lean byte-level model. The physical AIR composition lives in
`AliasCanonicalAirBridge` so the executable byte audit has a small dependency
closure. Python's serializer, Zig's `canonical.build`, the native verifier,
and SHA-256 require separate differential and native checks.
-/

namespace S31.Functional.Correspondence.AliasCanonicalIrBytes

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSAAliasTextBytes

/-- A single parsed producer graph determines both serialized identities. -/
def checkAliasCanonical (sourceBytes normalizedBytes canonicalBytes : Token) :
    Option Certificate := do
  let parsed ← parseAliasBytes sourceBytes
  let expectedNormalized ← SSANormalizedBytes.encodeNormalized parsed
  if expectedNormalized != normalizedBytes then none else
  if SSACanonicalIrBytes.encodeCanonical parsed != canonicalBytes then none
  else some parsed.certificate

/-- Admission binds all three exact byte strings to one parsed certificate.
In particular, source-level output aliases do not become an extra output
node: the selected name and ID are those of the original producer. -/
theorem checked_alias_canonical_bytes_sound
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ∃ parsed : Parsed,
      parseAliasBytes sourceBytes = some parsed ∧
      SSANormalizedBytes.encodeNormalized parsed = some normalizedBytes ∧
      SSACanonicalIrBytes.encodeCanonical parsed = canonicalBytes ∧
      parsed.certificate = certificate ∧
      checkAliasRelation sourceBytes normalizedBytes = some certificate ∧
      executeNormalized certificate input =
        SSAAliasTextBytes.denotation sourceBytes input := by
  unfold checkAliasCanonical at hcheck
  cases hsource : parseAliasBytes sourceBytes with
  | none => simp [hsource] at hcheck
  | some parsed =>
      cases hnormalized : SSANormalizedBytes.encodeNormalized parsed with
      | none => simp [hsource, hnormalized] at hcheck
      | some expectedNormalized =>
          by_cases hnormEq : expectedNormalized = normalizedBytes
          · by_cases hirEq : SSACanonicalIrBytes.encodeCanonical parsed =
                canonicalBytes
            · have hcertificate : parsed.certificate = certificate := by
                simpa [hsource, hnormalized, hnormEq, hirEq] using hcheck
              refine ⟨parsed, ?_, ?_, hirEq, hcertificate, ?_, ?_⟩
              · rfl
              · simpa [hnormEq] using hnormalized
              · simp [checkAliasRelation, hsource, hnormalized, hnormEq,
                  hcertificate]
              · subst certificate
                exact parsed_alias_bytes_normalized_sound sourceBytes input
                  parsed hsource
            · simp [hsource, hnormalized, hnormEq, hirEq] at hcheck
          · simp [hsource, hnormalized, hnormEq] at hcheck

/-- Canonical IR is unique for a checked source/relation pair. -/
theorem accepted_alias_ir_unique
    (sourceBytes normalizedBytes first second : Token)
    (certificate : Certificate)
    (hfirst : checkAliasCanonical sourceBytes normalizedBytes first =
      some certificate)
    (hsecond : checkAliasCanonical sourceBytes normalizedBytes second =
      some certificate) :
    first = second := by
  obtain ⟨parsed1, hp1, _, hir1, _, _, _⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes first
      certificate (fun _ => 0) hfirst
  obtain ⟨parsed2, hp2, _, hir2, _, _, _⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes second
      certificate (fun _ => 0) hsecond
  have heq : parsed1 = parsed2 := by
    simpa [hp1] using hp2
  subst parsed2
  exact hir1.symm.trans hir2

set_option maxRecDepth 2048 in
/-- Aliases and redundant parentheses preserve the canonical IR of the
equivalent producer-only spelling, including the producer output name. -/
theorem alias_square_canonical_ir_matches_direct :
    (parseAliasBytes aliasSquareSource).map
      SSACanonicalIrBytes.encodeCanonical =
    (parseBytes directSquareSource).map
      SSACanonicalIrBytes.encodeCanonical := by
  decide

set_option maxRecDepth 2048 in
def aliasSquareParsed : Parsed :=
  (parseAliasBytes aliasSquareSource).get (by decide)

set_option maxRecDepth 2048 in
def aliasSquareNormalized : Token :=
  (SSANormalizedBytes.encodeNormalized aliasSquareParsed).get (by decide)

def aliasSquareCanonical : Token :=
  SSACanonicalIrBytes.encodeCanonical aliasSquareParsed

set_option maxRecDepth 2048 in
/-- The concrete alias program parses, resolves its final `returned` alias
to producer `result` at ID 2, and emits only two arithmetic producers. -/
theorem alias_square_output_alias_resolved :
    parseAliasBytes aliasSquareSource = some aliasSquareParsed ∧
    aliasSquareParsed.outputName = token "result" ∧
    aliasSquareParsed.certificate.output = 2 ∧
    aliasSquareParsed.certificate.instructions.length = 2 := by
  have hprojection : (parseAliasBytes aliasSquareSource).map
      (fun p => (p.outputName, p.certificate.output,
        p.certificate.instructions.length)) =
        some (token "result", 2, 2) := by decide
  have hsource : parseAliasBytes aliasSquareSource =
      some aliasSquareParsed := by
    cases h : parseAliasBytes aliasSquareSource with
    | none => simp [h] at hprojection
    | some parsed => simp [aliasSquareParsed, h]
  simp only [hsource, Option.map_some] at hprojection
  have hfields := Option.some.inj hprojection
  simp only [Prod.mk.injEq] at hfields
  exact ⟨hsource, hfields.1, hfields.2.1, hfields.2.2⟩

set_option maxRecDepth 2048 in
/-- The concrete alias program is admitted with exactly its independently
encoded normalized relation and canonical IR bytes. -/
theorem alias_square_exact_ir_accepted :
    checkAliasCanonical aliasSquareSource aliasSquareNormalized
      aliasSquareCanonical = some aliasSquareParsed.certificate := by
  decide

set_option maxRecDepth 2048 in
/-- A changed canonical IR byte is rejected even when source and normalized
relation bytes are the admitted alias square program. -/
theorem alias_square_wrong_ir_rejected :
    checkAliasCanonical aliasSquareSource aliasSquareNormalized
      (aliasSquareCanonical ++ token " ") = none := by
  decide

end S31.Functional.Correspondence.AliasCanonicalIrBytes
