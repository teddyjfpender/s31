import S31.Gadgets.Functional.SSAAliasTextBytes
import S31.Gadgets.Functional.SSAGeneralDecodedTraceBridge

/-!
The alias byte parser is kept independent of AIR modules so its executable
audit checker does not link the full AIR evaluator. This module adds the one
physical input-use fact needed by the Gate soundness bridge.
-/

namespace S31.Functional.SSAAliasTextBytes

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes

private theorem parsed_alias_nonempty (bytes : List Nat) (parsed : Parsed)
    (hparse : parseAliasBytes bytes = some parsed) :
    parsed.certificate.instructions ≠ [] := by
  simp [parseAliasBytes, Option.bind] at hparse
  repeat (split at hparse <;> simp_all)
  rcases hparse with ⟨_, _, _, _, hnonempty, _, _, hparsed⟩
  intro hnil
  exact hnonempty ((congrArg (fun p : Parsed => p.certificate.instructions)
    hparsed).trans hnil)

/-- Even when aliases precede the first producer, a successful byte and
normalized-relation check has a positive use count for its sole public input.
This discharges the input-pack multiplicity premise of the raw row bridge. -/
theorem checked_alias_relation_source_input_used
    (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate)
    (hrelation : checkAliasRelation sourceBytes normalizedBytes = some certificate) :
    0 < SSAInputAirCells.sourceInputUses certificate := by
  unfold checkAliasRelation at hrelation
  cases hsource : parseAliasBytes sourceBytes with
  | none => simp [hsource] at hrelation
  | some parsed =>
      cases hencoded : SSANormalizedBytes.encodeNormalized parsed with
      | none => simp [hsource, hencoded] at hrelation
      | some expected =>
          by_cases hmatch : expected = normalizedBytes
          · have hcertificate : parsed.certificate = certificate := by
              simpa [hsource, hencoded, hmatch] using hrelation
            subst certificate
            exact SSAGeneralDecodedTraceBridge.source_input_used_of_checked_nonempty
              parsed.certificate parsed.meaning parsed.checked
              (parsed_alias_nonempty sourceBytes parsed hsource)
          · simp [hsource, hencoded, hmatch] at hrelation

end S31.Functional.SSAAliasTextBytes
