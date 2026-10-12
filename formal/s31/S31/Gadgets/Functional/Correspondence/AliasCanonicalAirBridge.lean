import S31.Gadgets.Functional.Correspondence.AliasCanonicalIrBytes
import S31.Gadgets.Functional.Correspondence.AliasRawGateSoundness

/-!
Compose the exact source/relation/canonical-IR byte admission with the
conditional physical Gate soundness theorem. Kept separate from the byte
checker so the optional executable audit need not link AIR evaluators.
-/

namespace S31.Functional.Correspondence.AliasCanonicalIrBytes

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.Correspondence.RawGateSoundness
open S31.Functional.Correspondence.AliasRawGateSoundness
open S31.Functional.SSAGeneralDecodedTraceBridge

set_option maxRecDepth 2048 in
/-- Canonical-IR admission supplies the exact alias relation premise of the
arbitrary-trace Gate balance theorem. Physical trace and ideal Gate balance
remain explicit premises; this theorem does not assert that a native verifier
has authenticated or checked them. -/
theorem canonical_alias_balanced_implies_claim
    (trace : Trace 9) (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (totalAddRows : Nat) (input claimed : Lanes)
    (hphysical : PhysicalTraceContext trace certificate totalAddRows
      input claimed)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    SSAAliasTextBytes.denotation sourceBytes input = some claimed := by
  obtain ⟨_, _, _, _, _, hrelation, _⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate input hcheck
  let context : AliasFixedTraceContext trace sourceBytes normalizedBytes
      certificate totalAddRows input claimed := ⟨hphysical, hrelation⟩
  exact balanced_implies_alias_claim trace sourceBytes normalizedBytes
    certificate totalAddRows input claimed context hbalance

end S31.Functional.Correspondence.AliasCanonicalIrBytes
