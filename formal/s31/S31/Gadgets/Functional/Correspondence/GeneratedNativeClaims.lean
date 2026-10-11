import S31.Gadgets.Functional.Correspondence.GeneratedMutationRows
import S31.Gadgets.Functional.Correspondence.AliasRawGateSoundness

/-!
The four generated direct-Gate native-proof samples also have source-bound
conditional raw Gate soundness claims. Unlike the general alias theorem, these
statements need no assumed source/normalized-byte relation: Lean checks its
exact bytes in `GeneratedMutationRows`. They still assume physical fixed cells,
all local arithmetic equations, ideal exact Gate balance, and public pins.
Native verifier acceptance and PCS/FRI authentication are not premises derived
here.
-/

namespace S31.Functional.Correspondence.GeneratedNativeClaims

open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSACertificate
open S31.Functional.SSAAliasTextBytes
open S31.Functional.Correspondence.RawGateSoundness
open S31.Functional.Correspondence.AliasRawGateSoundness
open S31.Functional.Correspondence.GeneratedMutationRows

private theorem checked_sample_claim (trace : Trace 9)
    (source normalized : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes)
    (hrelation : checkAliasRelation source normalized = some certificate)
    (hphysical : PhysicalTraceContext trace certificate totalAddRows input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    denotation source input = some claimed := by
  let hcontext : AliasFixedTraceContext trace source normalized certificate
      totalAddRows input claimed :=
    { hphysical with relation := hrelation }
  exact balanced_implies_alias_claim trace source normalized certificate
    totalAddRows input claimed hcontext hbalance

theorem case00_source_claim (trace : Trace 9) (totalAddRows : Nat)
    (input claimed : Lanes)
    (hphysical : PhysicalTraceContext trace case00Certificate totalAddRows
      input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    denotation case00Bytes input = some claimed := by
  exact checked_sample_claim trace case00Bytes case00NormalizedBytes
    case00Certificate totalAddRows input claimed
    case00NormalizedChecks.1 hphysical hbalance

theorem case07_source_claim (trace : Trace 9) (totalAddRows : Nat)
    (input claimed : Lanes)
    (hphysical : PhysicalTraceContext trace case07Certificate totalAddRows
      input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    denotation case07Bytes input = some claimed := by
  exact checked_sample_claim trace case07Bytes case07NormalizedBytes
    case07Certificate totalAddRows input claimed
    case07NormalizedChecks.1 hphysical hbalance

theorem case14_source_claim (trace : Trace 9) (totalAddRows : Nat)
    (input claimed : Lanes)
    (hphysical : PhysicalTraceContext trace case14Certificate totalAddRows
      input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    denotation case14Bytes input = some claimed := by
  exact checked_sample_claim trace case14Bytes case14NormalizedBytes
    case14Certificate totalAddRows input claimed
    case14NormalizedChecks.1 hphysical hbalance

theorem case16_source_claim (trace : Trace 9) (totalAddRows : Nat)
    (input claimed : Lanes)
    (hphysical : PhysicalTraceContext trace case16Certificate totalAddRows
      input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    denotation case16Bytes input = some claimed := by
  exact checked_sample_claim trace case16Bytes case16NormalizedBytes
    case16Certificate totalAddRows input claimed
    case16NormalizedChecks.1 hphysical hbalance

end S31.Functional.Correspondence.GeneratedNativeClaims
