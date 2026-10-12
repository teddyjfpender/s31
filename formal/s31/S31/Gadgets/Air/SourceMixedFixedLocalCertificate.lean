import S31.Gadgets.Air.SourceMixedFixedProducerCertificate
import S31.Gadgets.Air.SourceMixedFixedOutputSchedule

/-!
Assemble the source-pinned N1/N8 `LocalPublicSchedule` from complete native
fixed-column exports. Fixed rows supply the selected Gate schedule, full
producer-address scan, and all-row address range. The only remaining inputs
are source/trace identity and main-value facts: canonical call addresses,
source constants and first state, packed initial/final values, zero, and the
unpack basis constants. These inputs are not inferred from a JSON descriptor
or an unauthenticated proof header.
-/

namespace S31.Gadgets.Air.SourceMixedFixedLocalCertificate

open S31.Gadgets.Packed
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAddressSchedule
open S31.Gadgets.Air.SourceMixedPublicClosure
open S31.Gadgets.Air.SourceMixedScheduledPublicPath
open S31.Gadgets.Air.SourceMixedFixedScheduleBridge
open S31.Gadgets.Air.SourceMixedFixedProducerCertificate
open S31.Gadgets.Air.SourceMixedFixedOutputSchedule
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.UnpackRows
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.GeneratedMixedFixedRows

/-- Complete N1 schedule from fixed rows and separately named source-value
facts. The `rows` argument is the native chip-row family used by the later
authenticated trace theorem, not an independently assumed Gate schedule. -/
theorem n1_local_schedule (boundary : Boundary 1)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (hbaseline : boundary.baselineYields = [])
    (haddresses : ∀ call slot,
      boundary.addresses call slot =
        canonicalAddress (by decide : 1 ≤ 8) call slot)
    (hfirst : boundary.start ⟨0, by decide⟩ = initial)
    (hconstants : ∀ call, boundary.constants call = (13 + call.val : F))
    (hpackedInitial : ValueAt boundary 22 (packState initial))
    (hpackedFinal : ValueAt boundary (22 + 10 * 1)
      (packState (boundary.finish ⟨1 - 1, by omega⟩)))
    (hzero : ValueAt boundary 0 (base 0))
    (hunit : ∀ lane, ValueAt boundary (unitAddress lane) (unit lane))
    (hinverse : ∀ lane, lane.val ≠ 0 →
      ValueAt boundary (inverseAddress 1 lane) (unitInverse lane)) :
    LocalPublicSchedule (by decide : 1 ≤ 8) (by decide : 0 < 1)
      boundary rows initial := by
  obtain ⟨hadd, hmul⟩ := n1_tail_scheduled boundary trace hfixed hrows
  exact {
    addresses := haddresses
    producerScan := n1_producer_scan boundary trace hfixed hrows hbaseline
    rowAddressRange := n1_row_address_range boundary trace hfixed hrows
    first := hfirst
    constants := hconstants
    packedInitial := hpackedInitial
    packedFinal := hpackedFinal
    zero := hzero
    add := hadd
    mul := hmul
    outputs := n1_outputs_scheduled boundary trace hfixed hrows hunit hinverse
  }

/-- Complete N8 schedule under the corresponding source-value facts. -/
theorem n8_local_schedule (boundary : Boundary 8)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (hbaseline : boundary.baselineYields = [])
    (haddresses : ∀ call slot,
      boundary.addresses call slot =
        canonicalAddress (by decide : 8 ≤ 8) call slot)
    (hfirst : boundary.start ⟨0, by decide⟩ = initial)
    (hconstants : ∀ call, boundary.constants call = (13 + call.val : F))
    (hpackedInitial : ValueAt boundary 22 (packState initial))
    (hpackedFinal : ValueAt boundary (22 + 10 * 8)
      (packState (boundary.finish ⟨8 - 1, by omega⟩)))
    (hzero : ValueAt boundary 0 (base 0))
    (hunit : ∀ lane, ValueAt boundary (unitAddress lane) (unit lane))
    (hinverse : ∀ lane, lane.val ≠ 0 →
      ValueAt boundary (inverseAddress 8 lane) (unitInverse lane)) :
    LocalPublicSchedule (by decide : 8 ≤ 8) (by decide : 0 < 8)
      boundary rows initial := by
  obtain ⟨hadd, hmul⟩ := n8_tail_scheduled boundary trace hfixed hrows
  exact {
    addresses := haddresses
    producerScan := n8_producer_scan boundary trace hfixed hrows hbaseline
    rowAddressRange := n8_row_address_range boundary trace hfixed hrows
    first := hfirst
    constants := hconstants
    packedInitial := hpackedInitial
    packedFinal := hpackedFinal
    zero := hzero
    add := hadd
    mul := hmul
    outputs := n8_outputs_scheduled boundary trace hfixed hrows hunit hinverse
  }

end S31.Gadgets.Air.SourceMixedFixedLocalCertificate
