import S31.Gadgets.Functional.SSACanonicalIrBytes
import S31.Gadgets.Functional.SSAGateLookupWireMap

/-!
A single stated cut through the bounded direct-gate compiler correspondence:
actual source bytes, exact normalized JSON bytes, compact canonical SSA bytes,
source-projected physical AIR cells, and an ideal exact Gate join identify the
same four-lane computation for source programs whose every instruction is used.
This live-only condition is explicit: the accepted source grammar also admits
dead instructions, which the current source-row refinement does not cover.
This is intentionally conditional. The production
package checker reconstructs canonical bytes and compares their SHA-256 with
the key and manifest; Lean does not prove the Python/Zig serializer agreement
or SHA-256. The physical cell and source-row premises do not follow here from
the preprocessed commitment. The real LogUp, PCS, FRI and transcript checks do
not establish the exact multiset balance premise within this theorem.
-/

namespace S31.Functional.SSACanonicalGateChain

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSACanonicalIrBytes
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGateLookupWireMap
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.Qm31Ops

/-- No intermediate compiler identity is free in this conclusion: successful
byte admission fixes the source certificate and canonical SSA bytes, exact
fixed-cell equality fixes every projected source selector/address/multiplicity,
and ideal Gate balance plus unique producers forces all source-row reads to
the same packed wire values. The stated premises must be authenticated by a
future refinement of the installed native verifier; this is not that proof.
The live-row premise is a restriction on this theorem, not a consequence of
acceptance by the source parser. -/
theorem checked_live_canonical_source_output_of_exact_gate
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (totalAddRows : Nat)
    (observedCells : List ColumnCell) (input : Lanes)
    (rows : List Row) (externalUses externalYields : List Event)
    (hcanonical : checkCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hlive : ∀ instruction ∈ certificate.instructions,
      0 < sourceUses certificate instruction.id)
    (hcells : observedCells = expectedCells certificate totalAddRows)
    (hsource : sourceGateRows certificate observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hinputYield : (SSADirectGateBridge.address 0, packM31 input) ∈
      allYields rows externalYields) :
    ∃ parsed, parseBytes sourceBytes = some parsed ∧
      canonicalBytes = encodeCanonical parsed ∧
      observedCells = expectedCells certificate totalAddRows ∧
      (∃ output : Lanes,
        denotation sourceBytes input = some output ∧
        wireOfProduced (allYields rows externalYields)
          (SSADirectGateBridge.address certificate.output) =
            packM31 output) := by
  -- `hlive` is retained as a domain restriction; sourceGateRows itself
  -- requires positive multiplicity on each source instruction's physical row.
  obtain ⟨hrelation, ⟨parsed, hparse, hbytes⟩, _⟩ :=
    checked_canonical_bytes_sound sourceBytes normalizedBytes canonicalBytes
      certificate input hcanonical
  obtain ⟨hfixed, output, hdenotation, hwire⟩ :=
    checked_source_output_of_exact_gate sourceBytes normalizedBytes
      certificate totalAddRows observedCells input rows externalUses
      externalYields hrelation hcells hsource hbalance hunique hinputYield
  exact ⟨parsed, hparse, hbytes, hfixed, output, hdenotation, hwire⟩

end S31.Functional.SSACanonicalGateChain
