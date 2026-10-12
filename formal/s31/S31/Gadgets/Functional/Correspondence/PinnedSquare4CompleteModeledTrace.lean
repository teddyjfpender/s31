import S31.Gadgets.Functional.Correspondence.CheckedPhysicalModeledComposition
import S31.Gadgets.Functional.Correspondence.PinnedSquare4ConstantIslandCertificate
import S31.Gadgets.Functional.GeneratedDirectGateBridge

/-!
Discharge all three executable premises of the complete modeled-trace theorem
for the checked-in `functional_square4` source and native fixed island. This is
an honest *synthetic* witness for every four-lane input. It does not identify
that witness with any committed native proof opening or establish STARK
soundness.
-/

namespace S31.Functional.Correspondence.PinnedSquare4CompleteModeledTrace

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAPublicInputBinding
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.PinnedSquare4ConstantIslandCertificate
open S31.Functional.Correspondence.CheckedGateAddressLedger
open S31.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence
open S31.Functional.Correspondence.CheckedPhysicalModeledComposition

set_option maxRecDepth 16384
set_option maxHeartbeats 10000000

def sourceBytes : List UInt8 :=
  S31.Functional.GeneratedDirectGateBridge.sourceBytes.map UInt8.ofNat

def normalizedBytes : List UInt8 :=
  S31.Functional.GeneratedDirectGateBridge.normalizedBytes.map UInt8.ofNat

private theorem source_roundtrip :
    sourceBytes.map UInt8.toNat =
      S31.Functional.GeneratedDirectGateBridge.sourceBytes := by decide

private theorem normalized_roundtrip :
    normalizedBytes.map UInt8.toNat =
      S31.Functional.GeneratedDirectGateBridge.normalizedBytes := by decide

private theorem admitted_source :
    checkRelation (sourceBytes.map UInt8.toNat)
      (normalizedBytes.map UInt8.toNat) = some squareCertificate := by
  rw [source_roundtrip, normalized_roundtrip]
  exact S31.Functional.GeneratedDirectGateBridge.normalized_bytes_check

/-- Exact address multiplicities of the source, public cells, and 485 checked
constant cells close with the nine public feeder addresses. This finite check
does not authenticate a native proof's external events. -/
theorem complete_address_check :
    CheckedGateAddressLedger.check
      (joinedCells squareCertificate constantCells)
      [2, 3, 4, 5, 6, 7, 8, 9, 10] [] = true := by decide

/-- Literal source and normalized bytes have a coherent 512-row physical
model for every input. Every installed local arithmetic root is zero and the
trace's own *ideal* Gate events balance. Native commitment and PCS/FRI
correspondence remain separate obligations. -/
theorem complete_modeled_trace (input : Lanes) :
    ∃ (wire : Nat → Quad) (output : Lanes) (physical : Trace 9),
      denotation (sourceBytes.map UInt8.toNat) input = some output ∧
      physical = traceWithExternal (joinedCells squareCertificate constantCells)
        wire [2, 3, 4, 5, 6, 7, 8, 9, 10] [] ∧
      (joinedCells squareCertificate constantCells).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells squareCertificate constantCells,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells squareCertificate constantCells,
        fixedMatches physical cell) ∧
      allArithmeticRootsZero physical ∧
      wire (address squareCertificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      InputBoundary squareCertificate (compiledAddRows squareCertificate)
        wire input ∧
      balanced (nativeRows physical) physical.externalUses
        physical.externalYields := by
  exact checked_u8_physical_modeled_trace sourceBytes normalizedBytes
    squareCertificate input constantCells nativeValues
    [2, 3, 4, 5, 6, 7, 8, 9, 10] []
    admitted_source pinned_square4_constant_check complete_address_check

end S31.Functional.Correspondence.PinnedSquare4CompleteModeledTrace
