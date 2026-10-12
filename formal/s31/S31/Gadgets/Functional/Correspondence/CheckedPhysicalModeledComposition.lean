import S31.Gadgets.Functional.Correspondence.CheckedDirectGateModeledComposition
import S31.Gadgets.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence

/-!
One final synthetic direct-Gate trace carries the complete physical row
roster, local arithmetic, selected output, and its own Gate external events.
The three executable source/island/ledger checks are explicit premises.
Production compiler emission, native feeder binding, interaction arguments,
and PCS/FRI verification are outside this model theorem.
-/

namespace S31.Functional.Correspondence.CheckedPhysicalModeledComposition

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
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.CheckedGateAddressLedger
open S31.Functional.Correspondence.CheckedDirectGateModeledComposition
open S31.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence

/-- The modeled witness has a single physical trace whose own decoded rows
and external fields satisfy ideal Gate balance, while all installed local
arithmetic roots vanish. The three Boolean checks remain conditional; this
does not establish native proof acceptance or verifier soundness. -/
theorem checked_u8_physical_modeled_trace
    (sourceBytes normalizedBytes : List UInt8) (certificate : Certificate)
    (input : Lanes) (island : List ColumnCell) (values : List Quad)
    (externalUses externalYields : List Nat)
    (hcheck : checkRelation (sourceBytes.map UInt8.toNat)
      (normalizedBytes.map UInt8.toNat) = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hledger : CheckedGateAddressLedger.check
      (joinedCells certificate island) externalUses externalYields = true) :
    ∃ (wire : Nat → Quad) (output : Lanes) (physical : Trace 9),
      denotation (sourceBytes.map UInt8.toNat) input = some output ∧
      physical = traceWithExternal (joinedCells certificate island) wire
        externalUses externalYields ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island, fixedMatches physical cell) ∧
      allArithmeticRootsZero physical ∧
      wire (address certificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      InputBoundary certificate (compiledAddRows certificate) wire input ∧
      balanced (nativeRows physical) physical.externalUses
        physical.externalYields := by
  obtain ⟨wire, output, hdenotation, hlength, hcoverage, hfixed,
      harithmetic, hselected, hinput, _⟩ :=
    checked_u8_direct_full_modeled_trace sourceBytes normalizedBytes
      certificate input island values externalUses externalYields
      hcheck hisland hledger
  let physical := traceWithExternal (joinedCells certificate island) wire
    externalUses externalYields
  have hfixedPhysical : ∀ cell ∈ joinedCells certificate island,
      fixedMatches physical cell := by
    intro cell hcell
    simpa [physical, traceWithExternal] using hfixed cell hcell
  have harithmeticPhysical : allArithmeticRootsZero physical := by
    simpa [physical, traceWithExternal] using harithmetic
  have hbalance : balanced (nativeRows physical) physical.externalUses
      physical.externalYields := by
    simpa [physical] using
      checked_joined_trace_gate_balance
        (sourceBytes.map UInt8.toNat) (normalizedBytes.map UInt8.toNat)
        certificate island values wire externalUses externalYields
        hcheck hisland hledger
  exact ⟨wire, output, physical, hdenotation, rfl, hlength, hcoverage,
    hfixedPhysical, harithmeticPhysical, hselected, hinput, hbalance⟩

end S31.Functional.Correspondence.CheckedPhysicalModeledComposition
