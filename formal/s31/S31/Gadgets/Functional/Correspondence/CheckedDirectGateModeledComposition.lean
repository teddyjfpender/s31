import S31.Gadgets.Functional.Correspondence.HonestConstantIslandAgreement
import S31.Gadgets.Functional.Correspondence.CheckedGateAddressLedger

/-!
The complete *modeled* direct-Gate composition under three executable checks:
exact source-byte admission, a checked constant island, and an exact bounded
fixed-address ledger. The latter takes explicit external feeder/sink addresses;
these lists must still be tied to a native public component. No theorem here
identifies modeled rows with committed native columns or proves PCS/FRI.
-/

namespace S31.Functional.Correspondence.CheckedDirectGateModeledComposition

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAPublicInputBinding
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.HonestConstantIslandAgreement
open S31.Functional.Correspondence.CheckedGateAddressLedger

/-- The three checks yield one coherent modeled 512-row witness for local
arithmetic, every selected fixed cell, the selected public result, and ideal
Gate event balance. The address ledger is a genuine Boolean premise, not a
restatement of `balanced`: its checker compares bounded fixed-address counts.
The external lists are not yet authenticated against the native package. -/
theorem checked_direct_full_modeled_trace
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes) (island : List ColumnCell) (values : List Quad)
    (externalUses externalYields : List Nat)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hledger : CheckedGateAddressLedger.check
      (joinedCells certificate island) externalUses externalYields = true) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      denotation sourceBytes input = some output ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island,
        fixedMatches (trace (joinedCells certificate island) wire) cell) ∧
      allArithmeticRootsZero (trace (joinedCells certificate island) wire) ∧
      wire (address certificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      InputBoundary certificate (compiledAddRows certificate) wire input ∧
      balanced (gateRows (joinedCells certificate island) wire)
        (wireEvents wire externalUses)
        (wireEvents wire externalYields) := by
  obtain ⟨wire, output, hdenotation, hlength, hcoverage, hfixed,
      harithmetic, hselected, hinput⟩ :=
    checked_direct_joined_local_arithmetic_no_agreement
      sourceBytes normalizedBytes certificate input island values hcheck hisland
  exact ⟨wire, output, hdenotation, hlength, hcoverage, hfixed,
    harithmetic, hselected, hinput,
    CheckedGateAddressLedger.check_sound
      (joinedCells certificate island) wire externalUses externalYields hledger⟩

/-- Literal-byte admission entry point for the full modeled composition.
Mapping `UInt8` values to `Nat` supplies the parser's canonical byte domain. -/
theorem checked_u8_direct_full_modeled_trace
    (sourceBytes normalizedBytes : List UInt8) (certificate : Certificate)
    (input : Lanes) (island : List ColumnCell) (values : List Quad)
    (externalUses externalYields : List Nat)
    (hcheck : checkRelation (sourceBytes.map UInt8.toNat)
      (normalizedBytes.map UInt8.toNat) = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hledger : CheckedGateAddressLedger.check
      (joinedCells certificate island) externalUses externalYields = true) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      denotation (sourceBytes.map UInt8.toNat) input = some output ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island,
        fixedMatches (trace (joinedCells certificate island) wire) cell) ∧
      allArithmeticRootsZero (trace (joinedCells certificate island) wire) ∧
      wire (address certificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      InputBoundary certificate (compiledAddRows certificate) wire input ∧
      balanced (gateRows (joinedCells certificate island) wire)
        (wireEvents wire externalUses)
        (wireEvents wire externalYields) :=
  checked_direct_full_modeled_trace
    (sourceBytes.map UInt8.toNat) (normalizedBytes.map UInt8.toNat)
    certificate input island values externalUses externalYields
    hcheck hisland hledger

end S31.Functional.Correspondence.CheckedDirectGateModeledComposition
