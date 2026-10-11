import S31.Gadgets.Functional.Correspondence.CheckedFullLocalArithmeticComposition
import S31.Gadgets.Functional.Correspondence.CheckedGateAddressLedger

/-!
The final model-level join for a bounded direct Gate source: exact 512-row
coverage, selected fixed cells, all installed local arithmetic roots, and
ideal Gate event balance under one coherent address-to-QM31 wire assignment.
The event result follows from an executable bounded address ledger check,
which remains an explicit premise for arbitrary accepted sources. This module
does not prove production commitment binding, LogUp soundness or PCS/FRI.
-/

namespace S31.Functional.Correspondence.CheckedFullGateBalanceComposition

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
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.CheckedGateAddressLedger

/-- A checked address ledger lifts the completed local arithmetic witness to
ideal exact Gate event balance for the *same* merged address-coherent wire.
The two external address lists must be bound to the actual public component
by a separate native-package or verifier correspondence proof. -/
theorem joined_local_arithmetic_and_gate_balance_of_projected_wire
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes) (island : List ColumnCell) (values : List Quad)
    (projectedWire : Nat → Quad) (output : Lanes)
    (externalUses externalYields : List Nat)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hdenotation : denotation sourceBytes input = some output)
    (hsource : nativePolynomialRows certificate projectedWire)
    (hinput : InputBoundary certificate (compiledAddRows certificate)
      projectedWire input)
    (houtput : OutputBoundary certificate (compiledAddRows certificate)
      projectedWire output)
    (hselected : projectedWire (address certificate.output) =
      S31.Gadgets.Air.Qm31Ops.packM31 output)
    (hunit : projectedWire 1 = unit ⟨0, by decide⟩)
    (hshared : SharedAgreement certificate projectedWire values)
    (hledger : CheckedGateAddressLedger.check
      (joinedCells certificate island) externalUses externalYields = true) :
    ∃ wire : Nat → Quad,
      denotation sourceBytes input = some output ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island,
        fixedMatches (trace (joinedCells certificate island) wire) cell) ∧
      allArithmeticRootsZero (trace (joinedCells certificate island) wire) ∧
      wire (address certificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      balanced (gateRows (joinedCells certificate island) wire)
        (wireEvents wire externalUses)
        (wireEvents wire externalYields) := by
  obtain ⟨wire, hdenotation, hlength, hcoverage, hfixed,
      harithmetic, hselected⟩ :=
    joined_local_arithmetic_of_projected_wire sourceBytes normalizedBytes
      certificate input island values projectedWire output hcheck hisland
      hdenotation hsource hinput houtput hselected hunit hshared
  exact ⟨wire, hdenotation, hlength, hcoverage, hfixed, harithmetic,
    hselected, check_sound (joinedCells certificate island) wire
      externalUses externalYields hledger⟩

end S31.Functional.Correspondence.CheckedFullGateBalanceComposition
