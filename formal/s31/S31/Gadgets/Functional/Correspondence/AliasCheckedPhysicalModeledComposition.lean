import S31.Gadgets.Functional.Correspondence.CheckedPhysicalModeledComposition
import S31.Gadgets.Functional.Correspondence.AliasCanonicalIrBytes

/-!
Transport the checked complete direct-Gate physical model to an alias source
whose producer-only spelling has been separately checked to yield the same
certificate. This extra spelling is an explicit certificate premise. It is
not a theorem that the native compiler implements either Lean parser, and it
does not authenticate STARK openings or discharge PCS/FRI soundness.
-/

namespace S31.Functional.Correspondence.AliasCheckedPhysicalModeledComposition

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.CheckedGateAddressLedger
open S31.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.CheckedPhysicalModeledComposition

/-- Two exact source-byte checks yielding one certificate have the same
four-lane denotation. The alias spelling retains eager producers and may
select an earlier output. The direct spelling is an explicit second premise,
not an assumed source-to-compiler equivalence. -/
theorem checked_alias_direct_denotations_equal
    (aliasBytes aliasNormalized aliasCanonical directBytes directNormalized : Token)
    (certificate : Certificate) (input : Lanes)
    (halias : checkAliasCanonical aliasBytes aliasNormalized aliasCanonical =
      some certificate)
    (hdirect : checkRelation directBytes directNormalized = some certificate) :
    SSAAliasTextBytes.denotation aliasBytes input =
      SSATextBytes.denotation directBytes input := by
  obtain ⟨_, _, _, _, _, _, haliasSem⟩ :=
    checked_alias_canonical_bytes_sound aliasBytes aliasNormalized
      aliasCanonical certificate input halias
  exact haliasSem.symm.trans
    (checked_relation_sound directBytes directNormalized certificate input
      hdirect)

/-- Exact alias/source/IR byte admission plus an independently checked
producer-only spelling, a constant-island certificate, and a fixed-address
ledger construct a complete 512-row *modeled* physical trace for every
public input. All local arithmetic roots vanish and ideal external Gate
events balance. The direct spelling premise is visible in the signature. -/
theorem checked_alias_with_direct_physical_trace
    (aliasBytes aliasNormalized aliasCanonical directBytes directNormalized : Token)
    (certificate : Certificate) (input : Lanes)
    (island : List ColumnCell) (values : List Quad)
    (externalUses externalYields : List Nat)
    (halias : checkAliasCanonical aliasBytes aliasNormalized aliasCanonical =
      some certificate)
    (hdirect : checkRelation directBytes directNormalized = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hledger : CheckedGateAddressLedger.check
      (joinedCells certificate island) externalUses externalYields = true) :
    ∃ (wire : Nat → Quad) (output : Lanes) (physical : Trace 9),
      SSAAliasTextBytes.denotation aliasBytes input = some output ∧
      physical = traceWithExternal (joinedCells certificate island) wire
        externalUses externalYields ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island, fixedMatches physical cell) ∧
      allArithmeticRootsZero physical ∧
      wire (address certificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      balanced (nativeRows physical) physical.externalUses
        physical.externalYields := by
  obtain ⟨wire, output, hdenotation, hlength, hcoverage, hfixed,
      harithmetic, hselected, _⟩ :=
    S31.Functional.Correspondence.CheckedDirectGateModeledComposition.checked_direct_full_modeled_trace
      directBytes directNormalized certificate input island values
      externalUses externalYields hdirect hisland hledger
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
      S31.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence.checked_joined_trace_gate_balance
        directBytes directNormalized certificate island values wire
        externalUses externalYields hdirect hisland hledger
  have haliasDenotation : SSAAliasTextBytes.denotation aliasBytes input =
      some output := by
    rw [checked_alias_direct_denotations_equal aliasBytes aliasNormalized
      aliasCanonical directBytes directNormalized certificate input halias
      hdirect]
    exact hdenotation
  exact ⟨wire, output, physical, haliasDenotation, rfl, hlength,
    hcoverage, hfixedPhysical, harithmeticPhysical, hselected, hbalance⟩

end S31.Functional.Correspondence.AliasCheckedPhysicalModeledComposition
