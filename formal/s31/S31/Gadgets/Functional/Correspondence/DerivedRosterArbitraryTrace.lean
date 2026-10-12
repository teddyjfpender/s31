import S31.Gadgets.Functional.Correspondence.AliasDerivedGateMultiplicities
import S31.Gadgets.Functional.Correspondence.SourceDeterminedPhysicalSoundness

/-!
The source/canonical byte checker and the island address/value checker fix all
512 preprocessed rows, including output-use multiplicities computed from the
complete read schedule. If an arbitrary decoded trace has exactly those fixed
rows, locally satisfies the installed arithmetic roots, has the specified
public boundary events, and satisfies ideal exact Gate balance, its claim is
the source result. This is conditional on decoded-row authentication and ideal
Gate balance. It is not a theorem about the native PCS/FRI verifier Boolean.
-/

namespace S31.Functional.Correspondence.DerivedRosterArbitraryTrace

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.AliasDerivedGateMultiplicities
open S31.Functional.Correspondence.AliasJoinedFixedRoster
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.SourceDeterminedPhysicalSoundness

/-- The trace facts that cannot be reconstructed from checked source bytes and
the complete fixed roster. In particular, these remain obligations for any
real proof-system refinement. -/
structure RuntimeFacts (trace : Trace 9) (certificate : Certificate)
    (input claimed : Lanes) : Prop where
  arithmetic : allArithmeticRootsZero trace
  unique : uniqueProduced (allYields (nativeRows trace) trace.externalYields)
  zero : (0, base 0) ∈ allYields (nativeRows trace) trace.externalYields
  basis1 : (15, unit ⟨1, by decide⟩) ∈
    allYields (nativeRows trace) trace.externalYields
  basis2 : (2, unit ⟨2, by decide⟩) ∈
    allYields (nativeRows trace) trace.externalYields
  basis3 : (16, unit ⟨3, by decide⟩) ∈
    allYields (nativeRows trace) trace.externalYields
  maskBasis : ∀ i : Fin 4, (maskBasisAddress i.val, unit i) ∈
    allYields (nativeRows trace) trace.externalYields
  inverseBasis : ∀ i : Fin 3,
    ((expectedInverseCell certificate (compiledAddRows certificate) i.val).in1,
      unitInverse ⟨i.val + 1, by omega⟩) ∈
        allYields (nativeRows trace) trace.externalYields
  inputPins : ∀ i : Fin 4,
    (3 + i.val, base (Field.toZMod (input i))) ∈ trace.externalUses
  outputPins : ∀ i : Fin 4,
    (7 + i.val, base (Field.toZMod (claimed i))) ∈ trace.externalUses

/-- The checked complete roster discharges the selected source/public fixed
premise of arbitrary-trace soundness; all other runtime facts stay explicit.
Every decoded physical row is covered, and its count is source/schedule
derived, so a caller-supplied island multiplicity cannot alter this theorem.
-/
theorem checked_roster_arbitrary_trace_claim
    (trace : Trace 9) (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (island : List ColumnCell)
    (values : List Quad) (input claimed : Lanes)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hcheck : AliasDerivedGateMultiplicities.check certificate island values = true)
    (hfixed : ∀ cell ∈ joinedCells certificate
      (derivedIsland certificate island), fixedMatches trace cell)
    (facts : RuntimeFacts trace certificate input claimed)
    (hbalance : balanced (nativeRows trace) trace.externalUses
      trace.externalYields) :
    (joinedCells certificate (derivedIsland certificate island)).length = 512 ∧
    (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate
      (derivedIsland certificate island),
        cell.traceRow = row.val ∧ fixedMatches trace cell ∧
        cell.mults = outputUseCount certificate island cell.out) ∧
    SSAAliasTextBytes.denotation sourceBytes input = some claimed := by
  have hparts := hcheck
  simp only [AliasDerivedGateMultiplicities.check, Bool.and_eq_true] at hparts
  have hisland : NativeConstantIslandCertificate.check certificate
      (derivedIsland certificate island) values = true := hparts.1.1
  have hroster := checked_alias_joined_roster_complete sourceBytes
    normalizedBytes canonicalBytes certificate (derivedIsland certificate island)
    values halias hisland
  have hcounts := checked_joined_has_read_counts certificate island values hcheck
  have hselected : ∀ cell ∈ projectedCells certificate,
      fixedMatches trace cell := by
    intro cell hcell
    exact hfixed cell (List.mem_append.mpr (Or.inl hcell))
  let physical : UnpartitionedTrace trace certificate input claimed :=
    { fixed := by simpa [projectedCells, List.append_assoc] using hselected
      arithmetic := facts.arithmetic
      unique := facts.unique
      zero := facts.zero
      basis1 := facts.basis1
      basis2 := facts.basis2
      basis3 := facts.basis3
      maskBasis := facts.maskBasis
      inverseBasis := facts.inverseBasis
      inputPins := facts.inputPins
      outputPins := facts.outputPins }
  refine ⟨hroster.1, ?_, canonical_alias_balanced_implies_claim trace
    sourceBytes normalizedBytes canonicalBytes certificate input claimed
    halias physical hbalance⟩
  intro row
  obtain ⟨cell, hcell, hrow⟩ := hroster.2.2.2 row
  exact ⟨cell, hcell, hrow, hfixed cell hcell, hcounts cell hcell⟩

end S31.Functional.Correspondence.DerivedRosterArbitraryTrace
