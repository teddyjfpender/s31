import S31.Gadgets.Functional.Correspondence.SourceDeterminedDirectRows

/-!
Arbitrary-trace direct Gate soundness with no caller-supplied add-row count.
The exact source-byte check determines the count and completes the physical
context. All remaining facts concern decoded fixed/main columns, installed
arithmetic roots, ideal Gate producer events and public pins. None follows
from a succinct native verifier Boolean in this module.
-/

namespace S31.Functional.Correspondence.SourceDeterminedPhysicalSoundness

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.RawGateSoundness
open S31.Functional.Correspondence.AliasRawGateSoundness
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.SourceDeterminedDirectRows

/-- The arbitrary 512-row decoded trace premises that cannot be calculated
from the source bytes alone. In particular, `fixed` is a statement about
decoded fixed cells, `arithmetic` about decoded main cells, and the Gate
events are ideal exact-balance data. The add partition is deliberately absent:
accepted bytes derive it as `compiledAddRows certificate`. -/
structure UnpartitionedTrace (trace : Trace 9) (certificate : Certificate)
    (input claimed : Lanes) : Prop where
  fixed : ∀ cell ∈
      expectedCells certificate (compiledAddRows certificate) ++
      expectedInputCells certificate (compiledAddRows certificate) ++
      expectedOutputCells certificate (compiledAddRows certificate),
    fixedMatches trace cell
  arithmetic : allArithmeticRootsZero trace
  unique : uniqueProduced
    (allYields (nativeRows trace) trace.externalYields)
  zero : (0, base 0) ∈
    allYields (nativeRows trace) trace.externalYields
  basis1 : (15, unit ⟨1, by decide⟩) ∈
    allYields (nativeRows trace) trace.externalYields
  basis2 : (2, unit ⟨2, by decide⟩) ∈
    allYields (nativeRows trace) trace.externalYields
  basis3 : (16, unit ⟨3, by decide⟩) ∈
    allYields (nativeRows trace) trace.externalYields
  maskBasis : ∀ i : Fin 4,
    (maskBasisAddress i.val, unit i) ∈
      allYields (nativeRows trace) trace.externalYields
  inverseBasis : ∀ i : Fin 3,
    ((expectedInverseCell certificate (compiledAddRows certificate) i.val).in1,
      unitInverse ⟨i.val + 1, by omega⟩) ∈
        allYields (nativeRows trace) trace.externalYields
  inputPins : ∀ i : Fin 4,
    (3 + i.val, base (Field.toZMod (input i))) ∈ trace.externalUses
  outputPins : ∀ i : Fin 4,
    (7 + i.val, base (Field.toZMod (claimed i))) ∈ trace.externalUses

/-- Source-byte admission supplies the one missing physical-context field:
the exact 512-row add/sub/mul/pointwise partition. -/
def UnpartitionedTrace.toPhysical (trace : Trace 9)
    (certificate : Certificate) (input claimed : Lanes)
    (facts : UnpartitionedTrace trace certificate input claimed)
    (hpartition : compiledAddRows certificate + 1 + 27 +
      sourceMulCount certificate + 8 = 2 ^ 9) :
    PhysicalTraceContext trace certificate (compiledAddRows certificate)
      input claimed :=
  { partition := hpartition
    fixed := facts.fixed
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

/-- For every arbitrary decoded trace meeting the explicit physical facts,
exact Gate balance forces the public result of any source admitted by the
bounded direct byte grammar. The caller supplies neither an add-row count
nor a partition equation. -/
theorem direct_bytes_balanced_implies_claim
    (trace : Trace 9) (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate) (input claimed : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (facts : UnpartitionedTrace trace certificate input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    SSATextBytes.denotation sourceBytes input = some claimed := by
  let physical := UnpartitionedTrace.toPhysical trace certificate input claimed facts
    (direct_bytes_partition sourceBytes normalizedBytes certificate hcheck)
  let context : FixedTraceContext trace sourceBytes normalizedBytes certificate
      (compiledAddRows certificate) input claimed :=
    { physical with relation := hcheck }
  exact balanced_implies_source_claim trace sourceBytes normalizedBytes
    certificate (compiledAddRows certificate) input claimed context hbalance

/-- Canonical alias bytes use the same physical schedule. Aliases and
parentheses add no Gate producer, while the exact normalized and canonical
IR bytes bind the returned producer selected by the source. -/
theorem canonical_alias_balanced_implies_claim
    (trace : Trace 9) (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input claimed : Lanes)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (facts : UnpartitionedTrace trace certificate input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    SSAAliasTextBytes.denotation sourceBytes input = some claimed := by
  obtain ⟨_, _, _, _, _, hrelation, _⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate input hcheck
  let physical := UnpartitionedTrace.toPhysical trace certificate input claimed facts
    (canonical_alias_bytes_partition sourceBytes normalizedBytes
      canonicalBytes certificate hcheck)
  let context : AliasFixedTraceContext trace sourceBytes normalizedBytes
      certificate (compiledAddRows certificate) input claimed :=
    ⟨physical, hrelation⟩
  exact balanced_implies_alias_claim trace sourceBytes normalizedBytes
    certificate (compiledAddRows certificate) input claimed context hbalance

/-- A false direct-source claim makes ideal Gate balance impossible for any
fixed decoded trace satisfying the source-determined physical facts. The
existing raw LogUp theorem then bounds exceptional challenge pairs. -/
theorem direct_bytes_forged_unbalanced
    (trace : Trace 9) (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate) (input claimed : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (facts : UnpartitionedTrace trace certificate input claimed)
    (hforged : SSATextBytes.denotation sourceBytes input ≠ some claimed) :
    ¬ balanced (nativeRows trace) trace.externalUses trace.externalYields := by
  intro hbalance
  exact hforged (direct_bytes_balanced_implies_claim trace sourceBytes
    normalizedBytes certificate input claimed hcheck facts hbalance)

/-- The same arbitrary-trace false-claim implication for canonical alias
source bytes. -/
theorem canonical_alias_forged_unbalanced
    (trace : Trace 9) (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input claimed : Lanes)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (facts : UnpartitionedTrace trace certificate input claimed)
    (hforged : SSAAliasTextBytes.denotation sourceBytes input ≠ some claimed) :
    ¬ balanced (nativeRows trace) trace.externalUses trace.externalYields := by
  intro hbalance
  exact hforged (canonical_alias_balanced_implies_claim trace sourceBytes
    normalizedBytes canonicalBytes certificate input claimed hcheck facts hbalance)

/-- For every bounded direct source and every fixed decoded trace meeting the
explicit physical facts, an incorrect claim has only the existing algebraic
set of exceptional ideal Gate challenge pairs. The row partition is derived
from checked source bytes rather than supplied by the caller. -/
theorem direct_false_claim_raw_pair_bound
    (trace : Trace 9) (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate) (input claimed : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (facts : UnpartitionedTrace trace certificate input claimed)
    (hforged : SSATextBytes.denotation sourceBytes input ≠ some claimed)
    (hcanonical : ∀ event ∈
      allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields,
      (allUses (nativeRows trace) trace.externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields,
      (allYields (nativeRows trace) trace.externalYields).count event < 2147483647) :
    (acceptingChallengePairs trace).card ≤
      (5 * (allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields).toFinset.card ^ 2 +
        2 * (allUses (nativeRows trace) trace.externalUses ++
          allYields (nativeRows trace) trace.externalYields).toFinset.card +
        1536) * Fintype.card GateSecure := by
  exact unbalanced_accepting_pairs_card_le trace
    (direct_bytes_forged_unbalanced trace sourceBytes normalizedBytes
      certificate input claimed hcheck facts hforged)
    hcanonical huses hyields

/-- The same source-determined fixed-trace algebraic bound for canonical
alias bytes. Alias normalization contributes no additional physical rows. -/
theorem canonical_alias_false_claim_raw_pair_bound
    (trace : Trace 9) (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input claimed : Lanes)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (facts : UnpartitionedTrace trace certificate input claimed)
    (hforged : SSAAliasTextBytes.denotation sourceBytes input ≠ some claimed)
    (hcanonical : ∀ event ∈
      allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields,
      (allUses (nativeRows trace) trace.externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields,
      (allYields (nativeRows trace) trace.externalYields).count event < 2147483647) :
    (acceptingChallengePairs trace).card ≤
      (5 * (allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields).toFinset.card ^ 2 +
        2 * (allUses (nativeRows trace) trace.externalUses ++
          allYields (nativeRows trace) trace.externalYields).toFinset.card +
        1536) * Fintype.card GateSecure := by
  exact unbalanced_accepting_pairs_card_le trace
    (canonical_alias_forged_unbalanced trace sourceBytes normalizedBytes
      canonicalBytes certificate input claimed hcheck facts hforged)
    hcanonical huses hyields

end S31.Functional.Correspondence.SourceDeterminedPhysicalSoundness
