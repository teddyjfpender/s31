import S31.Gadgets.Air.GeneratedDirectGateCircleFactor

/-!
The resident Gate verifier reads the same `sampled_values` tree for its OODS
equation and for the later PCS quotient/FRI check. This module describes the
exact values that a *sound* PCS opening would authenticate. It does not prove
Merkle binding, Fiat–Shamir security, FRI soundness, or the Zig implementation.
Those are explicit premises of `accepted_of_authenticated_openings`.
-/

namespace S31.Gadgets.Air.DirectGatePcsOpeningLink

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsOpenings
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.DirectGateOodsComposition
open S31.Gadgets.Air.DirectGateCompositionOpening
open S31.Gadgets.Air.DirectGateCircleFactor
open S31.Gadgets.Air.DirectGateNativeIndices
open S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
open S31.Gadgets.Air.GeneratedDirectGateCircleFactor
open S31.Gadgets.Air.GeneratedDirectGateTranscriptParams

/-- Values of the committed column polynomials at the selected mask points.
The previous interaction value is meaningful only in columns four through
seven. -/
structure PolynomialOpenings where
  fixed : Fin 8 → QM
  main : Fin 12 → QM
  interactionCurrent : Fin 8 → QM
  interactionPrevious : Fin 8 → QM
  composition : Fin 8 → QM

def expectedCells (openings : PolynomialOpenings) : Cells where
  localFixed i := openings.fixed (fixedReadOrder i)
  main i := openings.main i
  interaction i := openings.interactionCurrent i
  previousInteraction i := if i.val < 4 then 0 else openings.interactionPrevious i

def expectedCompositionTree (openings : PolynomialOpenings) : List (List QM) :=
  [[openings.composition 0], [openings.composition 1],
   [openings.composition 2], [openings.composition 3],
   [openings.composition 4], [openings.composition 5],
   [openings.composition 6], [openings.composition 7]]

/-- The cryptographic PCS premise, indexed by the precise native Gate mask.
It says that every supplied OODS value is an evaluation of the polynomial
bound to its tree commitment. This relation is deliberately *not* constructed
from a successful verifier flag inside Lean. -/
structure PcsOpeningAssumption (samples : Samples)
    (compositionTree : List (List QM))
    (openings : PolynomialOpenings) : Prop where
  fixed : ∀ i, samples.fixed i = [openings.fixed i]
  main : ∀ i, samples.main i = [openings.main i]
  interactionFirst : ∀ i, i.val < 4 →
    samples.interaction i = [openings.interactionCurrent i]
  interactionLast : ∀ i, 4 ≤ i.val →
    samples.interaction i =
      [openings.interactionPrevious i, openings.interactionCurrent i]
  composition : compositionTree = expectedCompositionTree openings

theorem authenticated_shape (samples : Samples)
    (compositionTree : List (List QM)) (openings : PolynomialOpenings)
    (auth : PcsOpeningAssumption samples compositionTree openings) :
    DirectGateOodsOpenings.Shape samples := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i; rw [auth.fixed i]; rfl
  · intro i; rw [auth.main i]; rfl
  · intro i hi; rw [auth.interactionFirst i hi]; rfl
  · intro i hi; rw [auth.interactionLast i hi]; rfl

theorem authenticated_cells (samples : Samples)
    (compositionTree : List (List QM)) (openings : PolynomialOpenings)
    (auth : PcsOpeningAssumption samples compositionTree openings) :
    cellsOfSamples samples = expectedCells openings := by
  have hf : (cellsOfSamples samples).localFixed = (expectedCells openings).localFixed := by
    funext i
    simp [cellsOfSamples, expectedCells, fixedRead, auth.fixed]
  have hm : (cellsOfSamples samples).main = (expectedCells openings).main := by
    funext i
    simp [cellsOfSamples, expectedCells, mainRead, auth.main]
  have hi : (cellsOfSamples samples).interaction = (expectedCells openings).interaction := by
    funext i
    fin_cases i <;>
      simp [cellsOfSamples, expectedCells, interactionRead,
        interactionMaskRead, interactionOffsets, offsetIndex,
        auth.interactionFirst, auth.interactionLast]
  have hp : (cellsOfSamples samples).previousInteraction =
      (expectedCells openings).previousInteraction := by
    funext i
    fin_cases i <;>
      simp [cellsOfSamples, expectedCells, interactionRead,
        interactionMaskRead, interactionOffsets, offsetIndex,
        auth.interactionFirst, auth.interactionLast]
  cases h : cellsOfSamples samples with
  | mk fixed main interaction previousInteraction =>
    cases h' : expectedCells openings with
    | mk fixed' main' interaction' previousInteraction' =>
      simp only [h, h'] at hf hm hi hp
      cases hf
      cases hm
      cases hi
      cases hp
      rfl

theorem authenticated_composition_tree (samples : Samples)
    (compositionTree : List (List QM)) (openings : PolynomialOpenings)
    (auth : PcsOpeningAssumption samples compositionTree openings)
    (factor : QM) :
    extractSplitOne factor compositionTree =
      extractSplitOne factor (expectedCompositionTree openings) := by
  rw [auth.composition]

/-- Given one authenticated opening inventory and the native OODS equality,
the accepted Gate claim is the eleven-root pure polynomial identity *at those
authenticated evaluations*. This is conditional on a sound PCS opening
assumption and the checked seed/conversion and zeroifier premises. -/
theorem accepted_of_authenticated_openings (samples : Samples)
    (compositionTree : List (List QM)) (openings : PolynomialOpenings)
    (auth : PcsOpeningAssumption samples compositionTree openings)
    (seed z alpha claimed coefficient zeroifier : QM)
    (compositionLogSize : Nat) (hsize : 2 ≤ compositionLogSize)
    (seedAccepted : checkedFromSeed seed = some (fromSeed seed))
    (hzero : zeroifier ≠ 0)
    (accepted : extractSplitOne
      (repeatedDouble (compositionLogSize - 2) (fromSeed seed)).x
      compositionTree = some (quotientFold coefficient zeroifier⁻¹
        (transcriptRoots (cellsOfSamples samples) z alpha claimed))) :
    extractSplitOne (factor seed compositionLogSize)
      (expectedCompositionTree openings) =
      some (S31.Gadgets.Air.CompositionFold.fold coefficient
        (pureRoots (expectedCells openings) alpha z (claimed / 512)) /
        zeroifier) := by
  have shape := authenticated_shape samples compositionTree openings auth
  have claim := accepted_seeded_tree_eq_pure samples shape compositionTree
    seed z alpha claimed coefficient zeroifier compositionLogSize hsize
    seedAccepted hzero accepted
  rw [auth.composition, authenticated_cells samples compositionTree openings auth]
    at claim
  exact claim

end S31.Gadgets.Air.DirectGatePcsOpeningLink
