-- Generated from the selected Gate package and native OODS circle source contract.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Core verifier SHA-256: a66a349bcf408fc7864985d1c92ec7c9335fbc5287d9e5dc6de24072881246a9
-- Circle SHA-256: 71176ae60dc3bb2b799d0463c50b27f65ed908fd05e4405cdcda44f2e3aac5cf
-- Proof extraction SHA-256: 1d5d1726a45c64a141ce38e541bfe649af4582aedd51e6420c2be8a935bfbc7c
-- The seed denominator and native Zig refinement remain premises.
import S31.Gadgets.Air.DirectGateCircleFactor
import S31.Gadgets.Air.GeneratedDirectGateCompositionOpening

namespace S31.Gadgets.Air.GeneratedDirectGateCircleFactor

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsOpenings
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.DirectGateOodsComposition
open S31.Gadgets.Air.DirectGateCircleFactor
open S31.Gadgets.Air.DirectGateCompositionOpening
open S31.Gadgets.Air.GeneratedDirectGateCompositionOpening

/-- Reduce a native-shaped OODS check whose factor is the x-coordinate
after `compositionLogSize - 2` doublings of the seed-derived point.
The native channel draw and PCS opening authentication are premises. -/
theorem accepted_seeded_tree_eq_pure (samples : Samples)
    (shape : DirectGateOodsOpenings.Shape samples)
    (compositionTree : List (List QM))
    (seed z alpha claimed coefficient zeroifier : QM)
    (compositionLogSize : Nat)
    (_hsize : 2 ≤ compositionLogSize)
    (hden : 1 + seed * seed ≠ 0)
    (hzero : zeroifier ≠ 0)
    (accepted : extractSplitOne
      (repeatedDouble (compositionLogSize - 2) (fromSeed seed)).x
      compositionTree = some (quotientFold coefficient zeroifier⁻¹
        (S31.Gadgets.Air.GeneratedDirectGateTranscriptParams.transcriptRoots
          (cellsOfSamples samples) z alpha claimed))) :
    extractSplitOne (factor seed compositionLogSize) compositionTree =
      some (S31.Gadgets.Air.CompositionFold.fold coefficient
        (pureRoots (cellsOfSamples samples) alpha z (claimed / 512)) / zeroifier) := by
  rw [factor_eq_repeated_double seed hden compositionLogSize]
  exact accepted_tree_eq_pure samples shape compositionTree
    _ z alpha claimed coefficient zeroifier hzero accepted

end S31.Gadgets.Air.GeneratedDirectGateCircleFactor
