-- Generated from the selected Gate package and split-one native composition extraction.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Core verifier SHA-256: a66a349bcf408fc7864985d1c92ec7c9335fbc5287d9e5dc6de24072881246a9
-- Proof extraction SHA-256: 1d5d1726a45c64a141ce38e541bfe649af4582aedd51e6420c2be8a935bfbc7c
-- Verifier types SHA-256: 93b3145a250777f5e9f8835561cff94a00cecd0553c2d0756fa09e544900852a
-- QM31 field SHA-256: a60c2a5a6f10bf91b1bfab41a526e41b589d0d1d83275e0516cf68b7228be931
-- `factor` is native `oods_point.repeatedDouble(composition_log_size - 2).x`.
-- PCS authentication, circle-point implementation and FRI are premises.
import S31.Gadgets.Air.DirectGateCompositionOpening
import S31.Gadgets.Air.GeneratedDirectGateOodsOpenings

namespace S31.Gadgets.Air.GeneratedDirectGateCompositionOpening

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsOpenings
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.DirectGateOodsComposition
open S31.Gadgets.Air.DirectGateCompositionOpening

open S31.Gadgets.Air.GeneratedDirectGateTranscriptParams

/-- The native `extractCompositionOodsEvalWithSplit` reads exactly the
last eight singleton columns when split is one. `accepted` is the
subsequent core-verifier comparison to Gate quotient evaluation. -/
theorem accepted_tree_eq_pure (samples : Samples)
    (_shape : DirectGateOodsOpenings.Shape samples)
    (compositionTree : List (List QM))
    (factor z alpha claimed coefficient zeroifier : QM)
    (hzero : zeroifier ≠ 0)
    (accepted : extractSplitOne factor compositionTree =
      some (quotientFold coefficient zeroifier⁻¹
        (S31.Gadgets.Air.GeneratedDirectGateTranscriptParams.transcriptRoots
          (cellsOfSamples samples) z alpha claimed))) :
    extractSplitOne factor compositionTree =
      some (S31.Gadgets.Air.CompositionFold.fold coefficient
        (pureRoots (cellsOfSamples samples) alpha z (claimed / 512)) / zeroifier) := by
  rw [← transcript_composition_eq_pure (cellsOfSamples samples)
    z alpha claimed coefficient zeroifier hzero]
  exact accepted

end S31.Gadgets.Air.GeneratedDirectGateCompositionOpening
