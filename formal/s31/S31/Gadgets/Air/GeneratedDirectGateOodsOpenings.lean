-- Generated from the checked selected direct Gate package and native OODS source contracts.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Core verifier SHA-256: a66a349bcf408fc7864985d1c92ec7c9335fbc5287d9e5dc6de24072881246a9
-- Resident verifier SHA-256: 675eda24a90e6c5b456daf5188a596e596437375119e35c641c10c11beacece2
-- PCS sample authentication and FRI remain separate assumptions.
import S31.Gadgets.Air.DirectGateOodsOpenings
import S31.Gadgets.Air.GeneratedDirectGateTranscriptParams

namespace S31.Gadgets.Air.GeneratedDirectGateOodsOpenings

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsOpenings
open S31.Gadgets.Air.DirectGateOodsComposition
open S31.Gadgets.Air.DirectGateOodsLogUp

open S31.Gadgets.Air.GeneratedDirectGateTranscriptParams

/-- Accepted claim equation at the resident Gate component. `accepted`
is the core verifier's OODS equality check, with the exact sampled
values later passed to PCS verification. `Shape` makes every read
defined; authentication of the values is an external premise. -/
theorem accepted_claim_eq_pure (samples : Samples)
    (_shape : DirectGateOodsOpenings.Shape samples)
    (z alpha claimed coefficient zeroifier compositionClaim : QM)
    (_hzero : zeroifier ≠ 0)
    (accepted : compositionClaim =
      quotientFold coefficient zeroifier⁻¹
        (S31.Gadgets.Air.GeneratedDirectGateTranscriptParams.transcriptRoots
          (cellsOfSamples samples) z alpha claimed)) :
    compositionClaim = S31.Gadgets.Air.CompositionFold.fold coefficient
      (pureRoots (cellsOfSamples samples) alpha z (claimed / 512)) / zeroifier := by
  rw [accepted]
  exact transcript_composition_eq_pure (cellsOfSamples samples)
      z alpha claimed coefficient zeroifier _hzero

end S31.Gadgets.Air.GeneratedDirectGateOodsOpenings
