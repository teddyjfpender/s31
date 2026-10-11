-- Generated from the checked selected direct Gate package and native OODS source contracts.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Core verifier SHA-256: 85e70cea004f82060d94363b3552e0f2d9cd4203cee69fff0fb47b5345056381
-- Resident verifier SHA-256: 43d7524cc99b8084620c9983d6a9f0241fb0d5eced32c63753866d49e5e5c988
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
