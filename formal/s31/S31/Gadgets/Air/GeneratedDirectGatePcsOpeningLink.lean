-- Generated from the selected Gate package and reviewed OODS-to-PCS source dataflow.
-- Bundle SHA-256: 7b8022b09d84db371cc433aa0fcf132f7687f2720e05e4dc9a7650c575dc02c2
-- Gate program SHA-256: b80bf2c8b76770fb2cdee666908ac96f6dadedec83ae7ee4e334721af7478cf6
-- Source SHA-256: 2555767fb91b626f6ad959eb87bb2a83626f1aaacab3ad63179d966eeedfd1f6
-- Core verifier SHA-256: 85e70cea004f82060d94363b3552e0f2d9cd4203cee69fff0fb47b5345056381
-- PCS verifier SHA-256: a7b4e1977dc29feb9341eacceda8e09bd77a6a11dcdb7d0e4c1eb18445570581
-- FRI answers SHA-256: 5280b74c1762860fad733066a40d96dada813908532e3b8854e0a3f02f182181
-- PCS samples SHA-256: 18848c2e180236b0d6807a4d2863f127a8830366ac1df038f5042359e9401e2e
-- This theorem is conditional on PCS opening authentication; it does not prove it.
import S31.Gadgets.Air.DirectGatePcsOpeningLink

namespace S31.Gadgets.Air.GeneratedDirectGatePcsOpeningLink

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsOpenings
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.DirectGateOodsComposition
open S31.Gadgets.Air.DirectGateCircleFactor
open S31.Gadgets.Air.DirectGatePcsOpeningLink
open S31.Gadgets.Air.DirectGateCompositionOpening
open S31.Gadgets.Air.GeneratedDirectGateTranscriptParams

/-- The native verifier's shared proof-sample dataflow permits this
reduction only under an authenticated PCS-opening assumption. -/
theorem selected_gate_accepted_of_authenticated (samples : Samples)
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
  exact accepted_of_authenticated_openings samples compositionTree openings
    auth seed z alpha claimed coefficient zeroifier compositionLogSize
    hsize seedAccepted hzero accepted

end S31.Gadgets.Air.GeneratedDirectGatePcsOpeningLink
