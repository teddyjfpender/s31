import S31.Gadgets.Air.SourceMixedPackCorrespondence
import S31.Gadgets.Air.GateProducerRoster

/-!
The source-shaped Gate boundary has one logical producer per active arithmetic
row, although the lookup emits its output `multiplicity` times. A checked
address roster for those logical producers and the circuit's other yields
implies the value uniqueness used by the mixed chain and packing theorems.

This is a conditional correspondence result. Native `validateUniqueProducers`
checks declared output addresses, but the source-to-Lean row roster and any
permutation scratch outputs still need explicit correspondence. The checked
roster premise here includes *every* active modeled row and every baseline
yield; it cannot be inferred merely from a successful proof verification.
-/

namespace S31.Gadgets.Air.SourceMixedProducerCheck

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateProducerCheck
open S31.Gadgets.Air.GateProducerRoster
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedPublicClosure
open S31.Gadgets.Air.SourceMixedPackCorrespondence
open S31.Gadgets.Air.SourceMixedAddressSchedule
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge

/-- One event for each active arithmetic producer and each other circuit
producer. Repeated lookup yields from a row do not create another producer. -/
def checkedRoster {N : Nat} (boundary : Boundary N) : List Event :=
  logicalProducers boundary.jointGateSource.gateRows
    boundary.jointGateSource.gateExternalYields

/-- A successful logical-producer scan discharges the global value-uniqueness
premise. The scan list must include any scratch rows; omitting them would make
this premise weaker than the theorem requires. -/
theorem unique_produced_of_checked_roster {N : Nat}
    (boundary : Boundary N) (bound : Nat) (result : Finset Nat)
    (hscan : scan bound ∅
      ((checkedRoster boundary).map Prod.fst) = some result) :
    uniqueProduced (produced boundary) := by
  have hunique :=
    (checked_produced_unique bound (checkedRoster boundary) result hscan).1
  intro address left right hleft hright
  have covered (value : S31.Gadgets.Packed.Quad)
      (h : (address, value) ∈ produced boundary) :
      (address, value) ∈ checkedRoster boundary := by
    exact all_yields_in_logical
      boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalYields
      boundary.jointGateSource.gateExternalYields
      (fun _ hmem => hmem) _ (by simpa [produced] using h)
  exact hunique address left right (covered left hleft) (covered right hright)

/-- The public computation theorem with producer uniqueness supplied by a
checked logical roster rather than an unconstrained uniqueness assumption.
Exact lookup balance, native row correspondence, and AIR authentication are
still separate hypotheses. -/
theorem all_public_outputs_from_checked_roster {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (haddresses : ∀ call slot,
      boundary.addresses call slot = canonicalAddress hN call slot)
    (bound : Nat) (result : Finset Nat)
    (hscan : scan bound ∅
      ((checkedRoster boundary).map Prod.fst) = some result)
    (hfirst : boundary.start ⟨0, hpositive⟩ = initial)
    (hrounds : ∀ call, boundary.rounds call = 16)
    (hconstants : ∀ call, boundary.constants call = (13 + call.val : F))
    (hjoint : ((boundary.jointGateSource).circuitUses ++
      jointUses rows boundary.finish).Perm
      ((boundary.jointGateSource).circuitYields ++
        jointYields rows boundary.start))
    (hstep : ∀ call row,
      (rows call row).output =
        boundary.step call (rows call row).input)
    (hpackInitial : PackPath boundary
      (fun lane => inputAddress 0 lane.val) 22)
    (hpackFinal : PackPath boundary
      (fun lane => outputAddress (N - 1) lane.val) (22 + 10 * N))
    (hzero : ValueAt boundary 0 (S31.Gadgets.Packed.base 0))
    (hadd : AcceptedRow boundary 22 (22 + 10 * N) (23 + 10 * N) .add)
    (hmul : AcceptedRow boundary 22 (22 + 10 * N)
      (24 + 10 * N) .pointwiseMul)
    (hpaths : ∀ product lane, OutputPath boundary N product lane) :
    ∀ lane : Fin 4,
      boundary.publicOutputs (outputSlot false lane) =
        S31.Gadgets.Air.SourceMixedChainSemantics.sourcePrefix N initial lane +
          initial lane ∧
      boundary.publicOutputs (outputSlot true lane) =
        S31.Gadgets.Air.SourceMixedChainSemantics.sourcePrefix N initial lane *
          initial lane := by
  exact all_public_outputs_from_pack_paths hN hpositive boundary rows initial
    haddresses (unique_produced_of_checked_roster boundary bound result hscan)
    hfirst hrounds hconstants hjoint hstep hpackInitial hpackFinal hzero
    hadd hmul hpaths

end S31.Gadgets.Air.SourceMixedProducerCheck
