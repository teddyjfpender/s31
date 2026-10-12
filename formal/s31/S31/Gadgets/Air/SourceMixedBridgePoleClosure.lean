import S31.Gadgets.Air.SourceMixedPoleClosure

/-!
Bridge interaction AIR has zero-over-zero poles too. The checked bridge model
requires nonzero denominators at its anchor row. This module derives those
conditions from an event-support exceptional set, leaving the exact event-list
alignment as a visible premise. Main-row constancy in
`source_bridge_claim_eq_endpoint_events` then propagates anchor values across
the sixteen physical bridge rows.

This is an algebraic trace statement. It does not extract committed bridge
columns from an accepted PCS/FRI proof.
-/

namespace S31.Gadgets.Air.SourceMixedBridgePoleClosure

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.SourceMixedPoleClosure
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge

/-- The bridge AIR residuals before the four denominator conditions are
established. The words are still prover-selected committed witness columns. -/
structure RawBridgeRows (alpha z : GateSecure) where
  addresses : Fin 8 → F
  call : F
  rounds : F
  words : Fin 8 → Fin 16 → F
  current : Fin 5 → Fin 16 → GateSecure
  claim : GateSecure
  sixteenNonzero : (16 : GateSecure) ≠ 0
  mainAccepted : ∀ lane row,
    words lane row - words lane
      (sourceNextIndex 8 (by decide) bitReverse4 row) = 0
  interactionAccepted : TaggedPairAirClosure.BridgeAccepted
    (nativePrevMask 8 (by decide)
      (bitReverseEquivOfInvolution bitReverse4 bitReverse4_involutive))
    (sourceBridgeD0 addresses words alpha z)
    (sourceBridgeD1 addresses words alpha z)
    (sourceBridgeFirst call words alpha z)
    (sourceBridgeLast call rounds words alpha z)
    current claim

def RawBridgeRows.gateEvents {alpha z : GateSecure}
    (raw : RawBridgeRows alpha z) : List JointTuple :=
  sourceBridgeGateEvents raw.addresses raw.words

def RawBridgeRows.startEvents {alpha z : GateSecure}
    (raw : RawBridgeRows alpha z) : List JointTuple :=
  sourceBridgeStartEvents raw.call raw.words

def RawBridgeRows.finishEvents {alpha z : GateSecure}
    (raw : RawBridgeRows alpha z) : List JointTuple :=
  sourceBridgeFinishEvents raw.call raw.rounds raw.words

/-- A source-aligned bridge has all ten anchor tuples in the global ideal
event support. This remains a compiler/trace alignment premise. -/
structure AnchorEvents (raw : RawBridgeRows alpha z)
    (events : List JointTuple) : Prop where
  gateEven : ∀ slot,
    sourceBridgeGateTuple raw.addresses raw.words
      (bridgeEvenLane slot) sourceBridgeAnchor ∈ events
  gateOdd : ∀ slot,
    sourceBridgeGateTuple raw.addresses raw.words
      (bridgeOddLane slot) sourceBridgeAnchor ∈ events
  start : sourceBridgeStartTuple raw.call raw.words
    sourceBridgeAnchor ∈ events
  finish : sourceBridgeFinishTuple raw.call raw.rounds raw.words
    sourceBridgeAnchor ∈ events

/-- The four gate pairs and two chip endpoint tuples at the anchor are
exactly the bridge's local ideal-event support. -/
theorem AnchorEvents.local {alpha z : GateSecure}
    (raw : RawBridgeRows alpha z) :
    AnchorEvents raw
      ((sourceBridgeGateEvents raw.addresses raw.words ++
        sourceBridgeStartEvents raw.call raw.words) ++
        sourceBridgeFinishEvents raw.call raw.rounds raw.words) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro slot
    fin_cases slot <;>
      simp [sourceBridgeGateEvents, sourceBridgeStartEvents,
        sourceBridgeFinishEvents]
  · intro slot
    fin_cases slot <;>
      simp [sourceBridgeGateEvents, sourceBridgeStartEvents,
        sourceBridgeFinishEvents]
  · simp [sourceBridgeGateEvents, sourceBridgeStartEvents,
      sourceBridgeFinishEvents]
  · simp [sourceBridgeGateEvents, sourceBridgeStartEvents,
      sourceBridgeFinishEvents]

/-- Event-list alignment can be supplied as inclusion of the bridge's local
events in the global ideal support, with no denominator premise hidden in it. -/
theorem AnchorEvents.ofLocalInclusion {alpha z : GateSecure}
    (raw : RawBridgeRows alpha z) (events : List JointTuple)
    (hinclude : ∀ event,
      event ∈ ((sourceBridgeGateEvents raw.addresses raw.words ++
        sourceBridgeStartEvents raw.call raw.words) ++
        sourceBridgeFinishEvents raw.call raw.rounds raw.words) →
      event ∈ events) : AnchorEvents raw events := by
  have hlocal := AnchorEvents.local raw
  exact ⟨fun slot => hinclude _ (hlocal.gateEven slot),
    fun slot => hinclude _ (hlocal.gateOdd slot),
    hinclude _ hlocal.start, hinclude _ hlocal.finish⟩

/-- Outside the emitted-event pole set, raw bridge residuals satisfy the
checked bridge contract. The native AIR does not itself enforce nonzero
denominators at a pole. -/
def RawBridgeRows.toChecked {alpha z : GateSecure}
    (raw : RawBridgeRows alpha z) (events : List JointTuple)
    (halign : AnchorEvents raw events)
    (hgood : (alpha, z) ∉ eventPolePairs events) : BridgeRows alpha z :=
  { addresses := raw.addresses
    call := raw.call
    rounds := raw.rounds
    words := raw.words
    current := raw.current
    claim := raw.claim
    sixteenNonzero := raw.sixteenNonzero
    mainAccepted := raw.mainAccepted
    interactionAccepted := raw.interactionAccepted
    nonzeroD0 := fun slot => by
      simpa [sourceBridgeD0] using
        event_nonzero_outside events
          (sourceBridgeGateTuple raw.addresses raw.words
            (bridgeEvenLane slot) sourceBridgeAnchor)
          (halign.gateEven slot) alpha z hgood
    nonzeroD1 := fun slot => by
      simpa [sourceBridgeD1] using
        event_nonzero_outside events
          (sourceBridgeGateTuple raw.addresses raw.words
            (bridgeOddLane slot) sourceBridgeAnchor)
          (halign.gateOdd slot) alpha z hgood
    nonzeroFirst := by
      simpa [sourceBridgeFirst] using
        event_nonzero_outside events
          (sourceBridgeStartTuple raw.call raw.words sourceBridgeAnchor)
          halign.start alpha z hgood
    nonzeroLast := by
      simpa [sourceBridgeLast] using
        event_nonzero_outside events
          (sourceBridgeFinishTuple raw.call raw.rounds raw.words
            sourceBridgeAnchor)
          halign.finish alpha z hgood }

/-- Compose local bridge event inclusion with the mixed boundary's widened
exceptional set. The same challenge exclusion used for the raw Gate rows
therefore supplies the bridge's anchor denominator conditions. -/
def RawBridgeRows.toCheckedOutsideMixed {N : Nat} {alpha z : GateSecure}
    (raw : RawBridgeRows alpha z)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (gateRows : Fin 512 → Row)
    (hinclude : ∀ event,
      event ∈ ((sourceBridgeGateEvents raw.addresses raw.words ++
        sourceBridgeStartEvents raw.call raw.words) ++
        sourceBridgeFinishEvents raw.call raw.rounds raw.words) →
      event ∈
        ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
          (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)))
    (hgood : (alpha, z) ∉ mixedErrorPairs boundary rows gateRows) :
    BridgeRows alpha z :=
  raw.toChecked _
    (AnchorEvents.ofLocalInclusion raw _ hinclude)
    (by
      intro hpole
      exact hgood (Finset.mem_union_left _ (Finset.mem_union_right _ hpole)))

end S31.Gadgets.Air.SourceMixedBridgePoleClosure
