import S31.Gadgets.Air.TaggedPairEventProjection

/-!
Decode the source's seven-word tagged chip tuples into natural-indexed,
four-lane events. This is an algebraic source correspondence step. It does
not assert that native proof acceptance implies the source row premises.
-/

namespace S31.Gadgets.Air.TaggedPairEventDecode

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.TaggedPairEventProjection
open S31.Gadgets.Air.RawChipIndexCoverage

def stateCoordinate (lane : Fin 4) : Fin 7 :=
  ⟨lane.val + 3, by omega⟩

/-- Read the canonical M31 step and four base-field lanes from one tuple.
This decoder is only used after the per-call chip-tag projection. -/
def decodeChipEvent (event : JointTuple) : Nat × (Fin 4 → F) :=
  ((event ⟨2, by decide⟩).re.re.val,
    fun lane => (event (stateCoordinate lane)).re.re)

theorem decode_chipTuple7 (call step : F) (state : Fin 4 → F) :
    decodeChipEvent (chipTuple7 call step state) =
      (step.val, state) := by
  apply Prod.ext
  · rfl
  · funext lane
    fin_cases lane <;> rfl

theorem decode_sourceChipInputTuple {R : Nat}
    (call : F) (step : Fin R → F)
    (input : Fin R → Fin 4 → F) (row : Fin R) :
    decodeChipEvent (sourceChipInputTuple call step input row) =
      ((step row).val, input row) :=
  decode_chipTuple7 call (step row) (input row)

theorem decode_sourceChipOutputTuple {R : Nat}
    (call : F) (step : Fin R → F)
    (output : Fin R → Fin 4 → F) (row : Fin R) :
    decodeChipEvent (sourceChipOutputTuple call step output row) =
      (((step row).val + 1) % 2147483647, output row) := by
  rw [sourceChipOutputTuple, decode_chipTuple7]
  congr 1

theorem decode_sourceBridgeStartTuple (call : F)
    (words : Fin 8 → Fin 16 → F) (row : Fin 16) :
    decodeChipEvent (sourceBridgeStartTuple call words row) =
      (0, fun lane => words (bridgeInputLane lane) row) := by
  rw [sourceBridgeStartTuple, decode_chipTuple7]
  rfl

theorem decode_sourceBridgeFinishTuple (call rounds : F)
    (words : Fin 8 → Fin 16 → F) (row : Fin 16) :
    decodeChipEvent (sourceBridgeFinishTuple call rounds words row) =
      (rounds.val, fun lane => words (bridgeOutputLane lane) row) := by
  rw [sourceBridgeFinishTuple, decode_chipTuple7]

theorem decode_bridgeStartEvent {alpha z : GateSecure}
    (bridge : BridgeRows alpha z) :
    bridge.startEvents.map decodeChipEvent =
      [(0, bridge.initialState)] := by
  simp only [BridgeRows.startEvents, sourceBridgeStartEvents,
    List.map_cons, List.map_nil, decode_sourceBridgeStartTuple]
  rfl

theorem decode_bridgeFinishEvent {alpha z : GateSecure}
    (bridge : BridgeRows alpha z) :
    bridge.finishEvents.map decodeChipEvent =
      [(bridge.rounds.val, bridge.finalState)] := by
  simp only [BridgeRows.finishEvents, sourceBridgeFinishEvents,
    List.map_cons, List.map_nil, decode_sourceBridgeFinishTuple]
  rfl

theorem decode_chipInputEvents {m : Nat} {hm : 0 < m}
    {alpha z : GateSecure} (chip : ChipRows m hm alpha z) :
    chip.inputEvents.map decodeChipEvent =
      List.ofFn (fun row : Fin (2 * m) =>
        ((chip.step row).val, chip.input row)) := by
  simp only [ChipRows.inputEvents, List.map_ofFn]
  congr 1
  funext row
  exact decode_sourceChipInputTuple chip.call chip.step chip.input row

theorem decode_chipOutputEvents {m : Nat} {hm : 0 < m}
    {alpha z : GateSecure} (chip : ChipRows m hm alpha z) :
    chip.outputEvents.map decodeChipEvent =
      List.ofFn (fun row : Fin (2 * m) =>
        (((chip.step row).val + 1) % 2147483647, chip.output row)) := by
  simp only [ChipRows.outputEvents, List.map_ofFn]
  congr 1
  funext row
  exact decode_sourceChipOutputTuple chip.call chip.step chip.output row

/-- A source per-call seven-word balance is exactly the value-bearing
natural-indexed balance used by the arbitrary-row path theorem. The bridge
round count is a verifier-fixed field value equal to the native chip row
count, and `R < p` prevents its canonical value from wrapping. -/
theorem raw_event_balance_of_source_call
    {m : Nat} {hm : 0 < m} {alpha z : GateSecure}
    (chip : ChipRows m hm alpha z)
    (bridge : BridgeRows alpha z)
    (hrounds : bridge.rounds = ((2 * m : Nat) : F))
    (hR : 2 * m < 2147483647)
    (hsource :
      (chip.inputEvents ++ bridge.finishEvents).Perm
        (chip.outputEvents ++ bridge.startEvents)) :
    (useEvents chip.rawRows bridge.finalState).Perm
      (yieldEvents 2147483647 chip.rawRows bridge.initialState) := by
  have hroundsVal : bridge.rounds.val = 2 * m := by
    rw [hrounds]
    exact ZMod.val_natCast_of_lt hR
  have hdecoded := hsource.map decodeChipEvent
  simp only [List.map_append, decode_chipInputEvents,
    decode_chipOutputEvents, decode_bridgeFinishEvent,
    decode_bridgeStartEvent, hroundsVal] at hdecoded
  change
    ((2 * m, bridge.finalState) :: List.ofFn
      (fun row : Fin (2 * m) =>
        ((chip.step row).val, chip.input row))).Perm
      ((0, bridge.initialState) :: List.ofFn
        (fun row : Fin (2 * m) =>
          (((chip.step row).val + 1) % 2147483647,
            chip.output row)))
  exact (List.perm_append_comm.trans hdecoded).trans
    List.perm_append_comm.symm

/-- Exact source joint event balance gives both complete affine-square
paths. This is conditional on Gate-only circuit events, verifier-fixed
call/round tags, the row-count field bounds, and the source chip/bridge
accepted-row structures. It does not infer any of these facts from a native
proof or Fiat–Shamir transcript. -/
theorem source_joint_implies_two_complete_paths
    {m₀ m₁ : Nat} {hm₀ : 0 < m₀} {hm₁ : 0 < m₁}
    {alpha z : GateSecure}
    (chip₀ : ChipRows m₀ hm₀ alpha z)
    (chip₁ : ChipRows m₁ hm₁ alpha z)
    (bridge₀ bridge₁ : BridgeRows alpha z)
    (circuitYields circuitUses : List JointTuple)
    (outputs : List Quad)
    (hcircuitYields : ∀ event,
      event ∈ circuitYields → IsGateEvent event)
    (hcircuitUses : ∀ event,
      event ∈ circuitUses → IsGateEvent event)
    (hcall₀ : bridge₀.call = chip₀.call)
    (hcall₁ : bridge₁.call = chip₁.call)
    (hdistinct : chip₀.call ≠ chip₁.call)
    (hrounds₀ : bridge₀.rounds = ((2 * m₀ : Nat) : F))
    (hrounds₁ : bridge₁.rounds = ((2 * m₁ : Nat) : F))
    (hR₀ : 2 * m₀ < 2147483647)
    (hR₁ : 2 * m₁ < 2147483647)
    (hjoint :
      ((circuitYields ++ publicOutputYields outputs) ++
        (bridge₀.gateEvents ++ bridge₁.gateEvents) ++
        (chip₀.inputEvents ++ chip₁.inputEvents) ++
        (bridge₀.finishEvents ++ bridge₁.finishEvents)).Perm
        (circuitUses ++ (chip₀.outputEvents ++ chip₁.outputEvents) ++
          (bridge₀.startEvents ++ bridge₁.startEvents))) :
    (bridge₀.finalState = iterateStep
      (fun state lane => state lane ^ 2 + chip₀.constant)
      (2 * m₀) bridge₀.initialState) ∧
    (bridge₁.finalState = iterateStep
      (fun state lane => state lane ^ 2 + chip₁.constant)
      (2 * m₁) bridge₁.initialState) := by
  have hbalance₀ := source_joint_implies_first_call_balance
    chip₀ chip₁ bridge₀ bridge₁ circuitYields circuitUses outputs
    hcircuitYields hcircuitUses hcall₀ hcall₁ hdistinct hjoint
  have hbalance₁ := source_joint_implies_second_call_balance
    chip₀ chip₁ bridge₀ bridge₁ circuitYields circuitUses outputs
    hcircuitYields hcircuitUses hcall₀ hcall₁ hdistinct hjoint
  exact ⟨
    chip_complete_path_of_exact_balance chip₀ bridge₀ hR₀
      (raw_event_balance_of_source_call chip₀ bridge₀
        hrounds₀ hR₀ hbalance₀),
    chip_complete_path_of_exact_balance chip₁ bridge₁ hR₁
      (raw_event_balance_of_source_call chip₁ bridge₁
        hrounds₁ hR₁ hbalance₁)⟩

/-- Source-shaped algebraic end-to-end theorem. The modeled verifier's
five-claim fold, exact circuit Gate claim, and challenge outside `badPairs7`
yield two complete endpoint paths. Logical AIR-row acceptance is carried in
`ChipRows` and `BridgeRows`; the theorem does not derive it from PCS/FRI
acceptance. Challenge goodness and compiler/manifest tag correspondence are
independent explicit premises. -/
theorem source_claim_fold_implies_two_complete_paths
    {m₀ m₁ : Nat} {hm₀ : 0 < m₀} {hm₁ : 0 < m₁}
    (alpha z : GateSecure)
    (chip₀ : ChipRows m₀ hm₀ alpha z)
    (chip₁ : ChipRows m₁ hm₁ alpha z)
    (bridge₀ bridge₁ : BridgeRows alpha z)
    (circuitYields circuitUses : List JointTuple)
    (outputs : List Quad) (circuitClaim : GateSecure)
    (hcircuitClaim : circuitClaim =
      productionReciprocalSum7 circuitYields alpha z -
      productionReciprocalSum7 circuitUses alpha z)
    (hcircuitYields : ∀ event,
      event ∈ circuitYields → IsGateEvent event)
    (hcircuitUses : ∀ event,
      event ∈ circuitUses → IsGateEvent event)
    (hcall₀ : bridge₀.call = chip₀.call)
    (hcall₁ : bridge₁.call = chip₁.call)
    (hdistinct : chip₀.call ≠ chip₁.call)
    (hrounds₀ : bridge₀.rounds = ((2 * m₀ : Nat) : F))
    (hrounds₁ : bridge₁.rounds = ((2 * m₁ : Nat) : F))
    (hR₀ : 2 * m₀ < 2147483647)
    (hR₁ : 2 * m₁ < 2147483647)
    (hverify : verifierClaimFold outputs
      (pairClaims circuitClaim chip₀.claim chip₁.claim
        bridge₀.claim bridge₁.claim) alpha z = 0)
    (hgood : (alpha,z) ∉ badPairs7
      ((circuitYields ++ publicOutputYields outputs) ++
        (bridge₀.gateEvents ++ bridge₁.gateEvents) ++
        (chip₀.inputEvents ++ chip₁.inputEvents) ++
        (bridge₀.finishEvents ++ bridge₁.finishEvents))
      (circuitUses ++ (chip₀.outputEvents ++ chip₁.outputEvents) ++
        (bridge₀.startEvents ++ bridge₁.startEvents))) :
    (bridge₀.finalState = iterateStep
      (fun state lane => state lane ^ 2 + chip₀.constant)
      (2 * m₀) bridge₀.initialState) ∧
    (bridge₁.finalState = iterateStep
      (fun state lane => state lane ^ 2 + chip₁.constant)
      (2 * m₁) bridge₁.initialState) := by
  obtain ⟨_, _, hjoint⟩ := source_pair_claims_imply_exact_events
    alpha z chip₀ chip₁ bridge₀ bridge₁
    circuitYields circuitUses outputs circuitClaim
    hcircuitClaim hverify hgood
  exact source_joint_implies_two_complete_paths
    chip₀ chip₁ bridge₀ bridge₁ circuitYields circuitUses outputs
    hcircuitYields hcircuitUses hcall₀ hcall₁ hdistinct
    hrounds₀ hrounds₁ hR₀ hR₁ hjoint

end S31.Gadgets.Air.TaggedPairEventDecode
