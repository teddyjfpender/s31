import S31.Gadgets.Air.TaggedPairSourceCorrespondence

/-!
Source-shaped composition for the staged two-call tagged chip boundary.
Every accepted-row equation is an explicit premise. The native verifier's
PCS/FRI acceptance and Fiat–Shamir challenge distribution are not proved.
-/

namespace S31.Gadgets.Air.TaggedPairSourceComposition

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairAirClosure
open S31.Gadgets.Air.TaggedPairSourceCorrespondence

/-- The six row residuals of one source chip: four secure arithmetic
coordinates and two LogUp interaction coordinates. `call` is a fixed
verifier parameter; `step`, inputs, and outputs are committed witness rows.
Accepted logical-row equations are supplied explicitly; chip nonpole
conditions follow from its two interaction equations. -/
structure ChipRows (m : Nat) (hm : 0 < m)
    (alpha z : GateSecure) where
  bitReverseIndex : Fin (2 * m) → Fin (2 * m)
  bitReverseInvolutive : ∀ index,
    bitReverseIndex (bitReverseIndex index) = index
  call : F
  step : Fin (2 * m) → F
  input : Fin (2 * m) → Fin 4 → F
  output : Fin (2 * m) → Fin 4 → F
  constant : F
  first : Fin (2 * m) → GateSecure
  current : Fin (2 * m) → GateSecure
  claim : GateSecure
  rowCountNonzero : ((2 * m : Nat) : GateSecure) ≠ 0
  arithmeticAccepted : ∀ row lane,
    liftBase (output row lane) -
      (liftBase (input row lane)) ^ 2 - liftBase constant = 0
  interactionAccepted : ChipAccepted
    (nativePrevMask m hm
      (bitReverseEquivOfInvolution bitReverseIndex bitReverseInvolutive))
    (sourceChipQin call step input alpha z)
    (sourceChipQout call step output alpha z)
    first current claim

def ChipRows.inputEvents {m : Nat} {hm : 0 < m} {alpha z : GateSecure}
    (chip : ChipRows m hm alpha z) : List JointTuple :=
  List.ofFn (sourceChipInputTuple chip.call chip.step chip.input)

def ChipRows.outputEvents {m : Nat} {hm : 0 < m} {alpha z : GateSecure}
    (chip : ChipRows m hm alpha z) : List JointTuple :=
  List.ofFn (sourceChipOutputTuple chip.call chip.step chip.output)

theorem ChipRows.arithmetic_sound {m : Nat} {hm : 0 < m}
    {alpha z : GateSecure} (chip : ChipRows m hm alpha z) :
    ∀ row lane,
      chip.output row lane = chip.input row lane ^ 2 + chip.constant :=
  source_chip_arithmetic_residuals_sound
    chip.constant chip.input chip.output chip.arithmeticAccepted

theorem ChipRows.claim_eq_events {m : Nat} {hm : 0 < m}
    {alpha z : GateSecure} (chip : ChipRows m hm alpha z) :
    chip.claim = productionReciprocalSum7 chip.inputEvents alpha z -
      productionReciprocalSum7 chip.outputEvents alpha z :=
  source_chip_claim_eq_transition_events m hm
    chip.bitReverseIndex chip.bitReverseInvolutive chip.call
    chip.step chip.input chip.output chip.first chip.current chip.claim
    alpha z chip.rowCountNonzero chip.interactionAccepted

/-- Sixteen source rows of one bridge. Eight main-column residuals and five
interaction residuals are explicit premises. The verifier fixes addresses,
call ID, and round count. -/
structure BridgeRows (alpha z : GateSecure) where
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
  interactionAccepted : BridgeAccepted
    (nativePrevMask 8 (by decide)
      (bitReverseEquivOfInvolution bitReverse4 bitReverse4_involutive))
    (sourceBridgeD0 addresses words alpha z)
    (sourceBridgeD1 addresses words alpha z)
    (sourceBridgeFirst call words alpha z)
    (sourceBridgeLast call rounds words alpha z)
    current claim
  nonzeroD0 : ∀ slot,
    sourceBridgeD0 addresses words alpha z slot
      sourceBridgeAnchor ≠ 0
  nonzeroD1 : ∀ slot,
    sourceBridgeD1 addresses words alpha z slot
      sourceBridgeAnchor ≠ 0
  nonzeroFirst : sourceBridgeFirst call words alpha z
    sourceBridgeAnchor ≠ 0
  nonzeroLast : sourceBridgeLast call rounds words alpha z
    sourceBridgeAnchor ≠ 0

def BridgeRows.anchor {alpha z : GateSecure}
    (_bridge : BridgeRows alpha z) : Fin 16 :=
  sourceBridgeAnchor

def BridgeRows.gateEvents {alpha z : GateSecure}
    (bridge : BridgeRows alpha z) : List JointTuple :=
  sourceBridgeGateEvents bridge.addresses bridge.words

def BridgeRows.startEvents {alpha z : GateSecure}
    (bridge : BridgeRows alpha z) : List JointTuple :=
  sourceBridgeStartEvents bridge.call bridge.words

def BridgeRows.finishEvents {alpha z : GateSecure}
    (bridge : BridgeRows alpha z) : List JointTuple :=
  sourceBridgeFinishEvents bridge.call bridge.rounds bridge.words

theorem BridgeRows.claim_eq_events {alpha z : GateSecure}
    (bridge : BridgeRows alpha z) :
    bridge.claim = productionReciprocalSum7 bridge.gateEvents alpha z -
      productionReciprocalSum7 bridge.startEvents alpha z +
      productionReciprocalSum7 bridge.finishEvents alpha z := by
  have h := source_bridge_claim_eq_endpoint_events bridge.addresses bridge.call
    bridge.rounds bridge.words bridge.current bridge.claim alpha z
    bridge.sixteenNonzero bridge.mainAccepted bridge.interactionAccepted
    bridge.nonzeroD0 bridge.nonzeroD1 bridge.nonzeroFirst
    bridge.nonzeroLast
  simpa only [BridgeRows.gateEvents, BridgeRows.startEvents,
    BridgeRows.finishEvents] using h

/-- Native claim order: circuit, chip 0, chip 1, bridge 0, bridge 1. -/
def pairClaims (circuit chip₀ chip₁ bridge₀ bridge₁ : GateSecure) :
    Fin 5 → GateSecure := fun index =>
  match index.val with
  | 0 => circuit
  | 1 => chip₀
  | 2 => chip₁
  | 3 => bridge₀
  | _ => bridge₁

/-- Source circuit events must carry the six-word Gate relation tag.
The circuit claim equation alone would also admit fabricated chip-tagged
events; the compiler-to-event-list correspondence remains a separate
premise. -/
def IsGateEvent (event : JointTuple) : Prop :=
  event 0 = liftBase 378353459

def IsChipEvent (event : JointTuple) : Prop :=
  event 0 = liftBase 1395863811

theorem gate_chip_tags_disjoint (event : JointTuple) :
    IsGateEvent event → ¬ IsChipEvent event := by
  intro hgate hchip
  have htags : (378353459 : F) = 1395863811 :=
    liftBase_injective (hgate.symm.trans hchip)
  have hneq : (378353459 : F) ≠ 1395863811 := by decide
  exact hneq htags

theorem sourceChipInputTuple_isChip {R : Nat} (call : F)
    (step : Fin R → F) (input : Fin R → Fin 4 → F)
    (row : Fin R) :
    IsChipEvent (sourceChipInputTuple call step input row) := rfl

theorem sourceChipOutputTuple_isChip {R : Nat} (call : F)
    (step : Fin R → F) (output : Fin R → Fin 4 → F)
    (row : Fin R) :
    IsChipEvent (sourceChipOutputTuple call step output row) := rfl

theorem sourceBridgeStartTuple_isChip (call : F)
    (words : Fin 8 → Fin 16 → F) (row : Fin 16) :
    IsChipEvent (sourceBridgeStartTuple call words row) := rfl

theorem sourceBridgeFinishTuple_isChip (call rounds : F)
    (words : Fin 8 → Fin 16 → F) (row : Fin 16) :
    IsChipEvent (sourceBridgeFinishTuple call rounds words row) := rfl

theorem sourceBridgeGateTuple_isGate
    (addresses : Fin 8 → F) (words : Fin 8 → Fin 16 → F)
    (lane : Fin 8) (row : Fin 16) :
    IsGateEvent (sourceBridgeGateTuple addresses words lane row) := rfl

theorem paddedGateTuple_isGate (address : F) (value : Quad) :
    IsGateEvent (paddedGateTuple address value) := rfl

/-- Negative model if circuit-event classification is omitted: a fabricated
circuit yield with the chip relation tag exactly cancels a bridge start,
even though there is no chip row. The actual circuit compiler must guarantee
its event lists contain only Gate-tagged tuples. -/
theorem forged_circuit_chip_event_counterexample :
    let forged := chipTuple7 0 0 (fun _ => 0)
    (([forged] ++ [] ++ [] : List JointTuple).Perm
      ([] ++ [] ++ [forged])) ∧ ¬ IsGateEvent forged := by
  constructor
  · simp
  · intro hgate
    have htags : (1395863811 : F) = 378353459 :=
      liftBase_injective (by simpa [IsGateEvent, chipTuple7] using hgate)
    have hneq : (1395863811 : F) ≠ 378353459 := by decide
    exact hneq htags

theorem pairClaims_fold (outputs : List Quad)
    (circuit chip₀ chip₁ bridge₀ bridge₁ alpha z : GateSecure) :
    verifierClaimFold outputs
      (pairClaims circuit chip₀ chip₁ bridge₀ bridge₁) alpha z =
      circuit + chip₀ + chip₁ + bridge₀ + bridge₁ +
        productionReciprocalSum7 (publicOutputYields outputs) alpha z := by
  rw [verifierClaimFold_eq_source_closure]
  rfl

/-- Full source-shaped algebraic composition. A zero native claim fold and
a challenge outside the explicit exceptional set imply exact joint tagged
event balance, while all four lanes of each chip satisfy their M31 step
equation. This theorem assumes logical row acceptance, a separate circuit
Gate claim interpretation, and challenge goodness. It does not yet use
canonical call/round agreement or Gate-only circuit event classification to
derive two complete paths from the exact joint multiset. It does not derive
accepted rows from native PCS/FRI verification or challenge goodness from
the Fiat–Shamir transcript. -/
theorem source_pair_claims_imply_exact_events
    {m₀ m₁ : Nat} {hm₀ : 0 < m₀} {hm₁ : 0 < m₁}
    (alpha z : GateSecure)
    (chip₀ : ChipRows m₀ hm₀ alpha z)
    (chip₁ : ChipRows m₁ hm₁ alpha z)
    (bridge₀ bridge₁ : BridgeRows alpha z)
    (circuitYields circuitUses : List JointTuple)
    (outputs : List Quad) (circuitClaim : GateSecure)
    (hcircuit : circuitClaim =
      productionReciprocalSum7 circuitYields alpha z -
      productionReciprocalSum7 circuitUses alpha z)
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
    (∀ row lane,
      chip₀.output row lane = chip₀.input row lane ^ 2 + chip₀.constant) ∧
    (∀ row lane,
      chip₁.output row lane = chip₁.input row lane ^ 2 + chip₁.constant) ∧
    ((circuitYields ++ publicOutputYields outputs) ++
      (bridge₀.gateEvents ++ bridge₁.gateEvents) ++
      (chip₀.inputEvents ++ chip₁.inputEvents) ++
      (bridge₀.finishEvents ++ bridge₁.finishEvents)).Perm
      (circuitUses ++ (chip₀.outputEvents ++ chip₁.outputEvents) ++
        (bridge₀.startEvents ++ bridge₁.startEvents)) := by
  refine ⟨chip₀.arithmetic_sound, chip₁.arithmetic_sound, ?_⟩
  have hfold := pairClaims_fold outputs circuitClaim chip₀.claim
    chip₁.claim bridge₀.claim bridge₁.claim alpha z
  have hfive : circuitClaim + chip₀.claim + chip₁.claim +
      bridge₀.claim + bridge₁.claim +
      productionReciprocalSum7 (publicOutputYields outputs) alpha z = 0 :=
    hfold ▸ hverify
  exact five_claimed_sums_imply_exact_joint_events
    circuitYields circuitUses (publicOutputYields outputs)
    bridge₀.gateEvents bridge₁.gateEvents
    chip₀.inputEvents chip₁.inputEvents
    chip₀.outputEvents chip₁.outputEvents
    bridge₀.startEvents bridge₁.startEvents
    bridge₀.finishEvents bridge₁.finishEvents
    alpha z circuitClaim chip₀.claim chip₁.claim bridge₀.claim
    bridge₁.claim hcircuit chip₀.claim_eq_events chip₁.claim_eq_events
    bridge₀.claim_eq_events bridge₁.claim_eq_events hfive hgood

end S31.Gadgets.Air.TaggedPairSourceComposition
