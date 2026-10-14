import S31.Gadgets.Functional.Correspondence.ControlGadgetClaimTrace

/-!
A program-independent, conditional bridge from the native Gate claim equation
to exact Gate events and coherent wires. The output list and all component
event lists are arbitrary finite lists. External producer multiplicity is
modeled as repeated yields from one logical producer, matching fixed trace
rows. Claim-to-cell authentication, local AIR residuals, and good Fiat--Shamir
challenges remain explicit premises for arbitrary accepted proofs.
-/

namespace S31.Gadgets.Air.GateClaimTraceJoin

set_option maxHeartbeats 800000

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateWireMap
open S31.Gadgets.Air.GateProducerRoster
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GatePublicInteraction
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Functional.Correspondence.ControlGadgetClaimTrace

abbrev Event := GateLookup.Event

def outputEventsFrom (index : Nat) : List Quad → List Event
  | [] => []
  | value :: rest => (3 + index, value) :: outputEventsFrom (index + 1) rest

def publicGateEvents (outputs : List Quad) : List Event :=
  outputEventsFrom 0 outputs ++ [(2, ⟨0, 0, 1, 0⟩)]

theorem output_events_embed (index : Nat) (outputs : List Quad) :
    (outputEventsFrom index outputs).map embedGateEvent =
      outputEventsAux index outputs := by
  induction outputs generalizing index with
  | nil => rfl
  | cons value rest ih =>
      simp [outputEventsFrom, outputEventsAux, embedGateEvent, ih]

theorem public_events_embed (outputs : List Quad) :
    (publicGateEvents outputs).map embedGateEvent =
      publicOutputYields outputs := by
  simp [publicGateEvents, publicOutputYields, output_events_embed,
    fixedUEvent, embedGateEvent]

theorem native_public_reciprocal (outputs : List Quad)
    (alpha z : GateSecure) :
    productionReciprocalSum7 (publicOutputYields outputs) alpha z =
      productionReciprocalSum (publicGateEvents outputs) alpha z := by
  rw [← public_events_embed]
  exact padded_gate_reciprocal_sum _ alpha z

/-- One active external component row owns one address even when its fixed
multiplicity makes several identical Gate-yield events. -/
structure ExternalProducer where
  address : Nat
  value : Quad
  multiplicity : Nat

def activeExternal (producers : List ExternalProducer) : List ExternalProducer :=
  producers.filter (fun producer => 0 < producer.multiplicity)

def externalProducers (producers : List ExternalProducer) : List Event :=
  (activeExternal producers).map (fun producer => (producer.address, producer.value))

def externalYields (producers : List ExternalProducer) : List Event :=
  producers.flatMap (fun producer =>
    List.replicate producer.multiplicity (producer.address, producer.value))

theorem external_yield_has_logical_producer
    (producers : List ExternalProducer) (event : Event)
    (h : event ∈ externalYields producers) :
    event ∈ externalProducers producers := by
  obtain ⟨producer, hproducer, hyield⟩ := List.mem_flatMap.mp h
  have hevent : event = (producer.address, producer.value) :=
    List.eq_of_mem_replicate hyield
  have hpositive : 0 < producer.multiplicity := by
    by_contra hnot
    have hzero := Nat.eq_zero_of_not_pos hnot
    simp [hzero] at hyield
  exact List.mem_map.mpr ⟨producer,
    List.mem_filter.mpr ⟨hproducer, by simpa using hpositive⟩,
    hevent.symm⟩

theorem unique_produced_from_active_roster
    (rows : List Row) (producers : List ExternalProducer)
    (hroster : ((activeRows rows).map Row.outAddress ++
      (externalProducers producers).map Prod.fst).Nodup) :
    uniqueProduced (allYields rows (externalYields producers)) := by
  exact unique_yields_of_nodup_roster rows
    (externalYields producers) (externalProducers producers) hroster
    (external_yield_has_logical_producer producers)

/-- This is the still-conditional bridge from the eleven claimed values to
the signed sums of the actual committed component cells. -/
structure CellClaims (rows : List Row) (otherUses : List Event)
    (producers : List ExternalProducer) (claims : List GateSecure)
    (alpha z : GateSecure) : Prop where
  exactCells : ∃ cellClaims : Fin 11 → GateSecure,
    claims = List.ofFn cellClaims ∧
      (List.ofFn cellClaims).sum =
        (rows.map fun row => rowContribution row alpha z).sum +
          productionReciprocalSum otherUses alpha z -
          productionReciprocalSum (externalYields producers) alpha z

theorem CellClaims.sum_eq (h : CellClaims rows otherUses producers claims alpha z) :
    claims.sum = (rows.map fun row => rowContribution row alpha z).sum +
      productionReciprocalSum otherUses alpha z -
      productionReciprocalSum (externalYields producers) alpha z := by
  obtain ⟨_, heq, hsum⟩ := h.exactCells
  rw [heq]
  exact hsum

structure GoodChallenges (rows : List Row) (outputs : List Quad)
    (otherUses : List Event) (producers : List ExternalProducer)
    (alpha z : GateSecure) : Prop where
  canonical : ∀ event ∈
    allUses rows (publicGateEvents outputs ++ otherUses) ++
      allYields rows (externalYields producers), event.1 < 2147483647
  uses : ∀ event ∈
    allUses rows (publicGateEvents outputs ++ otherUses) ++
      allYields rows (externalYields producers),
      (allUses rows (publicGateEvents outputs ++ otherUses)).count event < 2147483647
  yields : ∀ event ∈
    allUses rows (publicGateEvents outputs ++ otherUses) ++
      allYields rows (externalYields producers),
      (allYields rows (externalYields producers)).count event < 2147483647
  goodAlpha : alpha ∉ badAlpha
    (allUses rows (publicGateEvents outputs ++ otherUses) ++
      allYields rows (externalYields producers))
  goodZ : z ∉ badZ
    (allUses rows (publicGateEvents outputs ++ otherUses))
    (allYields rows (externalYields producers)) alpha

/-- There is no free ideal-balance premise: the native public equation,
cell-derived claim equation, and good challenges imply exact Gate balance
for any finite S31 v1 Gate output and component event lists. -/
theorem balanced_of_cell_claims (rows : List Row) (outputs : List Quad)
    (otherUses : List Event) (producers : List ExternalProducer)
    (claims : List GateSecure) (alpha z : GateSecure)
    (hclaims : CellClaims rows otherUses producers claims alpha z)
    (haccepted : nativeGateClosure outputs claims alpha z = 0)
    (hgood : GoodChallenges rows outputs otherUses producers alpha z) :
    balanced rows (publicGateEvents outputs ++ otherUses)
      (externalYields producers) := by
  have hsum := nativeGateClosure_eq_event_sum outputs claims alpha z
  rw [native_public_reciprocal] at hsum
  rw [hclaims.sum_eq] at hsum
  have hclosed :
      (rows.map fun row => rowContribution row alpha z).sum +
        productionReciprocalSum (publicGateEvents outputs ++ otherUses) alpha z -
        productionReciprocalSum (externalYields producers) alpha z = 0 := by
    rw [hsum] at haccepted
    rw [productionReciprocalSum_append]
    linear_combination haccepted
  exact closed_gate_contribution_balanced_of_counts rows
    (publicGateEvents outputs ++ otherUses) (externalYields producers)
    alpha z hgood.canonical hgood.uses hgood.yields
    hgood.goodAlpha hgood.goodZ hclosed

/-- Every public output event, at any output-list length, denotes the
unique produced value at its Gate address. -/
theorem public_event_matches_wire (rows : List Row) (outputs : List Quad)
    (otherUses : List Event) (producers : List ExternalProducer)
    (claims : List GateSecure) (alpha z : GateSecure)
    (hclaims : CellClaims rows otherUses producers claims alpha z)
    (haccepted : nativeGateClosure outputs claims alpha z = 0)
    (hgood : GoodChallenges rows outputs otherUses producers alpha z)
    (hroster : ((activeRows rows).map Row.outAddress ++
      (externalProducers producers).map Prod.fst).Nodup)
    (address : Nat) (value : Quad)
    (hpublic : (address, value) ∈ publicGateEvents outputs) :
    producedWire (allYields rows (externalYields producers)) address = value := by
  have hbalance := balanced_of_cell_claims rows outputs otherUses
    producers claims alpha z hclaims haccepted hgood
  have huse : (address, value) ∈
      allUses rows (publicGateEvents outputs ++ otherUses) := by
    apply List.mem_append_right
    exact List.mem_append_left _ hpublic
  exact producedWire_eq _
    (unique_produced_from_active_roster rows producers hroster)
    address value (hbalance.mem_iff.mp huse)

/-- Every active physical QM31 row with vanishing local AIR residuals
evaluates on the same coherent wire map as the public events. -/
theorem active_row_air_on_wire (rows : List Row) (outputs : List Quad)
    (otherUses : List Event) (producers : List ExternalProducer)
    (claims : List GateSecure) (alpha z : GateSecure)
    (hclaims : CellClaims rows otherUses producers claims alpha z)
    (haccepted : nativeGateClosure outputs claims alpha z = 0)
    (hgood : GoodChallenges rows outputs otherUses producers alpha z)
    (hroster : ((activeRows rows).map Row.outAddress ++
      (externalProducers producers).map Prod.fst).Nodup)
    (row : Row) (hrow : row ∈ rows) (hm : 0 < row.multiplicity)
    (hair : S31.Gadgets.Air.Qm31Ops.accepts
      row.flags row.in0 row.in1 row.output) :
    S31.Gadgets.Air.Qm31Ops.accepts row.flags
      (producedWire (allYields rows (externalYields producers)) row.in0Address)
      (producedWire (allYields rows (externalYields producers)) row.in1Address)
      (producedWire (allYields rows (externalYields producers)) row.outAddress) := by
  exact row_accepts_on_wire rows
    (publicGateEvents outputs ++ otherUses) (externalYields producers)
    (balanced_of_cell_claims rows outputs otherUses producers
      claims alpha z hclaims haccepted hgood)
    (unique_produced_from_active_roster rows producers hroster)
    row hrow hm hair

end S31.Gadgets.Air.GateClaimTraceJoin
