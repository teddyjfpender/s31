import S31.Gadgets.Air.TaggedPairConditionalCorrespondence

/-!
A typed source-side model of the new mixed profile's interleaved component
roster and Gate event emission. The roster mirrors
`runtime/mixed_boundary/registry.zig::forSlot`: circuit, then `(chip, bridge)`
for each canonical source call. The older fixed pair profile has a different
five-claim order and is deliberately not identified with this roster.

Gate addresses are `Fin p` in this model. Consequently every emitted Gate
address is canonical, and each emitted seven-word Gate tuple has the fixed
relation tag. The mapping from Zig's parsed/canonical source, actual emitted
rows, and live component handles into this typed model remains an explicit
compiler-correspondence obligation. This file has no PCS or Fiat--Shamir
claim.
-/

namespace S31.Gadgets.Air.SourceMixedRoster

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence

def gateRelationId : Nat := 378353459
def chipRelationId : Nat := 1395863811

inductive Role where
  | circuit | chip | bridge
  deriving DecidableEq, Repr

inductive Key where
  | bundledCircuit | pairChip | pairBridge | manyChip | manyBridge
  deriving DecidableEq, Repr

structure Slot where
  role : Role
  key : Key
  callId : Option Nat
  proofIndex : Nat
  claimedSumIndex : Nat
  relationIds : List Nat
  deriving DecidableEq, Repr

def circuitSlot : Slot :=
  ⟨.circuit, .bundledCircuit, none, 0, 0, [gateRelationId]⟩

def chipSlot (call : Nat) : Slot :=
  ⟨.chip, if call < 2 then .pairChip else .manyChip,
    some call, 1 + 2 * call, 1 + 2 * call, [chipRelationId]⟩

def bridgeSlot (call : Nat) : Slot :=
  ⟨.bridge, if call < 2 then .pairBridge else .manyBridge,
    some call, 2 + 2 * call, 2 + 2 * call,
    [gateRelationId, chipRelationId]⟩

/-- The exact `forSlot` arithmetic of the new source-derived registry,
represented over an already bounded index. The caller must separately show
that source inspection produced `n` canonical calls and `1+2n` live slots. -/
def sourceSlot (n : Nat) (index : Fin (1 + 2 * n)) : Slot :=
  if index.val = 0 then circuitSlot
  else
    let call := (index.val - 1) / 2
    if (index.val - 1) % 2 = 0 then chipSlot call
    else bridgeSlot call

theorem sourceSlot_zero (n : Nat) :
    sourceSlot n ⟨0, by omega⟩ = circuitSlot := by
  simp [sourceSlot]

theorem sourceSlot_call_bound (n : Nat)
    (index : Fin (1 + 2 * n)) (hnonzero : index.val ≠ 0) :
    (index.val - 1) / 2 < n := by
  have hindex := index.isLt
  omega

theorem sourceSlot_chip {n : Nat} (call : Fin n) :
    sourceSlot n ⟨1 + 2 * call.val, by omega⟩ =
      chipSlot call.val := by
  have hnonzero : 1 + 2 * call.val ≠ 0 := by omega
  have hsub : 1 + 2 * call.val - 1 = 2 * call.val := by omega
  have hdiv : (2 * call.val) / 2 = call.val := by omega
  have hmod : (2 * call.val) % 2 = 0 := by omega
  simp [sourceSlot, hnonzero, hsub, hdiv, hmod]

theorem sourceSlot_bridge {n : Nat} (call : Fin n) :
    sourceSlot n ⟨2 + 2 * call.val, by omega⟩ =
      bridgeSlot call.val := by
  have hnonzero : 2 + 2 * call.val ≠ 0 := by omega
  have hsub : 2 + 2 * call.val - 1 = 1 + 2 * call.val := by omega
  have hdiv : (1 + 2 * call.val) / 2 = call.val := by omega
  have hmod : (1 + 2 * call.val) % 2 = 1 := by omega
  simp [sourceSlot, hnonzero, hsub, hdiv, hmod]

theorem sourceSlot_claim_index (n : Nat)
    (index : Fin (1 + 2 * n)) :
    (sourceSlot n index).claimedSumIndex = index.val := by
  by_cases hz : index.val = 0
  · simp [sourceSlot, hz, circuitSlot]
  · have hbound := sourceSlot_call_bound n index hz
    have hindex := index.isLt
    unfold sourceSlot
    simp only [hz, ↓reduceIte]
    split_ifs <;> simp [chipSlot, bridgeSlot] <;> omega

/-! Source-owned Gate addresses and tuple lists. -/

abbrev CanonicalAddress := Fin 2147483647
abbrev CanonicalEvent := CanonicalAddress × Quad

def CanonicalEvent.toGate (event : CanonicalEvent) : GateLookup.Event :=
  (event.1.val, event.2)

structure CanonicalRow where
  in0Address : CanonicalAddress
  in1Address : CanonicalAddress
  outAddress : CanonicalAddress
  flags : Flags
  in0 : Quad
  in1 : Quad
  output : Quad
  multiplicity : Nat

def CanonicalRow.toGate (row : CanonicalRow) : Row :=
  { in0Address := row.in0Address.val,
    in1Address := row.in1Address.val,
    outAddress := row.outAddress.val,
    flags := row.flags,
    in0 := row.in0,
    in1 := row.in1,
    output := row.output,
    multiplicity := row.multiplicity }

structure GateSource where
  rows : List CanonicalRow
  externalUses : List CanonicalEvent
  externalYields : List CanonicalEvent

def GateSource.gateRows (source : GateSource) : List Row :=
  source.rows.map CanonicalRow.toGate

def GateSource.gateExternalUses (source : GateSource) :
    List GateLookup.Event :=
  source.externalUses.map CanonicalEvent.toGate

def GateSource.gateExternalYields (source : GateSource) :
    List GateLookup.Event :=
  source.externalYields.map CanonicalEvent.toGate

def GateSource.circuitUses (source : GateSource) : List JointTuple :=
  (allUses source.gateRows source.gateExternalUses).map embedGateEvent

def GateSource.circuitYields (source : GateSource) : List JointTuple :=
  (allYields source.gateRows source.gateExternalYields).map embedGateEvent

theorem GateSource.circuit_uses_gate_tag (source : GateSource) :
    ∀ event ∈ source.circuitUses, IsGateEvent event := by
  intro event hmem
  obtain ⟨gate, _, rfl⟩ := List.mem_map.mp hmem
  exact paddedGateTuple_isGate _ _

theorem GateSource.circuit_yields_gate_tag (source : GateSource) :
    ∀ event ∈ source.circuitYields, IsGateEvent event := by
  intro event hmem
  obtain ⟨gate, _, rfl⟩ := List.mem_map.mp hmem
  exact paddedGateTuple_isGate _ _

private theorem row_uses_canonical (row : CanonicalRow)
    (event : GateLookup.Event)
    (hmem : event ∈ row.toGate.uses) :
    event.1 < 2147483647 := by
  simp only [Row.uses, CanonicalRow.toGate, List.mem_cons,
    List.mem_singleton] at hmem
  rcases hmem with rfl | rfl
  · exact row.in0Address.isLt
  · exact row.in1Address.isLt

private theorem row_yields_canonical (row : CanonicalRow)
    (event : GateLookup.Event)
    (hmem : event ∈ row.toGate.yields) :
    event.1 < 2147483647 := by
  have hrep : event ∈
      List.replicate row.multiplicity
        (row.outAddress.val, row.output) := by
    simpa [Row.yields, CanonicalRow.toGate] using hmem
  have heq := List.eq_of_mem_replicate hrep
  rw [heq]
  exact row.outAddress.isLt

theorem GateSource.canonical_uses (source : GateSource) :
    ∀ event ∈ allUses source.gateRows source.gateExternalUses,
      event.1 < 2147483647 := by
  intro event hmem
  rcases List.mem_append.mp hmem with hrow | hext
  · obtain ⟨row, hr, huse⟩ := List.mem_flatMap.mp hrow
    obtain ⟨canonical, _, rfl⟩ := List.mem_map.mp hr
    exact row_uses_canonical canonical event huse
  · obtain ⟨canonical, _, rfl⟩ := List.mem_map.mp hext
    exact canonical.1.isLt

theorem GateSource.canonical_yields (source : GateSource) :
    ∀ event ∈ allYields source.gateRows source.gateExternalYields,
      event.1 < 2147483647 := by
  intro event hmem
  rcases List.mem_append.mp hmem with hrow | hext
  · obtain ⟨row, hr, hyield⟩ := List.mem_flatMap.mp hrow
    obtain ⟨canonical, _, rfl⟩ := List.mem_map.mp hr
    exact row_yields_canonical canonical event hyield
  · obtain ⟨canonical, _, rfl⟩ := List.mem_map.mp hext
    exact canonical.1.isLt

theorem GateSource.canonical_events (source : GateSource) :
    ∀ event ∈
      allUses source.gateRows source.gateExternalUses ++
        allYields source.gateRows source.gateExternalYields,
      event.1 < 2147483647 := by
  intro event hmem
  rcases List.mem_append.mp hmem with huse | hyield
  · exact source.canonical_uses event huse
  · exact source.canonical_yields event hyield

/-- The typed source emitter discharges the four Gate projection premises:
both circuit lists carry the Gate tag, their lists equal the physical-row
event lists by construction, and every emitted address is canonical.
Chip-only lists vanish under the Gate-tag projection. A native-verifier
proof would still need to authenticate that its actual source-derived rows
and component roster are exactly this `GateSource`. -/
theorem GateSource.exact_joint_implies_gate_balance
    (source : GateSource) (chipYields chipUses : List JointTuple)
    (hchipYields : ∀ event ∈ chipYields, IsChipEvent event)
    (hchipUses : ∀ event ∈ chipUses, IsChipEvent event)
    (hjoint : (source.circuitYields ++ chipYields).Perm
      (source.circuitUses ++ chipUses)) :
    balanced source.gateRows source.gateExternalUses
      source.gateExternalYields := by
  exact exact_joint_balance_implies_gate_balance
    source.gateRows source.gateExternalUses source.gateExternalYields
    source.circuitYields source.circuitUses chipYields chipUses
    source.circuit_yields_gate_tag source.circuit_uses_gate_tag
    hchipYields hchipUses rfl rfl source.canonical_events hjoint

end S31.Gadgets.Air.SourceMixedRoster
