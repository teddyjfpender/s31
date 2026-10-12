import S31.Gadgets.Air.SourceMixedRoster

/-!
The generated `direct-m31-mixed-interleaved-admission-v1` manifest has one
bundled circuit entry followed by a chip and bridge for each source call.
This file proves the finite combinatorics of the *checked projection* in
`runtime/mixed_boundary/{inspection,registry,registry_manifest}.zig`.

The native inspection checks live AIR facts, provenance, geometry, relations,
source digests, and the verifier-owned source before a manifest is admitted.
Those checks are not implemented or proved equivalent to Zig here. In
particular, this is not a proof about parsing, hashing, PCS, or Fiat--Shamir.
-/

namespace S31.Gadgets.Air.Manifest.InterleavedRoster

open S31.Gadgets.Air.SourceMixedRoster

/-- The projection fields used by the native registry's `forSlot` and the
manifest's `fromSchedule` validation. -/
def expected (n : Nat) (index : Fin (1 + 2 * n)) : Slot := sourceSlot n index

/-- Closed constructor IDs in `registry.zig::constructor`. -/
def constructorId : Key → Nat
  | .bundledCircuit => 0
  | .pairChip => 1
  | .pairBridge => 2
  | .manyChip => 3
  | .manyBridge => 4

theorem expected_count (n : Nat) :
    (List.ofFn (expected n)).length = 1 + 2 * n := by simp

theorem expected_circuit (n : Nat) :
    expected n ⟨0, by omega⟩ = circuitSlot := sourceSlot_zero n

theorem expected_chip {n : Nat} (call : Fin n) :
    expected n ⟨1 + 2 * call.val, by omega⟩ = chipSlot call.val :=
  sourceSlot_chip call

theorem expected_bridge {n : Nat} (call : Fin n) :
    expected n ⟨2 + 2 * call.val, by omega⟩ = bridgeSlot call.val :=
  sourceSlot_bridge call

theorem expected_constructor_ids {n : Nat} (call : Fin n) :
    constructorId (expected n ⟨1 + 2 * call.val, by omega⟩).key =
      (if call.val < 2 then 1 else 3) ∧
    constructorId (expected n ⟨2 + 2 * call.val, by omega⟩).key =
      (if call.val < 2 then 2 else 4) := by
  by_cases h : call.val < 2
  · simp [expected_chip, expected_bridge, chipSlot, bridgeSlot,
      constructorId, h]
  · simp [expected_chip, expected_bridge, chipSlot, bridgeSlot,
      constructorId, h]

/-- Both transcript positions are equal to their unique roster position. -/
theorem expected_indices (n : Nat) (index : Fin (1 + 2 * n)) :
    (expected n index).proofIndex = index.val ∧
    (expected n index).claimedSumIndex = index.val := by
  constructor
  · by_cases hz : index.val = 0
    · simp [expected, sourceSlot, hz, circuitSlot]
    · have hbound := sourceSlot_call_bound n index hz
      have hindex := index.isLt
      unfold expected sourceSlot
      simp only [hz, ↓reduceIte]
      split_ifs <;> simp [chipSlot, bridgeSlot] <;> omega
  · exact sourceSlot_claim_index n index

/-- No two positions denote the same projected logical component. -/
theorem expected_injective (n : Nat) : Function.Injective (expected n) := by
  intro i j hij
  have hi := (expected_indices n i).1
  have hj := (expected_indices n j).1
  have hindex := congrArg Slot.proofIndex hij
  rw [hi, hj] at hindex
  apply Fin.ext
  exact hindex

/-- Logical component identity excludes the transcript index. The pair
`(role, call ID)` is unique in the canonical roster, so reusing a claim
position cannot hide a duplicate chip or bridge. -/
def logicalIdentity (entry : Slot) : Role × Option Nat :=
  (entry.role, entry.callId)

theorem expected_logical_injective (n : Nat) :
    Function.Injective (logicalIdentity ∘ expected n) := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hmodi : (i.val - 1) % 2 + 2 * ((i.val - 1) / 2) = i.val - 1 :=
    Nat.mod_add_div _ _
  have hmodj : (j.val - 1) % 2 + 2 * ((j.val - 1) / 2) = j.val - 1 :=
    Nat.mod_add_div _ _
  unfold Function.comp logicalIdentity expected sourceSlot at hij
  by_cases iz : i.val = 0
  · by_cases jz : j.val = 0
    · exact Fin.ext (by omega)
    · simp [iz, jz, circuitSlot, chipSlot, bridgeSlot] at hij
      split_ifs at hij <;> simp_all
  · by_cases jz : j.val = 0
    · simp [iz, jz, circuitSlot, chipSlot, bridgeSlot] at hij
      split_ifs at hij <;> simp_all
    · by_cases ie : (i.val - 1) % 2 = 0
      · by_cases je : (j.val - 1) % 2 = 0
        · simp [iz, jz, ie, je, chipSlot] at hij
          apply Fin.ext
          omega
        · simp [iz, jz, ie, je, chipSlot, bridgeSlot] at hij
      · by_cases je : (j.val - 1) % 2 = 0
        · simp [iz, jz, ie, je, chipSlot, bridgeSlot] at hij
        · simp [iz, jz, ie, je, bridgeSlot] at hij
          have hie : (i.val - 1) % 2 = 1 := by omega
          have hje : (j.val - 1) % 2 = 1 := by omega
          apply Fin.ext
          omega

/-- The source identity fields are copied from the compiler-selected call.
The native manifest stores these in its `calls` array, while each component
entry stores the call number. -/
structure SourceCall where
  callId : Nat
  sourceNodeId : Nat
  inputNodeId : Nat
  rounds : Nat
  constant : Nat
  deriving DecidableEq, Repr

def entrySourceCall {n : Nat} (calls : Fin n → SourceCall)
    (entry : Slot) : Option SourceCall :=
  entry.callId.bind fun id =>
    if h : id < n then some (calls ⟨id, h⟩) else none

theorem circuit_has_no_source_call {n : Nat} (calls : Fin n → SourceCall) :
    entrySourceCall calls (expected n ⟨0, by omega⟩) = none := by
  simp [entrySourceCall, expected, sourceSlot, circuitSlot]

theorem chip_projects_source_call {n : Nat} (calls : Fin n → SourceCall)
    (call : Fin n) :
    entrySourceCall calls (expected n ⟨1 + 2 * call.val, by omega⟩) =
      some (calls call) := by
  simp [entrySourceCall, expected_chip, chipSlot, call.isLt]

theorem bridge_projects_source_call {n : Nat} (calls : Fin n → SourceCall)
    (call : Fin n) :
    entrySourceCall calls (expected n ⟨2 + 2 * call.val, by omega⟩) =
      some (calls call) := by
  simp [entrySourceCall, expected_bridge, bridgeSlot, call.isLt]

/-- The call IDs rejected by `inspection.zig` unless they equal their source
positions. This is an explicit assumption about the source inspection result. -/
def CanonicalCalls {n : Nat} (calls : Fin n → SourceCall) : Prop :=
  ∀ call, (calls call).callId = call.val

theorem chip_projects_canonical_call_id {n : Nat}
    (calls : Fin n → SourceCall) (h : CanonicalCalls calls)
    (call : Fin n) :
    (entrySourceCall calls (expected n ⟨1 + 2 * call.val, by omega⟩)).map
      SourceCall.callId = some call.val := by
  rw [chip_projects_source_call]
  simp [h call]

theorem bridge_projects_canonical_call_id {n : Nat}
    (calls : Fin n → SourceCall) (h : CanonicalCalls calls)
    (call : Fin n) :
    (entrySourceCall calls (expected n ⟨2 + 2 * call.val, by omega⟩)).map
      SourceCall.callId = some call.val := by
  rw [bridge_projects_source_call]
  simp [h call]

/-- Field-level acceptance premise of `registry_manifest.zig::fromSchedule`:
the source-inspected slots have the expected role, key, call ID, relations,
and both transcript indices at every position. The actual Zig equivalence
to this predicate remains a separate compiler/native refinement obligation. -/
structure CheckedProjection (n : Nat) where
  entries : Fin (1 + 2 * n) → Slot
  role_eq : ∀ index, (entries index).role = (expected n index).role
  key_eq : ∀ index, (entries index).key = (expected n index).key
  call_eq : ∀ index, (entries index).callId = (expected n index).callId
  proof_eq : ∀ index, (entries index).proofIndex = index.val
  sum_eq : ∀ index, (entries index).claimedSumIndex = index.val
  relation_eq : ∀ index, (entries index).relationIds = (expected n index).relationIds

theorem CheckedProjection.entry_eq {n : Nat} (checked : CheckedProjection n)
    (index : Fin (1 + 2 * n)) : checked.entries index = expected n index := by
  have hrole := checked.role_eq index
  have hkey := checked.key_eq index
  have hcall := checked.call_eq index
  have hrelation := checked.relation_eq index
  have hproof := checked.proof_eq index
  have hsum := checked.sum_eq index
  rw [← (expected_indices n index).1] at hproof
  rw [← (expected_indices n index).2] at hsum
  cases he : checked.entries index
  cases hx : expected n index
  simp_all

theorem CheckedProjection.exact_roster {n : Nat} (checked : CheckedProjection n) :
    List.ofFn checked.entries = List.ofFn (expected n) := by
  congr 1
  funext index
  exact checked.entry_eq index

theorem CheckedProjection.no_duplicate_slots {n : Nat}
    (checked : CheckedProjection n) : Function.Injective checked.entries := by
  intro i j hij
  rw [checked.entry_eq, checked.entry_eq] at hij
  exact expected_injective n hij

theorem CheckedProjection.no_duplicate_logical_components {n : Nat}
    (checked : CheckedProjection n) :
    Function.Injective (logicalIdentity ∘ checked.entries) := by
  intro i j hij
  have hi := checked.entry_eq i
  have hj := checked.entry_eq j
  dsimp [Function.comp] at hij
  rw [hi, hj] at hij
  exact expected_logical_injective n hij

theorem CheckedProjection.all_calls_present {n : Nat}
    (checked : CheckedProjection n) (call : Fin n) :
    checked.entries ⟨1 + 2 * call.val, by omega⟩ = chipSlot call.val ∧
    checked.entries ⟨2 + 2 * call.val, by omega⟩ = bridgeSlot call.val := by
  constructor
  · rw [checked.entry_eq, expected_chip]
  · rw [checked.entry_eq, expected_bridge]

theorem CheckedProjection.projects_source_calls {n : Nat}
    (checked : CheckedProjection n) (calls : Fin n → SourceCall)
    (call : Fin n) :
    entrySourceCall calls
      (checked.entries ⟨1 + 2 * call.val, by omega⟩) = some (calls call) ∧
    entrySourceCall calls
      (checked.entries ⟨2 + 2 * call.val, by omega⟩) = some (calls call) := by
  constructor
  · rw [checked.entry_eq, chip_projects_source_call]
  · rw [checked.entry_eq, bridge_projects_source_call]

theorem CheckedProjection.claimed_sum_positions {n : Nat}
    (checked : CheckedProjection n) (i j : Fin (1 + 2 * n))
    (h : (checked.entries i).claimedSumIndex =
      (checked.entries j).claimedSumIndex) : i = j := by
  apply Fin.ext
  simpa only [checked.sum_eq] using h

/-- The native policy supports exactly the nonempty one-to-eight-call band.
The arithmetic above is parametric; the bound matters at source admission. -/
def Supported (n : Nat) : Prop := 1 ≤ n ∧ n ≤ 8

theorem supported_entry_count {n : Nat} (h : Supported n) :
    3 ≤ (List.ofFn (expected n)).length ∧
    (List.ofFn (expected n)).length ≤ 17 := by
  rw [expected_count]
  dsimp [Supported] at h
  omega

end S31.Gadgets.Air.Manifest.InterleavedRoster
