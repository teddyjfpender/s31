import S31.Gadgets.Air.SourceMixedPath

/-!
Arithmetic lookup bounds for the source-pinned 512-row mixed family. This
module counts *occurrences*, including repeated Gate output lookups and chip
endpoints. `SourceShape` is an explicit native-to-Lean correspondence premise:
the current native fixture checks the 512 fixed rows for N=1 and N=8, and a
separate N=1..8 producer-roster fixture checks their multiplicities, but no
theorem here promotes those honest fixture checks into proof authentication.

The ideal tuple lists here have one event per chip row and per chip endpoint.
Native bridge fractions are repeated on sixteen trace rows; this model's
exact-event reduction uses their telescope, so the numeric bound below is
for the ideal source-shaped lists, not the wider whole-AIR lookup budget.
-/

namespace S31.Gadgets.Air.SourceMixedLookupBound

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge

/-- Native source-family dimensions, stated as an explicit correspondence
contract. In this family there are no external baseline Gate events: input
and constant producers are circuit rows, while the nine public and eight-per-
call bridge occurrences consume Gate outputs. The output multiplicity total
is 1033+8N for the 512-row, zero-permutation family. -/
structure SourceShape {N : Nat} (boundary : Boundary N) : Prop where
  rows : boundary.rows.length = 512
  multiplicity : (boundary.rows.map CanonicalRow.multiplicity).sum =
    1033 + 8 * N
  baselineUses : boundary.baselineUses = []
  baselineYields : boundary.baselineYields = []
  rounds : ∀ call, boundary.rounds call = 16

private theorem gate_row_uses_length (rows : List CanonicalRow) :
    ((rows.map CanonicalRow.toGate).flatMap Row.uses).length =
      2 * rows.length := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
      simp [Row.uses, ih]
      omega

private theorem gate_row_yields_length (rows : List CanonicalRow) :
    ((rows.map CanonicalRow.toGate).flatMap Row.yields).length =
      (rows.map CanonicalRow.multiplicity).sum := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
      simp [Row.yields, CanonicalRow.toGate, ih]

theorem circuit_uses_length {N : Nat} (boundary : Boundary N) :
    boundary.jointGateSource.circuitUses.length =
      2 * boundary.rows.length + boundary.baselineUses.length +
        9 + 8 * N := by
  unfold GateSource.circuitUses GateSource.gateRows
    GateSource.gateExternalUses allUses
  simp only [List.length_map, List.length_append]
  rw [gate_row_uses_length]
  simp [Boundary.jointGateSource, Boundary.publicFeeder,
    Boundary.bridgeGates_length]
  omega

theorem circuit_yields_length {N : Nat} (boundary : Boundary N) :
    boundary.jointGateSource.circuitYields.length =
      (boundary.rows.map CanonicalRow.multiplicity).sum +
        boundary.baselineYields.length := by
  unfold GateSource.circuitYields GateSource.gateRows
    GateSource.gateExternalYields allYields
  simp only [List.length_map, List.length_append]
  rw [gate_row_yields_length]
  simp [Boundary.jointGateSource]

private theorem joint_uses_length {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hrounds : ∀ call, boundary.rounds call = 16) :
    (jointUses rows boundary.finish).length = 17 * N := by
  have hcall (call : Fin N) :
      (callUses rows boundary.finish call).length = 17 := by
    simp [callUses, hrounds call]
  have hflat (xs : List (Fin N)) :
      (xs.flatMap (callUses rows boundary.finish)).length =
        17 * xs.length := by
    induction xs with
    | nil => simp
    | cons call rest ih =>
        simp [List.flatMap_cons, hcall call, ih]
        omega
  simpa [jointUses] using hflat (List.finRange N)

private theorem joint_yields_length {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hrounds : ∀ call, boundary.rounds call = 16) :
    (jointYields rows boundary.start).length = 17 * N := by
  have hcall (call : Fin N) :
      (callYields rows boundary.start call).length = 17 := by
    simp [callYields, hrounds call]
  have hflat (xs : List (Fin N)) :
      (xs.flatMap (callYields rows boundary.start)).length =
        17 * xs.length := by
    induction xs with
    | nil => simp
    | cons call rest ih =>
        simp [List.flatMap_cons, hcall call, ih]
        omega
  simpa [jointYields] using hflat (List.finRange N)

/-- Both sides of the ideal joint closure have precisely 1033+25N tuple
occurrences. This discharges the two separate `< p` hypotheses used by the
false-closure lemma from source-shape facts. -/
theorem joint_lengths {N : Nat} (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hshape : SourceShape boundary) :
    (boundary.jointGateSource.circuitUses ++
      jointUses rows boundary.finish).length = 1033 + 25 * N ∧
    (boundary.jointGateSource.circuitYields ++
      jointYields rows boundary.start).length = 1033 + 25 * N := by
  constructor
  · rw [List.length_append, circuit_uses_length,
      joint_uses_length boundary rows hshape.rounds,
      hshape.rows, hshape.baselineUses]
    simp
    omega
  · rw [List.length_append, circuit_yields_length,
      joint_yields_length boundary rows hshape.rounds,
      hshape.multiplicity, hshape.baselineYields]
    simp
    omega

/-- Each event in the signed ideal closure has a canonical Gate address or
the fixed chip relation tag. The relation tag prevents a Gate event from
being mistaken for a chip event after seven-coordinate padding. -/
theorem joint_events_canonical_tags {N : Nat} (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow) :
    (∀ event ∈ boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish,
      (∃ address : CanonicalAddress, ∃ value : Quad,
        event = embedGateEvent (address.val, value)) ∨
        IsChipEvent event) ∧
    (∀ event ∈ boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start,
      (∃ address : CanonicalAddress, ∃ value : Quad,
        event = embedGateEvent (address.val, value)) ∨
        IsChipEvent event) := by
  constructor
  · intro event hmem
    rcases List.mem_append.mp hmem with hgate | hchip
    · obtain ⟨gate, hsource, rfl⟩ := List.mem_map.mp hgate
      exact Or.inl ⟨⟨gate.1,
        boundary.jointGateSource.canonical_uses gate hsource⟩,
        gate.2, rfl⟩
    · exact Or.inr (jointUses_chip_only rows boundary.finish event hchip)
  · intro event hmem
    rcases List.mem_append.mp hmem with hgate | hchip
    · obtain ⟨gate, hsource, rfl⟩ := List.mem_map.mp hgate
      exact Or.inl ⟨⟨gate.1,
        boundary.jointGateSource.canonical_yields gate hsource⟩,
        gate.2, rfl⟩
    · exact Or.inr (jointYields_chip_only rows boundary.start event hchip)
/-- Every positive/negative tuple multiplicity is below the M31
characteristic for the admitted one-to-eight-call source shape. Gate
addresses are canonical by `Boundary`'s `Fin p` types; chip call and step
coordinates are M31 values by `NativeRow` and `nativeTuple`. -/
theorem joint_multiplicities_bounded {N : Nat} (hN : N ≤ 8)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hshape : SourceShape boundary) (event : JointTuple) :
    (boundary.jointGateSource.circuitUses ++
      jointUses rows boundary.finish).count event < 2147483647 ∧
    (boundary.jointGateSource.circuitYields ++
      jointYields rows boundary.start).count event < 2147483647 := by
  obtain ⟨hleft, hright⟩ := joint_lengths boundary rows hshape
  constructor
  · have h :
        (boundary.jointGateSource.circuitUses ++
          jointUses rows boundary.finish).count event ≤
        (boundary.jointGateSource.circuitUses ++
          jointUses rows boundary.finish).length := List.count_le_length
    omega
  · have h :
        (boundary.jointGateSource.circuitYields ++
          jointYields rows boundary.start).count event ≤
        (boundary.jointGateSource.circuitYields ++
          jointYields rows boundary.start).length := List.count_le_length
    omega

/-- For any *unbalanced fixed* ideal event roster of this admitted source
shape, at most `36,491,868·|QM31|` independent challenge pairs can fall in
the explicit collision/pole/cancellation exceptional set. The exceptional
set is strictly smaller than the full pair space. This is conditional
algebra; native AIR/PCS/FRI and transcript sampling are not premises proved
here. -/
theorem source_false_closure_pair_bound {N : Nat} (hN : N ≤ 8)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hshape : SourceShape boundary)
    (hne : ¬ (boundary.jointGateSource.circuitUses ++
      jointUses rows boundary.finish).Perm
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start)) :
    (badPairs7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish)
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start)).card ≤
      36491868 * Fintype.card GateSecure := by
  let left := boundary.jointGateSource.circuitUses ++
    jointUses rows boundary.finish
  let right := boundary.jointGateSource.circuitYields ++
    jointYields rows boundary.start
  obtain ⟨hleft, hright⟩ := joint_lengths boundary rows hshape
  change left.length = 1033 + 25 * N at hleft
  change right.length = 1033 + 25 * N at hright
  have hleftp : left.length < 2147483647 := by omega
  have hrightp : right.length < 2147483647 := by omega
  have hsupport : (left ++ right).toFinset.card ≤ 2466 := by
    have h := List.toFinset_card_le (left ++ right)
    simp only [List.length_append] at h
    omega
  have hsquare : (left ++ right).toFinset.card ^ 2 ≤ 2466 ^ 2 :=
    Nat.pow_le_pow_left hsupport 2
  have hfactor :
      6 * (left ++ right).toFinset.card ^ 2 +
        2 * (left ++ right).toFinset.card ≤ 36491868 := by
    omega
  exact (badPairs7_card_le left right hleftp hrightp hne).trans
    (Nat.mul_le_mul_right (Fintype.card GateSecure) hfactor)

/-- The error event is empty when the exact lists balance. Otherwise the
concrete source-family bound applies. This is the nonvacuous form to use with
an honest witness and with `closed_pair_balance_or_error`. -/
theorem source_imbalance_pair_bound {N : Nat} (hN : N ≤ 8)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hshape : SourceShape boundary) :
    (imbalancePairs7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish)
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start)).card ≤
      36491868 * Fintype.card GateSecure := by
  classical
  let left := boundary.jointGateSource.circuitUses ++
    jointUses rows boundary.finish
  let right := boundary.jointGateSource.circuitYields ++
    jointYields rows boundary.start
  by_cases hbalanced :
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish).Perm
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start)
  · simp [imbalancePairs7, hbalanced]
  · simpa [imbalancePairs7, hbalanced] using
      source_false_closure_pair_bound hN boundary rows hshape hbalanced

theorem source_error_pairs_proper {N : Nat} (hN : N ≤ 8)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hshape : SourceShape boundary) :
    (imbalancePairs7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish)
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start)).card <
      (Fintype.card GateSecure) ^ 2 := by
  have hbound := source_imbalance_pair_bound hN boundary rows hshape
  have hq : 36491868 < Fintype.card GateSecure := by
    rw [card_secure]
    norm_num
  have hqpositive : 0 < Fintype.card GateSecure := Fintype.card_pos
  have hstrict := Nat.mul_lt_mul_of_pos_right hq hqpositive
  nlinarith

/-- A closed ideal reciprocal relation either reflects exact Gate/chip
event balance or falls in the bounded fixed-witness error set. There is no
verifier-acceptance or Fiat--Shamir conclusion in this theorem. -/
theorem source_closed_or_error {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (alpha z : GateSecure)
    (hclosed : productionReciprocalSum7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish) alpha z =
      productionReciprocalSum7
        (boundary.jointGateSource.circuitYields ++
          jointYields rows boundary.start) alpha z) :
    ((boundary.jointGateSource.circuitUses ++
      jointUses rows boundary.finish).Perm
        (boundary.jointGateSource.circuitYields ++
          jointYields rows boundary.start)) ∨
      (alpha, z) ∈ imbalancePairs7
        (boundary.jointGateSource.circuitUses ++
          jointUses rows boundary.finish)
        (boundary.jointGateSource.circuitYields ++
          jointYields rows boundary.start) := by
  exact closed_pair_balance_or_error _ _ alpha z hclosed

end S31.Gadgets.Air.SourceMixedLookupBound
