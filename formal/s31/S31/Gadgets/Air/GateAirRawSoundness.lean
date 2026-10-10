import S31.Gadgets.Air.GateAirChallengeSoundness

namespace S31.Gadgets.Air.GateAirRawSoundness
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateChallengePairs
open S31.Gadgets.Air.GateAirChallengeSoundness
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.Qm31GateInteraction
open S31.Gadgets.Air.LogUpInteraction

abbrev Event := S31.Gadgets.Air.GateLookup.Event

/-- Includes output tuples even when their multiplicity is zero. Such an
output has no Gate event, but a zero denominator can still make its AIR
singleton equation vacuous. -/
def denominatorEvents (rows : List Row) : List Event :=
  rows.flatMap fun row =>
    [(row.in0Address, row.in0), (row.in1Address, row.in1),
      (row.outAddress, row.output)]

theorem denominator_events_length (rows : List Row) :
    (denominatorEvents rows).length = 3 * rows.length := by
  induction rows with
  | nil => simp [denominatorEvents]
  | cons row rest ih =>
      simp [denominatorEvents]
      omega

noncomputable def zeroDenominatorPairs (rows : List Row) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact (Finset.univ : Finset GateSecure).biUnion fun alpha =>
    ((denominatorEvents rows).map (compressedEvent alpha)).toFinset.image
      fun z => (alpha, z)

theorem event_denominator_nonzero (rows : List Row)
    (event : Event) (hmem : event ∈ denominatorEvents rows)
    (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ zeroDenominatorPairs rows) :
    combineTerm (eventTuple event) alpha z ≠ 0 := by
  classical
  intro hzero
  apply hgood
  apply Finset.mem_biUnion.mpr
  refine ⟨alpha, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨compressedEvent alpha event, ?_, ?_⟩
  · exact List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨event, hmem, rfl⟩)
  · exact congrArg (fun value => (alpha, value))
      (((combineTerm_zero_iff (eventTuple event) alpha z).mp hzero).symm)

theorem row_denominator_members (rows : List Row) (row : Row)
    (hrow : row ∈ rows) :
    (row.in0Address, row.in0) ∈ denominatorEvents rows ∧
    (row.in1Address, row.in1) ∈ denominatorEvents rows ∧
    (row.outAddress, row.output) ∈ denominatorEvents rows := by
  constructor
  · exact List.mem_flatMap.mpr ⟨row, hrow, by simp⟩
  constructor
  · exact List.mem_flatMap.mpr ⟨row, hrow, by simp⟩
  · exact List.mem_flatMap.mpr ⟨row, hrow, by simp⟩

theorem zero_denominator_pairs_card_le (rows : List Row) :
    (zeroDenominatorPairs rows).card ≤
      Fintype.card GateSecure * (denominatorEvents rows).length := by
  classical
  unfold zeroDenominatorPairs
  calc
    ((Finset.univ : Finset GateSecure).biUnion fun alpha =>
      ((denominatorEvents rows).map (compressedEvent alpha)).toFinset.image
        fun z => (alpha, z)).card ≤
        ∑ alpha ∈ (Finset.univ : Finset GateSecure),
          (((denominatorEvents rows).map
            (compressedEvent alpha)).toFinset.image
            fun z => (alpha, z)).card := Finset.card_biUnion_le
    _ ≤ ∑ _alpha ∈ (Finset.univ : Finset GateSecure),
        (denominatorEvents rows).length := by
      apply Finset.sum_le_sum
      intro alpha _
      exact Finset.card_image_le.trans
        ((List.toFinset_card_le _).trans
          (by simp))
    _ = Fintype.card GateSecure * (denominatorEvents rows).length := by simp

/-- These are precisely the modeled raw AIR residual and external-claim
conditions. No denominator premise is assumed. -/
def rawInteractionAccepts (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure) : Prop :=
  ∃ firstColumn lastColumn : Fin (2 ^ logSize) → GateSecure,
  ∃ claimed : GateSecure,
    (∀ i, pairResidual (rowPair (rows i) alpha z).1
      (rowPair (rows i) alpha z).2 (firstColumn i) = 0) ∧
    (∀ i, singleResidual (yieldTerm (rows i) alpha z)
      (lastColumn i - lastColumn (prev i) - firstColumn i +
        claimed / ((2 ^ logSize : Nat) : GateSecure)) = 0) ∧
    claimed + productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0

noncomputable def rawAcceptingPairs (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List Event) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact Finset.univ.filter fun pair =>
    rawInteractionAccepts logSize prev rows externalUses externalYields
      pair.1 pair.2

noncomputable def exceptionalPairs (rows : List Row)
    (externalUses externalYields : List Event) :
    Finset (GateSecure × GateSecure) :=
  badPairs (allUses rows externalUses) (allYields rows externalYields) ∪
    zeroDenominatorPairs rows

theorem raw_accepting_pairs_subset_exceptional (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List Event) :
    rawAcceptingPairs logSize prev rows externalUses externalYields ⊆
      exceptionalPairs (List.ofFn rows) externalUses externalYields := by
  classical
  intro pair hpair
  by_contra hnot
  have hnotBad : pair ∉ badPairs
      (allUses (List.ofFn rows) externalUses)
      (allYields (List.ofFn rows) externalYields) := by
    exact fun h => hnot (Finset.mem_union_left _ h)
  have hnotZero : pair ∉ zeroDenominatorPairs (List.ofFn rows) := by
    exact fun h => hnot (Finset.mem_union_right _ h)
  obtain ⟨firstColumn, lastColumn, claimed,
    hpairair, hlastair, hclosed⟩ := (Finset.mem_filter.mp hpair).2
  have hrow (i : Fin (2 ^ logSize)) : rows i ∈ List.ofFn rows := by simp
  have hden (i : Fin (2 ^ logSize)) :=
    row_denominator_members (List.ofFn rows) (rows i) (hrow i)
  have huse0 : ∀ i, (useTerm ((rows i).in0Address, (rows i).in0)
      pair.1 pair.2).denominator ≠ 0 := by
    intro i
    exact event_denominator_nonzero _ _ (hden i).1 _ _ hnotZero
  have huse1 : ∀ i, (useTerm ((rows i).in1Address, (rows i).in1)
      pair.1 pair.2).denominator ≠ 0 := by
    intro i
    exact event_denominator_nonzero _ _ (hden i).2.1 _ _ hnotZero
  have hyield : ∀ i, (yieldTerm (rows i) pair.1 pair.2).denominator ≠ 0 := by
    intro i
    exact event_denominator_nonzero _ _ (hden i).2.2 _ _ hnotZero
  have hguarded : pair ∈ acceptingPairs logSize prev rows
      externalUses externalYields := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, ⟨firstColumn, lastColumn, claimed,
      huse0, huse1, hyield, hpairair, hlastair, hclosed⟩⟩
  exact hnotBad ((accepting_pairs_subset_bad_pairs logSize prev rows
    externalUses externalYields) hguarded)

theorem raw_false_acceptance_card_le (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List Event)
    (hcanonical : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      (allUses (List.ofFn rows) externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      (allYields (List.ofFn rows) externalYields).count event < 2147483647)
    (hwrong : ¬ (allUses (List.ofFn rows) externalUses).Perm
      (allYields (List.ofFn rows) externalYields)) :
    (rawAcceptingPairs logSize prev rows externalUses externalYields).card ≤
      (5 * (allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn rows) externalUses ++
          allYields (List.ofFn rows) externalYields).toFinset.card +
        (denominatorEvents (List.ofFn rows)).length) *
        Fintype.card GateSecure := by
  have hbase := bad_pairs_card_le
    (allUses (List.ofFn rows) externalUses)
    (allYields (List.ofFn rows) externalYields)
    hcanonical huses hyields hwrong
  have hzero := zero_denominator_pairs_card_le (List.ofFn rows)
  calc
    (rawAcceptingPairs logSize prev rows externalUses externalYields).card ≤
        (exceptionalPairs (List.ofFn rows)
          externalUses externalYields).card :=
      Finset.card_le_card (raw_accepting_pairs_subset_exceptional
        logSize prev rows externalUses externalYields)
    _ ≤ (badPairs (allUses (List.ofFn rows) externalUses)
        (allYields (List.ofFn rows) externalYields)).card +
          (zeroDenominatorPairs (List.ofFn rows)).card :=
      Finset.card_union_le _ _
    _ ≤ (5 * (allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn rows) externalUses ++
          allYields (List.ofFn rows) externalYields).toFinset.card) *
          Fintype.card GateSecure +
        Fintype.card GateSecure *
          (denominatorEvents (List.ofFn rows)).length :=
      Nat.add_le_add hbase hzero
    _ = _ := by ring

end S31.Gadgets.Air.GateAirRawSoundness
