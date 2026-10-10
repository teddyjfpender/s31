import S31.Gadgets.Air.GateAirRawSoundness
import S31.Gadgets.Air.EqGateInteraction

namespace S31.Gadgets.Air.GateEqRawSoundness
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateChallengePairs
open S31.Gadgets.Air.GateAirRawSoundness
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.Qm31GateInteraction
open S31.Gadgets.Air.EqGateInteraction
open S31.Gadgets.Air.EqRows
open S31.Gadgets.Air.LogUpInteraction

abbrev Event := S31.Gadgets.Air.GateLookup.Event

/-- The arithmetic and Eq interaction AIRs share one Gate relation. The
committed rows are fixed; all interaction columns and claims may depend on
the challenge pair. No denominator premise is part of acceptance. -/
def combinedRawAccepts (arithLogSize eqLogSize : Nat)
    (arithPrev : Equiv.Perm (Fin (2 ^ arithLogSize)))
    (eqPrev : Equiv.Perm (Fin (2 ^ eqLogSize)))
    (arithRows : Fin (2 ^ arithLogSize) → Row)
    (eqRows : Fin (2 ^ eqLogSize) → EqRow)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure) : Prop :=
  ∃ arithFirst arithLast : Fin (2 ^ arithLogSize) → GateSecure,
  ∃ eqColumn : Fin (2 ^ eqLogSize) → GateSecure,
  ∃ arithClaim eqClaim : GateSecure,
    (∀ i, pairResidual (rowPair (arithRows i) alpha z).1
      (rowPair (arithRows i) alpha z).2 (arithFirst i) = 0) ∧
    (∀ i, singleResidual (yieldTerm (arithRows i) alpha z)
      (arithLast i - arithLast (arithPrev i) - arithFirst i +
        arithClaim / ((2 ^ arithLogSize : Nat) : GateSecure)) = 0) ∧
    (∀ i, pairResidual (eqPair (eqRows i) alpha z).1
      (eqPair (eqRows i) alpha z).2
      (eqColumn i - eqColumn (eqPrev i) +
        eqClaim / ((2 ^ eqLogSize : Nat) : GateSecure)) = 0) ∧
    arithClaim + eqClaim +
      productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0

noncomputable def combinedAcceptingPairs (arithLogSize eqLogSize : Nat)
    (arithPrev : Equiv.Perm (Fin (2 ^ arithLogSize)))
    (eqPrev : Equiv.Perm (Fin (2 ^ eqLogSize)))
    (arithRows : Fin (2 ^ arithLogSize) → Row)
    (eqRows : Fin (2 ^ eqLogSize) → EqRow)
    (externalUses externalYields : List Event) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact Finset.univ.filter fun pair =>
    combinedRawAccepts arithLogSize eqLogSize arithPrev eqPrev
      arithRows eqRows externalUses externalYields pair.1 pair.2

theorem eq_use_in_combined_events
    (arithRows : List Row) (eqRows : List EqRow)
    (externalUses externalYields : List Event)
    (r : EqRow) (hr : r ∈ eqRows) (event : Event)
    (huse : event ∈ r.uses) :
    event ∈ allUses arithRows
      (eqRows.flatMap EqRow.uses ++ externalUses) ++
        allYields arithRows externalYields := by
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨r, hr, huse⟩

/-- Raw Eq residual acceptance reduces to exact Eq Gate use terms outside
the shared bad-pair set. Eq introduces no zero-multiplicity output tuple. -/
theorem combined_accepting_pairs_subset_exceptional
    (arithLogSize eqLogSize : Nat)
    (arithPrev : Equiv.Perm (Fin (2 ^ arithLogSize)))
    (eqPrev : Equiv.Perm (Fin (2 ^ eqLogSize)))
    (arithRows : Fin (2 ^ arithLogSize) → Row)
    (eqRows : Fin (2 ^ eqLogSize) → EqRow)
    (externalUses externalYields : List Event) :
    combinedAcceptingPairs arithLogSize eqLogSize arithPrev eqPrev
      arithRows eqRows externalUses externalYields ⊆
      exceptionalPairs (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)
        externalYields := by
  classical
  intro pair hpair
  by_contra hnot
  have hnotBad : pair ∉ badPairs
      (allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses))
      (allYields (List.ofFn arithRows) externalYields) := by
    exact fun h => hnot (Finset.mem_union_left _ h)
  obtain ⟨arithFirst, arithLast, eqColumn, arithClaim, eqClaim,
    harithPair, harithLast, heqAir, hclosed⟩ :=
      (Finset.mem_filter.mp hpair).2
  have heqRow (i : Fin (2 ^ eqLogSize)) :
      eqRows i ∈ List.ofFn eqRows := by simp
  have heq0 : ∀ i, (eqPair (eqRows i) pair.1 pair.2).1.denominator ≠ 0 := by
    intro i
    apply event_denominator_nonzero_of_not_bad_pair
      (allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses))
      (allYields (List.ofFn arithRows) externalYields)
      ((eqRows i).leftAddress, (eqRows i).value)
    · exact eq_use_in_combined_events _ _ _ _ _ (heqRow i) _
        (by simp [EqRow.uses])
    · exact hnotBad
  have heq1 : ∀ i, (eqPair (eqRows i) pair.1 pair.2).2.denominator ≠ 0 := by
    intro i
    apply event_denominator_nonzero_of_not_bad_pair
      (allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses))
      (allYields (List.ofFn arithRows) externalYields)
      ((eqRows i).rightAddress, (eqRows i).value)
    · exact eq_use_in_combined_events _ _ _ _ _ (heqRow i) _
        (by simp [EqRow.uses])
    · exact hnotBad
  have heqClaim := eq_claimed_sum_eq_event_sum eqLogSize eqPrev
    eqRows eqColumn pair.1 pair.2 eqClaim heq0 heq1 heqAir
  have harithRaw : pair ∈ rawAcceptingPairs arithLogSize arithPrev
      arithRows ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)
      externalYields := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, arithFirst, arithLast, arithClaim,
      harithPair, harithLast, ?_⟩
    rw [productionReciprocalSum_append, ← heqClaim]
    simpa only [add_assoc] using hclosed
  exact hnot ((raw_accepting_pairs_subset_exceptional
    arithLogSize arithPrev arithRows
    ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)
    externalYields) harithRaw)

/-- The Eq component's raw interaction AIR adds no new exceptional field
choices beyond the arithmetic-row denominator set and the shared Gate
multiset collision set. -/
theorem combined_false_acceptance_card_le
    (arithLogSize eqLogSize : Nat)
    (arithPrev : Equiv.Perm (Fin (2 ^ arithLogSize)))
    (eqPrev : Equiv.Perm (Fin (2 ^ eqLogSize)))
    (arithRows : Fin (2 ^ arithLogSize) → Row)
    (eqRows : Fin (2 ^ eqLogSize) → EqRow)
    (externalUses externalYields : List Event)
    (hcanonical : ∀ event ∈
      allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
        allYields (List.ofFn arithRows) externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
        allYields (List.ofFn arithRows) externalYields,
      (allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)).count event <
        2147483647)
    (hyields : ∀ event ∈
      allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
        allYields (List.ofFn arithRows) externalYields,
      (allYields (List.ofFn arithRows) externalYields).count event <
        2147483647)
    (hwrong : ¬ (allUses (List.ofFn arithRows)
      ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)).Perm
      (allYields (List.ofFn arithRows) externalYields)) :
    (combinedAcceptingPairs arithLogSize eqLogSize arithPrev eqPrev
      arithRows eqRows externalUses externalYields).card ≤
      (5 * (allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
        allYields (List.ofFn arithRows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn arithRows)
          ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
          allYields (List.ofFn arithRows) externalYields).toFinset.card +
        (denominatorEvents (List.ofFn arithRows)).length) *
        Fintype.card GateSecure := by
  have hbase := bad_pairs_card_le
    (allUses (List.ofFn arithRows)
      ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses))
    (allYields (List.ofFn arithRows) externalYields)
    hcanonical huses hyields hwrong
  have hzero := zero_denominator_pairs_card_le
    (List.ofFn arithRows)
  calc
    (combinedAcceptingPairs arithLogSize eqLogSize arithPrev eqPrev
      arithRows eqRows externalUses externalYields).card ≤
        (exceptionalPairs (List.ofFn arithRows)
          ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)
          externalYields).card :=
      Finset.card_le_card (combined_accepting_pairs_subset_exceptional
    arithLogSize eqLogSize arithPrev eqPrev arithRows eqRows
    externalUses externalYields)
    _ ≤ (badPairs (allUses (List.ofFn arithRows)
      ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses))
      (allYields (List.ofFn arithRows) externalYields)).card +
      (zeroDenominatorPairs (List.ofFn arithRows)).card :=
      Finset.card_union_le _ _
    _ ≤ (5 * (allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
        allYields (List.ofFn arithRows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn arithRows)
          ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
          allYields (List.ofFn arithRows) externalYields).toFinset.card) *
          Fintype.card GateSecure +
        Fintype.card GateSecure *
          (denominatorEvents (List.ofFn arithRows)).length :=
      Nat.add_le_add hbase hzero
    _ = _ := by ring

/-- A false equality assertion has the same fixed-trace challenge bound.
Both Eq reads must refer to uniquely produced Gate values. -/
theorem false_eq_raw_acceptance_card_le
    (arithLogSize eqLogSize : Nat)
    (arithPrev : Equiv.Perm (Fin (2 ^ arithLogSize)))
    (eqPrev : Equiv.Perm (Fin (2 ^ eqLogSize)))
    (arithRows : Fin (2 ^ arithLogSize) → Row)
    (eqRows : Fin (2 ^ eqLogSize) → EqRow)
    (externalUses externalYields : List Event)
    (r : EqRow) (hr : r ∈ List.ofFn eqRows)
    (left right : S31.Gadgets.Packed.Quad)
    (hunique : uniqueProduced
      (allYields (List.ofFn arithRows) externalYields))
    (hleft : (r.leftAddress, left) ∈
      allYields (List.ofFn arithRows) externalYields)
    (hright : (r.rightAddress, right) ∈
      allYields (List.ofFn arithRows) externalYields)
    (hfalse : left ≠ right)
    (hcanonical : ∀ event ∈
      allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
        allYields (List.ofFn arithRows) externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
        allYields (List.ofFn arithRows) externalYields,
      (allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)).count event <
        2147483647)
    (hyields : ∀ event ∈
      allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
        allYields (List.ofFn arithRows) externalYields,
      (allYields (List.ofFn arithRows) externalYields).count event <
        2147483647) :
    (combinedAcceptingPairs arithLogSize eqLogSize arithPrev eqPrev
      arithRows eqRows externalUses externalYields).card ≤
      (5 * (allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
        allYields (List.ofFn arithRows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn arithRows)
          ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
          allYields (List.ofFn arithRows) externalYields).toFinset.card +
        (denominatorEvents (List.ofFn arithRows)).length) *
        Fintype.card GateSecure := by
  have hwrong : ¬ (allUses (List.ofFn arithRows)
      ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)).Perm
      (allYields (List.ofFn arithRows) externalYields) := by
    intro hbalanced
    exact hfalse (eq_row_sound_of_shared_gate
      (List.ofFn arithRows) (List.ofFn eqRows)
      externalUses externalYields r hr hbalanced hunique
      left right hleft hright)
  exact combined_false_acceptance_card_le arithLogSize eqLogSize
    arithPrev eqPrev arithRows eqRows externalUses externalYields
    hcanonical huses hyields hwrong

end S31.Gadgets.Air.GateEqRawSoundness
