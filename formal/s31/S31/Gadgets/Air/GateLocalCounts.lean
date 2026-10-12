import S31.Gadgets.Air.GateLogUpBridge

namespace S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.LogUpCount
open S31.Gadgets.Air.LogUpNumerator

theorem compressed_count_bound (left right : List Event)
    (alpha : GateSecure)
    (hgood : alpha ∉ badAlpha (left ++ right))
    (hcount : ∀ event ∈ left ++ right,
      left.count event < 2147483647) :
    ∀ value ∈ eventSupport (left.map (compressedEvent alpha))
      (right.map (compressedEvent alpha)),
      (left.map (compressedEvent alpha)).count value < 2147483647 := by
  let eventBEq : BEq Event := inferInstance
  classical
  letI : BEq Event := eventBEq
  intro value hvalue
  have hmapped : value ∈ (left ++ right).map (compressedEvent alpha) := by
    simpa [eventSupport, List.map_append] using hvalue
  obtain ⟨event, hevent, heq⟩ := List.mem_map.mp hmapped
  subst value
  rw [count_map_of_injective_on_list_lawful]
  · exact hcount event hevent
  · intro other hother hequal
    exact compressedEvent_injective_on (left ++ right) alpha hgood
      other (List.mem_append_left right hother) event hevent hequal

theorem compressed_right_count_bound (left right : List Event)
    (alpha : GateSecure)
    (hgood : alpha ∉ badAlpha (left ++ right))
    (hcount : ∀ event ∈ left ++ right,
      right.count event < 2147483647) :
    ∀ value ∈ eventSupport (left.map (compressedEvent alpha))
      (right.map (compressedEvent alpha)),
      (right.map (compressedEvent alpha)).count value < 2147483647 := by
  let eventBEq : BEq Event := inferInstance
  classical
  letI : BEq Event := eventBEq
  intro value hvalue
  have hmapped : value ∈ (left ++ right).map (compressedEvent alpha) := by
    simpa [eventSupport, List.map_append] using hvalue
  obtain ⟨event, hevent, heq⟩ := List.mem_map.mp hmapped
  subst value
  rw [count_map_of_injective_on_list_lawful]
  · exact hcount event hevent
  · intro other hother hequal
    exact compressedEvent_injective_on (left ++ right) alpha hgood
      other (List.mem_append_right left hother) event hevent hequal

theorem compressed_lists_bad_balance_card_le_of_counts
    (left right : List Event)
    (hleft : ∀ event ∈ left ++ right,
      left.count event < 2147483647)
    (hright : ∀ event ∈ left ++ right,
      right.count event < 2147483647)
    (hne : ¬ left.Perm right)
    (alpha : GateSecure)
    (hgood : alpha ∉ badAlpha (left ++ right)) :
    (badBalanceZ
      (eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha)))
      (netWeight (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha)))).card ≤
      (eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha))).card - 1 := by
  apply unequal_lists_bad_balance_card_le_of_counts
  · exact compressed_count_bound left right alpha hgood hleft
  · exact compressed_right_count_bound left right alpha hgood hright
  · exact compressed_lists_unbalanced left right alpha hgood hne

theorem badZ_card_le_of_counts (left right : List Event)
    (hleft : ∀ event ∈ left ++ right,
      left.count event < 2147483647)
    (hright : ∀ event ∈ left ++ right,
      right.count event < 2147483647)
    (hne : ¬ left.Perm right)
    (alpha : GateSecure)
    (hgood : alpha ∉ badAlpha (left ++ right)) :
    (badZ left right alpha).card ≤
      (eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha))).card +
      ((eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha))).card - 1) := by
  unfold badZ
  calc
    (eventSupport (left.map (compressedEvent alpha))
      (right.map (compressedEvent alpha)) ∪
      badBalanceZ
        (eventSupport (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha)))
        (netWeight (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha)))).card ≤
      (eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha))).card +
      (badBalanceZ
        (eventSupport (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha)))
        (netWeight (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha)))).card :=
        Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left
      (compressed_lists_bad_balance_card_le_of_counts
        left right hleft hright hne alpha hgood) _

/-- Larger fixed traces may have more than p total Gate events. Soundness
still follows when every *individual* canonical event count stays below p. -/
theorem fixed_gate_multiset_sound_of_counts
    (left right : List Event)
    (hcanonical : ∀ event ∈ left ++ right,
      event.1 < 2147483647)
    (hleft : ∀ event ∈ left ++ right,
      left.count event < 2147483647)
    (hright : ∀ event ∈ left ++ right,
      right.count event < 2147483647)
    (hne : ¬ left.Perm right) :
    (badAlpha (left ++ right)).card ≤
      5 * (left ++ right).toFinset.card ^ 2 ∧
    ∀ alpha ∉ badAlpha (left ++ right),
      (badZ left right alpha).card ≤
        (eventSupport (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha))).card +
        ((eventSupport (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha))).card - 1) ∧
      ∀ z ∉ badZ left right alpha,
        productionReciprocalSum left alpha z ≠
          productionReciprocalSum right alpha z := by
  refine ⟨badAlpha_card_le (left ++ right) hcanonical, ?_⟩
  intro alpha halpha
  refine ⟨badZ_card_le_of_counts left right hleft hright hne
    alpha halpha, ?_⟩
  intro z hz
  exact rejected_outside_exceptional_sets left right alpha z hz

end S31.Gadgets.Air.GateLogUpBridge
