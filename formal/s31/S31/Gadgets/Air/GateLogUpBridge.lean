import S31.Gadgets.Air.LogUpCount

namespace S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.LogUpCount
open S31.Gadgets.Air.GateLookup

abbrev Event := GateLookup.Event

def compressedEvent (alpha : GateSecure) (event : Event) : GateSecure :=
  tupleHorner (eventTuple event) alpha

noncomputable def eventPairs (events : List Event) : List (Event × Event) := by
  classical
  exact ((events.toFinset.toList).product (events.toFinset.toList)).filter
    (fun pair => pair.1 ≠ pair.2)

noncomputable def pairTuples (events : List Event) :
    List ((Fin 6 → GateSecure) × (Fin 6 → GateSecure)) :=
  (eventPairs events).map fun pair =>
    (eventTuple pair.1, eventTuple pair.2)

theorem eventPairs_mem (events : List Event) (a b : Event)
    (ha : a ∈ events) (hb : b ∈ events) (hne : a ≠ b) :
    (a, b) ∈ eventPairs events := by
  classical
  simp [eventPairs, ha, hb, hne]

theorem pairTuples_mem (events : List Event) (a b : Event)
    (ha : a ∈ events) (hb : b ∈ events) (hne : a ≠ b) :
    (eventTuple a, eventTuple b) ∈ pairTuples events := by
  apply List.mem_map.mpr
  exact ⟨(a,b), eventPairs_mem events a b ha hb hne, rfl⟩

theorem eventPairs_facts (events : List Event) (a b : Event)
    (h : (a,b) ∈ eventPairs events) :
    a ∈ events ∧ b ∈ events ∧ a ≠ b := by
  classical
  have hp : (a ∈ events ∧ b ∈ events) ∧ a ≠ b := by
    simpa [eventPairs] using h
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

theorem pairTuples_distinct (events : List Event)
    (hcanonical : ∀ event ∈ events, event.1 < 2147483647) :
    ∀ pair ∈ pairTuples events, pair.1 ≠ pair.2 := by
  intro pair hp
  obtain ⟨⟨a,b⟩, hab, heq⟩ := List.mem_map.mp hp
  obtain ⟨ha,hb,hne⟩ := eventPairs_facts events a b hab
  subst pair
  intro htuple
  exact hne (eventTuple_injective_of_canonical a b
    (hcanonical a ha) (hcanonical b hb) htuple)

theorem pairTuples_length_le (events : List Event) :
    (pairTuples events).length ≤ events.toFinset.card ^ 2 := by
  classical
  calc
    (pairTuples events).length = (eventPairs events).length := by
      simp [pairTuples]
    _ ≤ ((events.toFinset.toList).product
        (events.toFinset.toList)).length := by
      exact List.length_filter_le _ _
    _ = events.toFinset.card ^ 2 := by
      change (events.toFinset.toList ×ˢ events.toFinset.toList).length = _
      rw [List.length_product]
      simp [pow_two]

noncomputable def badAlpha (events : List Event) : Finset GateSecure :=
  collisionUnion (pairTuples events)

theorem badAlpha_card_le (events : List Event)
    (hcanonical : ∀ event ∈ events, event.1 < 2147483647) :
    (badAlpha events).card ≤ 5 * events.toFinset.card ^ 2 := by
  calc
    (badAlpha events).card ≤ 5 * (pairTuples events).length := by
      exact collisionUnion_card_le _ (pairTuples_distinct events hcanonical)
    _ ≤ 5 * events.toFinset.card ^ 2 := by
      exact Nat.mul_le_mul_left _ (pairTuples_length_le events)

theorem mem_collisionUnion_of_mem
    (pairs : List ((Fin 6 → GateSecure) × (Fin 6 → GateSecure)))
    (pair : (Fin 6 → GateSecure) × (Fin 6 → GateSecure))
    (alpha : GateSecure)
    (hp : pair ∈ pairs)
    (hc : alpha ∈ collisionChallenges pair.1 pair.2) :
    alpha ∈ collisionUnion pairs := by
  induction pairs with
  | nil => cases hp
  | cons head tail ih =>
      rcases List.mem_cons.mp hp with rfl | htail
      · exact Finset.mem_union_left _ hc
      · exact Finset.mem_union_right _ (ih htail)

theorem compressedEvent_injective_on (events : List Event)
    (alpha : GateSecure) (hgood : alpha ∉ badAlpha events)
    (a : Event) (ha : a ∈ events)
    (b : Event) (hb : b ∈ events)
    (heq : compressedEvent alpha a = compressedEvent alpha b) :
    a = b := by
  by_contra hne
  have hp := pairTuples_mem events a b ha hb hne
  have hc : alpha ∈ collisionChallenges (eventTuple a) (eventTuple b) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
  exact hgood (mem_collisionUnion_of_mem
    (pairTuples events) (eventTuple a, eventTuple b) alpha hp hc)

theorem compressed_lists_unbalanced (left right : List Event)
    (alpha : GateSecure)
    (hgood : alpha ∉ badAlpha (left ++ right))
    (hne : ¬ left.Perm right) :
    ¬ (left.map (compressedEvent alpha)).Perm
        (right.map (compressedEvent alpha)) := by
  intro hmap
  apply hne
  exact mapped_perm_reflects left right (compressedEvent alpha)
    (fun a ha b hb heq => compressedEvent_injective_on
      (left ++ right) alpha hgood a ha b hb heq) hmap

theorem compressed_lists_bad_balance_card_le (left right : List Event)
    (hlength : left.length < 2147483647)
    (hrlength : right.length < 2147483647)
    (hne : ¬ left.Perm right)
    (alpha : GateSecure)
    (hgood : alpha ∉ badAlpha (left ++ right)) :
    (LogUpNumerator.badBalanceZ
      (eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha)))
      (netWeight (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha)))).card ≤
      (eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha))).card - 1 := by
  apply unequal_lists_bad_balance_card_le
  · simpa using hlength
  · simpa using hrlength
  · exact compressed_lists_unbalanced left right alpha hgood hne

def productionReciprocalSum (events : List Event)
    (alpha z : GateSecure) : GateSecure :=
  (events.map fun event => 1 / combineTerm (eventTuple event) alpha z).sum

theorem productionReciprocalSum_eq_neg (events : List Event)
    (alpha z : GateSecure) :
    productionReciprocalSum events alpha z =
      - (events.map fun event =>
        1 / (z - compressedEvent alpha event)).sum := by
  induction events with
  | nil => simp [productionReciprocalSum]
  | cons event rest ih =>
      unfold productionReciprocalSum
      simp only [List.map_cons, List.sum_cons]
      rw [show (rest.map fun e => 1 / combineTerm (eventTuple e) alpha z).sum =
        productionReciprocalSum rest alpha z from rfl, ih]
      have hden : combineTerm (eventTuple event) alpha z =
          -(z - compressedEvent alpha event) := by
        simp [combineTerm, compressedEvent]
      rw [hden, div_neg]
      ring

theorem production_reciprocal_rejected
    (left right : List Event)
    (alpha : GateSecure)
    (z : GateSecure)
    (hz : z ∉ eventSupport (left.map (compressedEvent alpha))
      (right.map (compressedEvent alpha)))
    (hgood : z ∉ LogUpNumerator.badBalanceZ
      (eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha)))
      (netWeight (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha)))) :
    productionReciprocalSum left alpha z ≠
      productionReciprocalSum right alpha z := by
  have hrec := reciprocal_rejected_outside_bad_set
    (left.map (compressedEvent alpha))
    (right.map (compressedEvent alpha)) z hz hgood
  intro heq
  rw [productionReciprocalSum_eq_neg,
    productionReciprocalSum_eq_neg] at heq
  apply hrec
  exact neg_injective (by simpa only [List.map_map] using heq)

noncomputable def badZ (left right : List Event)
    (alpha : GateSecure) : Finset GateSecure :=
  let support := eventSupport (left.map (compressedEvent alpha))
    (right.map (compressedEvent alpha))
  support ∪ LogUpNumerator.badBalanceZ support
    (netWeight (left.map (compressedEvent alpha))
      (right.map (compressedEvent alpha)))

theorem badZ_card_le (left right : List Event)
    (hlength : left.length < 2147483647)
    (hrlength : right.length < 2147483647)
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
      LogUpNumerator.badBalanceZ
        (eventSupport (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha)))
        (netWeight (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha)))).card ≤
      (eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha))).card +
      (LogUpNumerator.badBalanceZ
        (eventSupport (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha)))
        (netWeight (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha)))).card :=
        Finset.card_union_le _ _
    _ ≤ _ := Nat.add_le_add_left
      (compressed_lists_bad_balance_card_le left right hlength
        hrlength hne alpha hgood) _

theorem rejected_outside_exceptional_sets
    (left right : List Event)
    (alpha z : GateSecure)
    (hz : z ∉ badZ left right alpha) :
    productionReciprocalSum left alpha z ≠
      productionReciprocalSum right alpha z := by
  have hparts :
      z ∉ eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha)) ∧
      z ∉ LogUpNumerator.badBalanceZ
        (eventSupport (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha)))
        (netWeight (left.map (compressedEvent alpha))
          (right.map (compressedEvent alpha))) := by
    simpa [badZ] using hz
  exact production_reciprocal_rejected left right alpha z
    hparts.1 hparts.2

/-- Fixed canonical Gate multisets: outside explicit exceptional challenge
sets, the exact production-order reciprocal sums cannot close when the
multisets differ. This theorem does not model the interaction AIR or the
Fiat–Shamir transcript. -/
theorem fixed_gate_multiset_sound
    (left right : List Event)
    (hcanonical : ∀ event ∈ left ++ right,
      event.1 < 2147483647)
    (hlength : left.length < 2147483647)
    (hrlength : right.length < 2147483647)
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
  refine ⟨badZ_card_le left right hlength hrlength hne alpha halpha, ?_⟩
  intro z hz
  exact rejected_outside_exceptional_sets left right alpha z hz

end S31.Gadgets.Air.GateLogUpBridge
