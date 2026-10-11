import S31.Gadgets.Air.GateLocalCounts

namespace S31.Gadgets.Air.GateChallengePairs
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.LogUpCount

abbrev Event := S31.Gadgets.Air.GateLookup.Event

theorem support_card_le_distinct_events
    (left right : List Event) (alpha : GateSecure) :
    (eventSupport (left.map (compressedEvent alpha))
      (right.map (compressedEvent alpha))).card ≤
      (left ++ right).toFinset.card := by
  classical
  have heq : eventSupport (left.map (compressedEvent alpha))
      (right.map (compressedEvent alpha)) =
      (left ++ right).toFinset.image (compressedEvent alpha) := by
    ext value
    simp only [eventSupport, List.mem_toFinset, List.mem_append,
      List.mem_map, Finset.mem_image]
    aesop
  rw [heq]
  exact Finset.card_image_le

theorem bad_z_card_le_distinct_events
    (left right : List Event)
    (hleft : ∀ event ∈ left ++ right,
      left.count event < 2147483647)
    (hright : ∀ event ∈ left ++ right,
      right.count event < 2147483647)
    (hne : ¬ left.Perm right)
    (alpha : GateSecure) (hgood : alpha ∉ badAlpha (left ++ right)) :
    (badZ left right alpha).card ≤
      2 * (left ++ right).toFinset.card := by
  have hbad := badZ_card_le_of_counts left right
    hleft hright hne alpha hgood
  have hsupport := support_card_le_distinct_events left right alpha
  omega

noncomputable def badPairs (left right : List Event) :
    Finset (GateSecure × GateSecure) := by
  classical
  let badA := badAlpha (left ++ right)
  exact (badA.product (Finset.univ : Finset GateSecure)) ∪
    ((Finset.univ : Finset GateSecure).biUnion fun alpha =>
      if alpha ∈ badA then ∅
      else (badZ left right alpha).image fun z => (alpha, z))

/-- A fixed unequal Gate multiset can falsely close only on a bounded set
of ideal, independently sampled challenge pairs. -/
theorem bad_pairs_card_le
    (left right : List Event)
    (hcanonical : ∀ event ∈ left ++ right,
      event.1 < 2147483647)
    (hleft : ∀ event ∈ left ++ right,
      left.count event < 2147483647)
    (hright : ∀ event ∈ left ++ right,
      right.count event < 2147483647)
    (hne : ¬ left.Perm right) :
    (badPairs left right).card ≤
      (5 * (left ++ right).toFinset.card ^ 2 +
        2 * (left ++ right).toFinset.card) *
        Fintype.card GateSecure := by
  classical
  let s := (left ++ right).toFinset.card
  let n := Fintype.card GateSecure
  let badA := badAlpha (left ++ right)
  let badGood := (Finset.univ : Finset GateSecure).biUnion fun alpha =>
    if alpha ∈ badA then ∅
    else (badZ left right alpha).image fun z => (alpha, z)
  have hgoodCount : badGood.card ≤ n * (2 * s) := by
    calc
      badGood.card ≤ ∑ alpha ∈ (Finset.univ : Finset GateSecure),
          (if alpha ∈ badA then (∅ : Finset (GateSecure × GateSecure))
          else (badZ left right alpha).image
            fun z => (alpha, z)).card := Finset.card_biUnion_le
      _ ≤ ∑ _alpha ∈ (Finset.univ : Finset GateSecure),
          2 * s := by
        apply Finset.sum_le_sum
        intro alpha _
        by_cases ha : alpha ∈ badA
        · simp [ha]
        · simp only [ha, ↓reduceIte]
          exact Finset.card_image_le.trans
            (bad_z_card_le_distinct_events left right
              hleft hright hne alpha ha)
      _ = n * (2 * s) := by simp [n]
  have hbadA : badA.card ≤ 5 * s ^ 2 := by
    exact badAlpha_card_le (left ++ right) hcanonical
  change (badA.product (Finset.univ : Finset GateSecure) ∪
    badGood).card ≤ (5 * s ^ 2 + 2 * s) * n
  calc
    (badA.product (Finset.univ : Finset GateSecure) ∪ badGood).card ≤
        (badA.product (Finset.univ : Finset GateSecure)).card +
          badGood.card := Finset.card_union_le _ _
    _ ≤ badA.card * n + n * (2 * s) := by
      simpa [Finset.card_product, n] using
        Nat.add_le_add_left hgoodCount (badA.card * n)
    _ ≤ (5 * s ^ 2) * n + n * (2 * s) := by
      exact Nat.add_le_add_right (Nat.mul_le_mul_right n hbadA) _
    _ = (5 * s ^ 2 + 2 * s) * n := by ring

theorem reciprocal_closure_implies_bad_pair
    (left right : List Event)
    (alpha z : GateSecure)
    (hclosed : productionReciprocalSum left alpha z =
      productionReciprocalSum right alpha z) :
    (alpha, z) ∈ badPairs left right := by
  classical
  by_contra hnot
  let badA := badAlpha (left ++ right)
  let badGood := (Finset.univ : Finset GateSecure).biUnion fun a =>
    if a ∈ badA then ∅
    else (badZ left right a).image fun b => (a, b)
  have hnotA : alpha ∉ badA := by
    intro ha
    apply hnot
    change (alpha, z) ∈
      badA.product (Finset.univ : Finset GateSecure) ∪ badGood
    exact Finset.mem_union_left _ (Finset.mem_product.mpr
      ⟨ha, Finset.mem_univ z⟩)
  have hnotZ : z ∉ badZ left right alpha := by
    intro hz
    apply hnot
    change (alpha, z) ∈
      badA.product (Finset.univ : Finset GateSecure) ∪ badGood
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨alpha, Finset.mem_univ _, ?_⟩
    simp [hnotA, hz]
  exact (rejected_outside_exceptional_sets left right alpha z hnotZ)
    hclosed

/-- Any event denominator is nonzero outside the explicit bad-pair set.
This matters because the AIR fraction equations alone do not constrain a
zero denominator. -/
theorem event_denominator_nonzero_of_not_bad_pair
    (left right : List Event) (event : Event)
    (hmem : event ∈ left ++ right)
    (alpha z : GateSecure)
    (hpair : (alpha, z) ∉ badPairs left right) :
    combineTerm (eventTuple event) alpha z ≠ 0 := by
  classical
  have hnotA : alpha ∉ badAlpha (left ++ right) := by
    intro ha
    apply hpair
    apply Finset.mem_union_left
    exact Finset.mem_product.mpr ⟨ha, Finset.mem_univ z⟩
  have hnotZ : z ∉ badZ left right alpha := by
    intro hz
    apply hpair
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨alpha, Finset.mem_univ _, ?_⟩
    simp [hnotA, hz]
  have hsupport : compressedEvent alpha event ∈
      eventSupport (left.map (compressedEvent alpha))
        (right.map (compressedEvent alpha)) := by
    simp only [eventSupport, List.mem_toFinset, List.mem_append,
      List.mem_map]
    rcases List.mem_append.mp hmem with hl | hr
    · exact Or.inl ⟨event, hl, rfl⟩
    · exact Or.inr ⟨event, hr, rfl⟩
  have hzne : z ≠ compressedEvent alpha event := by
    intro heq
    apply hnotZ
    apply Finset.mem_union_left
    exact heq.symm ▸ hsupport
  intro hzero
  exact hzne ((combineTerm_zero_iff
    (eventTuple event) alpha z).mp hzero)

/-- For an ideal independent uniform pair from QM31², the false-closure
fraction is at most `(5s² + 2s) / p⁴`, where `s` is the number of distinct
canonical Gate events. -/
theorem uniform_pair_failure_rate_le
    (left right : List Event)
    (hcanonical : ∀ event ∈ left ++ right,
      event.1 < 2147483647)
    (hleft : ∀ event ∈ left ++ right,
      left.count event < 2147483647)
    (hright : ∀ event ∈ left ++ right,
      right.count event < 2147483647)
    (hne : ¬ left.Perm right) :
    ((badPairs left right).card : ℚ) /
      (Fintype.card GateSecure : ℚ) ^ 2 ≤
      (((5 * (left ++ right).toFinset.card ^ 2 +
        2 * (left ++ right).toFinset.card : Nat) : ℚ) /
        (Fintype.card GateSecure : ℚ)) := by
  let n := Fintype.card GateSecure
  let b := 5 * (left ++ right).toFinset.card ^ 2 +
    2 * (left ++ right).toFinset.card
  have hnat := bad_pairs_card_le left right hcanonical
    hleft hright hne
  have hcast : ((badPairs left right).card : ℚ) ≤
      ((b * n : Nat) : ℚ) := by
    exact_mod_cast hnat
  have hn : (0 : ℚ) < n := by
    dsimp [n]
    rw [card_secure]
    positivity
  have hn0 : (n : ℚ) ≠ 0 := ne_of_gt hn
  change ((badPairs left right).card : ℚ) / (n : ℚ) ^ 2 ≤
    (b : ℚ) / (n : ℚ)
  calc
    ((badPairs left right).card : ℚ) / (n : ℚ) ^ 2 ≤
        ((b * n : Nat) : ℚ) / (n : ℚ) ^ 2 :=
      div_le_div_of_nonneg_right hcast (sq_nonneg _)
    _ = (b : ℚ) / (n : ℚ) := by
      push_cast
      field_simp

end S31.Gadgets.Air.GateChallengePairs
