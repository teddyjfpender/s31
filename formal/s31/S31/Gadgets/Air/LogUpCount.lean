import S31.Gadgets.Air.LogUpNumerator
import S31.Gadgets.Air.GateChallenge

namespace S31.Gadgets.Air.LogUpCount
set_option maxHeartbeats 600000
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Packed

theorem natCast_secure_injective_below (a b : Nat)
    (ha : a < 2147483647) (hb : b < 2147483647)
    (h : (a : GateSecure) = (b : GateSecure)) : a = b := by
  have hF : (a : F) = (b : F) := by
    simpa using congrArg (fun q : GateSecure => q.re.re) h
  have hval := congrArg ZMod.val hF
  simpa [ZMod.val_natCast_of_lt ha,
    ZMod.val_natCast_of_lt hb] using hval

def eventSupport (left right : List GateSecure) : Finset GateSecure :=
  (left ++ right).toFinset

def netWeight (left right : List GateSecure) (a : GateSecure) : GateSecure :=
  (left.count a : GateSecure) - (right.count a : GateSecure)

theorem unequal_lists_have_nonzero_weight
    (left right : List GateSecure)
    (hlength : left.length < 2147483647)
    (hrlength : right.length < 2147483647)
    (hne : ¬ left.Perm right) :
    ∃ a ∈ eventSupport left right, netWeight left right a ≠ 0 := by
  classical
  have hcount : ∃ a, left.count a ≠ right.count a := by
    by_contra hnot
    apply hne
    apply List.perm_iff_count.mpr
    intro a
    by_contra hneq
    exact hnot ⟨a, hneq⟩
  obtain ⟨a, hneq⟩ := hcount
  have hmem : a ∈ eventSupport left right := by
    by_contra hnot
    have hboth : a ∉ left ∧ a ∉ right := by
      simpa [eventSupport, List.mem_toFinset] using hnot
    have hlzero := List.count_eq_zero_of_not_mem hboth.1
    have hrzero := List.count_eq_zero_of_not_mem hboth.2
    exact hneq (hlzero.trans hrzero.symm)
  refine ⟨a, hmem, ?_⟩
  intro hzero
  have hcast : (left.count a : GateSecure) =
      (right.count a : GateSecure) :=
    sub_eq_zero.mp hzero
  apply hneq
  exact natCast_secure_injective_below _ _
    (lt_of_le_of_lt List.count_le_length hlength)
    (lt_of_le_of_lt List.count_le_length hrlength) hcast

/-- Total event count is only a convenient sufficient condition. The exact
characteristic premise is that each compressed value occurs fewer than p
times on either side. -/
theorem unequal_lists_have_nonzero_weight_of_counts
    (left right : List GateSecure)
    (hleft : ∀ a ∈ eventSupport left right,
      left.count a < 2147483647)
    (hright : ∀ a ∈ eventSupport left right,
      right.count a < 2147483647)
    (hne : ¬ left.Perm right) :
    ∃ a ∈ eventSupport left right, netWeight left right a ≠ 0 := by
  classical
  have hcount : ∃ a, left.count a ≠ right.count a := by
    by_contra hnot
    apply hne
    apply List.perm_iff_count.mpr
    intro a
    by_contra hneq
    exact hnot ⟨a, hneq⟩
  obtain ⟨a, hneq⟩ := hcount
  have hmem : a ∈ eventSupport left right := by
    by_contra hnot
    have hboth : a ∉ left ∧ a ∉ right := by
      simpa [eventSupport, List.mem_toFinset] using hnot
    exact hneq ((List.count_eq_zero_of_not_mem hboth.1).trans
      (List.count_eq_zero_of_not_mem hboth.2).symm)
  refine ⟨a, hmem, ?_⟩
  intro hzero
  apply hneq
  exact natCast_secure_injective_below _ _ (hleft a hmem)
    (hright a hmem) (sub_eq_zero.mp hzero)

theorem weighted_sum_count (l : List GateSecure)
    (support : Finset GateSecure)
    (hsub : ∀ a ∈ l, a ∈ support)
    (f : GateSecure → GateSecure) :
    (∑ a ∈ support, (l.count a : GateSecure) * f a) =
      (l.map f).sum := by
  classical
  induction l with
  | nil => simp
  | cons x xs ih =>
      have hx : x ∈ support := hsub x (by simp)
      have hrest : ∀ a ∈ xs, a ∈ support := by
        intro a ha
        exact hsub a (by simp [ha])
      have hih := ih hrest
      simp only [List.map_cons, List.sum_cons]
      simp_rw [List.count_cons, beq_iff_eq]
      simp only [Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have hsingle :
          (∑ a ∈ support, (if x = a then (1 : GateSecure) else 0) * f a) =
            f x := by
        simp [ite_mul, hx]
      rw [hsingle, hih]
      exact add_comm _ _

theorem net_weight_reciprocal_eq_lists (left right : List GateSecure)
    (z : GateSecure) :
    LogUpNumerator.reciprocalSum (eventSupport left right)
        (netWeight left right) z =
      (left.map fun a => 1 / (z - a)).sum -
      (right.map fun a => 1 / (z - a)).sum := by
  classical
  have hleft : ∀ a ∈ left, a ∈ eventSupport left right := by
    intro a ha
    simp [eventSupport, ha]
  have hright : ∀ a ∈ right, a ∈ eventSupport left right := by
    intro a ha
    simp [eventSupport, ha]
  have hl := weighted_sum_count left (eventSupport left right) hleft
    (fun a => 1 / (z - a))
  have hr := weighted_sum_count right (eventSupport left right) hright
    (fun a => 1 / (z - a))
  unfold LogUpNumerator.reciprocalSum netWeight
  simp_rw [sub_div]
  rw [Finset.sum_sub_distrib]
  simpa [div_eq_mul_inv] using congrArg₂ Sub.sub hl hr

theorem unequal_lists_bad_balance_card_le
    (left right : List GateSecure)
    (hlength : left.length < 2147483647)
    (hrlength : right.length < 2147483647)
    (hne : ¬ left.Perm right) :
    (LogUpNumerator.badBalanceZ (eventSupport left right)
      (netWeight left right)).card ≤
        (eventSupport left right).card - 1 := by
  obtain ⟨a, ha, hw⟩ := unequal_lists_have_nonzero_weight
    left right hlength hrlength hne
  exact LogUpNumerator.badBalanceZ_card_le
    (eventSupport left right) (netWeight left right) a ha hw

theorem unequal_lists_bad_balance_card_le_of_counts
    (left right : List GateSecure)
    (hleft : ∀ a ∈ eventSupport left right,
      left.count a < 2147483647)
    (hright : ∀ a ∈ eventSupport left right,
      right.count a < 2147483647)
    (hne : ¬ left.Perm right) :
    (LogUpNumerator.badBalanceZ (eventSupport left right)
      (netWeight left right)).card ≤
        (eventSupport left right).card - 1 := by
  obtain ⟨a, ha, hw⟩ := unequal_lists_have_nonzero_weight_of_counts
    left right hleft hright hne
  exact LogUpNumerator.badBalanceZ_card_le
    (eventSupport left right) (netWeight left right) a ha hw

theorem reciprocal_rejected_outside_bad_set
    (left right : List GateSecure)
    (z : GateSecure)
    (hz : z ∉ eventSupport left right)
    (hgood : z ∉ LogUpNumerator.badBalanceZ
      (eventSupport left right) (netWeight left right)) :
    (left.map fun a => 1 / (z - a)).sum ≠
      (right.map fun a => 1 / (z - a)).sum := by
  intro heq
  have hzsum : LogUpNumerator.reciprocalSum
      (eventSupport left right) (netWeight left right) z = 0 := by
    rw [net_weight_reciprocal_eq_lists]
    exact sub_eq_zero.mpr heq
  exact hgood (Finset.mem_filter.mpr
    ⟨Finset.mem_univ z, ⟨hz, hzsum⟩⟩)

theorem count_map_of_injective_on_list
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (l : List α) (f : α → β) (a : α)
    (hinj : ∀ b ∈ l, f b = f a → b = a) :
    (l.map f).count (f a) = l.count a := by
  induction l with
  | nil => simp
  | cons b bs ih =>
      have hrest : ∀ c ∈ bs, f c = f a → c = a := by
        intro c hc heq
        exact hinj c (by simp [hc]) heq
      have hih := ih hrest
      by_cases hba : b = a
      · subst b
        simp [hih]
      · have hfb : f b ≠ f a := by
          intro heq
          exact hba (hinj b (by simp) heq)
        simp [hba, hfb, hih]

/-- The same count-map law with the source's existing lawful `BEq` instance.
This avoids changing a concrete Gate event counter to a different equality
implementation when a proof introduces classical decidable equality. -/
theorem count_map_of_injective_on_list_lawful
    {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β]
    (l : List α) (f : α → β) (a : α)
    (hinj : ∀ b ∈ l, f b = f a → b = a) :
    (l.map f).count (f a) = l.count a := by
  induction l with
  | nil => simp
  | cons b bs ih =>
      have hrest : ∀ c ∈ bs, f c = f a → c = a := by
        intro c hc heq
        exact hinj c (by simp [hc]) heq
      have hih := ih hrest
      by_cases hba : b = a
      · subst b
        simp [hih]
      · have hfb : f b ≠ f a := by
          intro heq
          exact hba (hinj b (by simp) heq)
        simp [hba, hfb, hih]

theorem mapped_perm_reflects
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left right : List α) (f : α → β)
    (hinj : ∀ a ∈ left ++ right, ∀ b ∈ left ++ right,
      f a = f b → a = b)
    (hmap : (left.map f).Perm (right.map f)) :
    left.Perm right := by
  classical
  apply List.perm_iff_count.mpr
  intro a
  by_cases ha : a ∈ left ++ right
  · have hl : (left.map f).count (f a) = left.count a := by
      apply count_map_of_injective_on_list
      intro b hb heq
      exact hinj b (List.mem_append_left right hb) a ha heq
    have hr : (right.map f).count (f a) = right.count a := by
      apply count_map_of_injective_on_list
      intro b hb heq
      exact hinj b (List.mem_append_right left hb) a ha heq
    exact hl.symm.trans ((List.perm_iff_count.mp hmap) (f a) |>.trans hr)
  · have hb : a ∉ left ∧ a ∉ right := by
      simpa using ha
    simp [List.count_eq_zero_of_not_mem hb.1,
      List.count_eq_zero_of_not_mem hb.2]

/-- The field-size premise is substantive. A symbolic list of `p` copies
has zero net field weight against the empty list, even though the lists do
not balance as multisets. This proof rewrites the count without building
the large list. -/
theorem characteristic_wrap_example :
    netWeight (List.replicate 2147483647 (0 : GateSecure)) [] 0 = 0 := by
  simp only [netWeight, List.count_replicate, beq_self_eq_true, ↓reduceIte,
    List.count_nil, Nat.cast_zero, sub_zero]
  change liftBase (2147483647 : F) = liftBase 0
  exact congrArg liftBase (ZMod.natCast_self _)

end S31.Gadgets.Air.LogUpCount
