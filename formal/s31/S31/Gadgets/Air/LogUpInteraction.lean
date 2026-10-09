import S31.Gadgets.Air.GateChallenge

namespace S31.Gadgets.Air.LogUpInteraction
open S31.Gadgets.Air.GateChallenge

variable {K : Type*} [Field K]

structure Term (K : Type*) where
  numerator : K
  denominator : K

def singleResidual (term : Term K) (diff : K) : K :=
  diff * term.denominator - term.numerator

def pairResidual (left right : Term K) (diff : K) : K :=
  diff * (left.denominator * right.denominator) -
    (right.numerator * left.denominator +
      left.numerator * right.denominator)

theorem singleResidual_iff (term : Term K) (diff : K)
    (hden : term.denominator ≠ 0) :
    singleResidual term diff = 0 ↔
      diff = term.numerator / term.denominator := by
  unfold singleResidual
  rw [sub_eq_zero, eq_div_iff hden]

theorem pairResidual_iff (left right : Term K) (diff : K)
    (hleft : left.denominator ≠ 0)
    (hright : right.denominator ≠ 0) :
    pairResidual left right diff = 0 ↔
      diff = left.numerator / left.denominator +
        right.numerator / right.denominator := by
  unfold pairResidual
  rw [sub_eq_zero]
  constructor
  · intro h
    apply (eq_div_iff (mul_ne_zero hleft hright)).mpr at h
    rw [h]
    field_simp [hleft, hright]
    ring
  · intro h
    rw [h]
    field_simp [hleft, hright]
    ring

theorem claimed_sum_of_cyclic_recurrence
    (n : Nat) (prev : Equiv.Perm (Fin n))
    (trace increment : Fin n → K) (shift claimed : K)
    (hshift : (n : K) * shift = claimed)
    (hrow : ∀ i, trace i - trace (prev i) = increment i - shift) :
    claimed = ∑ i, increment i := by
  have hsum :
      (∑ i, (trace i - trace (prev i))) =
        ∑ i, (increment i - shift) := by
    exact Finset.sum_congr rfl (fun i _ => hrow i)
  have hprev : (∑ i, trace (prev i)) = ∑ i, trace i :=
    Equiv.sum_comp prev trace
  have hconst : (∑ _i : Fin n, shift) = (n : K) * shift := by
    simp
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    hprev, hconst, hshift] at hsum
  have hzero : (∑ i, increment i) - claimed = 0 := by
    simpa only [sub_self] using hsum.symm
  exact (sub_eq_zero.mp hzero).symm

/-- The non-final interaction columns within one row: each new column
adds its batch of one or two fractions to the preceding column. -/
def prefixAccepted (start : K) : List K → List K → K → Prop
  | [], [], finish => finish = start
  | batch :: batches, column :: columns, finish =>
      column - start = batch ∧
        prefixAccepted column batches columns finish
  | _, _, _ => False

theorem prefixAccepted_end (start : K) (batches columns : List K)
    (finish : K) (h : prefixAccepted start batches columns finish) :
    finish = start + batches.sum := by
  induction batches generalizing start columns with
  | nil =>
      cases columns with
      | nil => simpa [prefixAccepted] using h
      | cons _ _ => simp [prefixAccepted] at h
  | cons batch rest ih =>
      cases columns with
      | nil => simp [prefixAccepted] at h
      | cons column more =>
          obtain ⟨hstep, htail⟩ := h
          have hend := ih column more htail
          simp only [List.sum_cons]
          rw [hend]
          have hcolumn : column = start + batch := by
            exact (sub_eq_iff_eq_add.mp hstep).trans (add_comm _ _)
          rw [hcolumn]
          ring

theorem prefixAccepted_complete (start : K) (batches : List K) :
    ∃ columns finish, prefixAccepted start batches columns finish ∧
      finish = start + batches.sum := by
  induction batches generalizing start with
  | nil => exact ⟨[], start, rfl, by simp⟩
  | cons batch rest ih =>
      obtain ⟨columns, finish, htail, hend⟩ := ih (start + batch)
      refine ⟨(start + batch) :: columns, finish, ?_, ?_⟩
      · exact ⟨by ring, htail⟩
      · simp only [List.sum_cons]
        rw [hend]
        ring

theorem claimed_sum_of_batched_interaction
    (n : Nat) (prev : Equiv.Perm (Fin n))
    (batches columns : Fin n → List K)
    (lastBatch priorLast trace : Fin n → K)
    (shift claimed : K)
    (hprefix : ∀ i, prefixAccepted 0 (batches i) (columns i) (priorLast i))
    (hfinal : ∀ i,
      trace i - trace (prev i) - priorLast i + shift = lastBatch i)
    (hshift : (n : K) * shift = claimed) :
    claimed = ∑ i, ((batches i).sum + lastBatch i) := by
  apply claimed_sum_of_cyclic_recurrence n prev trace
    (fun i => (batches i).sum + lastBatch i) shift claimed hshift
  intro i
  have hprior : priorLast i = (batches i).sum := by
    simpa using prefixAccepted_end 0 (batches i)
      (columns i) (priorLast i) (hprefix i)
  have hi := hfinal i
  rw [hprior] at hi
  linear_combination hi

theorem zero_pair_denominators_accept_any_diff (diff : K) :
    pairResidual (Term.mk 1 0) (Term.mk 1 0) diff = 0 := by
  simp [pairResidual]

def pairValue (pair : Term K × Term K) : K :=
  pair.1.numerator / pair.1.denominator +
    pair.2.numerator / pair.2.denominator

def pairPrefixAccepted (start : K) :
    List (Term K × Term K) → List K → K → Prop
  | [], [], finish => finish = start
  | pair :: pairs, column :: columns, finish =>
      pairResidual pair.1 pair.2 (column - start) = 0 ∧
        pairPrefixAccepted column pairs columns finish
  | _, _, _ => False

theorem pairPrefixAccepted_implies_prefixAccepted
    (start : K) (pairs : List (Term K × Term K))
    (columns : List K) (finish : K)
    (hden : ∀ pair ∈ pairs,
      pair.1.denominator ≠ 0 ∧ pair.2.denominator ≠ 0)
    (hair : pairPrefixAccepted start pairs columns finish) :
    prefixAccepted start (pairs.map pairValue) columns finish := by
  induction pairs generalizing start columns with
  | nil =>
      cases columns with
      | nil => simpa [pairPrefixAccepted, prefixAccepted] using hair
      | cons _ _ => simp [pairPrefixAccepted] at hair
  | cons pair rest ih =>
      cases columns with
      | nil => simp [pairPrefixAccepted] at hair
      | cons column more =>
          obtain ⟨hhead, htail⟩ := hair
          have hpair := hden pair (by simp)
          have hrest : ∀ p ∈ rest,
              p.1.denominator ≠ 0 ∧ p.2.denominator ≠ 0 := by
            intro p hp
            exact hden p (by simp [hp])
          exact ⟨(pairResidual_iff pair.1 pair.2
            (column - start) hpair.1 hpair.2).mp hhead,
            ih column more hrest htail⟩

abbrev FinalTerm (K : Type*) := Term K ⊕ (Term K × Term K)

def finalValue : FinalTerm K → K
  | .inl term => term.numerator / term.denominator
  | .inr pair => pairValue pair

def finalResidual (batch : FinalTerm K) (diff : K) : K :=
  match batch with
  | .inl term => singleResidual term diff
  | .inr pair => pairResidual pair.1 pair.2 diff

def finalNonzero : FinalTerm K → Prop
  | .inl term => term.denominator ≠ 0
  | .inr pair =>
      pair.1.denominator ≠ 0 ∧ pair.2.denominator ≠ 0

theorem finalResidual_iff (batch : FinalTerm K) (diff : K)
    (hden : finalNonzero batch) :
    finalResidual batch diff = 0 ↔ diff = finalValue batch := by
  cases batch with
  | inl term => exact singleResidual_iff term diff hden
  | inr pair => exact pairResidual_iff pair.1 pair.2 diff hden.1 hden.2

theorem claimed_sum_of_checked_interaction
    (n : Nat) (prev : Equiv.Perm (Fin n))
    (pairs : Fin n → List (Term K × Term K))
    (columns : Fin n → List K)
    (last : Fin n → FinalTerm K)
    (priorLast trace : Fin n → K)
    (shift claimed : K)
    (hpairden : ∀ i, ∀ pair ∈ pairs i,
      pair.1.denominator ≠ 0 ∧ pair.2.denominator ≠ 0)
    (hpairair : ∀ i,
      pairPrefixAccepted 0 (pairs i) (columns i) (priorLast i))
    (hlastden : ∀ i, finalNonzero (last i))
    (hlastair : ∀ i,
      finalResidual (last i)
        (trace i - trace (prev i) - priorLast i + shift) = 0)
    (hshift : (n : K) * shift = claimed) :
    claimed = ∑ i : Fin n,
      (((pairs i).map pairValue).sum + finalValue (last i)) := by
  apply claimed_sum_of_batched_interaction n prev
    (fun i => (pairs i).map pairValue) columns
    (fun i => finalValue (last i)) priorLast trace shift claimed
  · intro i
    exact pairPrefixAccepted_implies_prefixAccepted 0
      (pairs i) (columns i) (priorLast i)
      (hpairden i) (hpairair i)
  · intro i
    exact (finalResidual_iff (last i)
      (trace i - trace (prev i) - priorLast i + shift)
      (hlastden i)).mp (hlastair i)
  · exact hshift

theorem gateSecure_pow_two_nonzero (k : Nat) :
    (((2 ^ k : Nat) : GateSecure)) ≠ 0 := by
  have hbase : (2 : S31.Gadgets.Packed.F) ≠ 0 := by
    intro h
    have hval := congrArg ZMod.val h
    have htwo : ZMod.val (2 : S31.Gadgets.Packed.F) = 2 := by decide
    rw [htwo, ZMod.val_zero] at hval
    omega
  have hpow : ((2 ^ k : Nat) : S31.Gadgets.Packed.F) ≠ 0 := by
    simpa only [Nat.cast_pow] using pow_ne_zero k hbase
  intro hzero
  change liftBase ((2 ^ k : Nat) : S31.Gadgets.Packed.F) = liftBase 0 at hzero
  exact hpow (liftBase_injective hzero)

theorem claimed_sum_of_checked_power_two_interaction
    (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (pairs : Fin (2 ^ logSize) → List (Term GateSecure × Term GateSecure))
    (columns : Fin (2 ^ logSize) → List GateSecure)
    (last : Fin (2 ^ logSize) → FinalTerm GateSecure)
    (priorLast trace : Fin (2 ^ logSize) → GateSecure)
    (claimed : GateSecure)
    (hpairden : ∀ i, ∀ pair ∈ pairs i,
      pair.1.denominator ≠ 0 ∧ pair.2.denominator ≠ 0)
    (hpairair : ∀ i,
      pairPrefixAccepted 0 (pairs i) (columns i) (priorLast i))
    (hlastden : ∀ i, finalNonzero (last i))
    (hlastair : ∀ i,
      finalResidual (last i)
        (trace i - trace (prev i) - priorLast i +
          claimed / ((2 ^ logSize : Nat) : GateSecure)) = 0) :
    claimed = ∑ i : Fin (2 ^ logSize),
      (((pairs i).map pairValue).sum + finalValue (last i)) := by
  apply claimed_sum_of_checked_interaction (2 ^ logSize) prev
    pairs columns last priorLast trace
    (claimed / ((2 ^ logSize : Nat) : GateSecure)) claimed
    hpairden hpairair hlastden hlastair
  exact mul_div_cancel₀ claimed (gateSecure_pow_two_nonzero logSize)

end S31.Gadgets.Air.LogUpInteraction
