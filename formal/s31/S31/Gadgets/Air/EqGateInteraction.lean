import S31.Gadgets.Air.Qm31GateInteraction
import S31.Gadgets.Air.EqRows

namespace S31.Gadgets.Air.EqGateInteraction
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.LogUpInteraction
open S31.Gadgets.Air.Qm31GateInteraction
open S31.Gadgets.Air.EqRows

def eqPair (row : EqRow) (alpha z : GateSecure) :
    Term GateSecure × Term GateSecure :=
  (useTerm (row.leftAddress, row.value) alpha z,
    useTerm (row.rightAddress, row.value) alpha z)

theorem eq_pair_value_eq_event_sum (row : EqRow)
    (alpha z : GateSecure) :
    pairValue (eqPair row alpha z) =
      productionReciprocalSum row.uses alpha z := by
  simp [eqPair, useTerm, pairValue, EqRow.uses,
    productionReciprocalSum]

theorem eq_claimed_sum
    (logSize : Nat) (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → EqRow)
    (column : Fin (2 ^ logSize) → GateSecure)
    (alpha z claimed : GateSecure)
    (hleft : ∀ i, (eqPair (rows i) alpha z).1.denominator ≠ 0)
    (hright : ∀ i, (eqPair (rows i) alpha z).2.denominator ≠ 0)
    (hair : ∀ i,
      pairResidual (eqPair (rows i) alpha z).1
        (eqPair (rows i) alpha z).2
        (column i - column (prev i) +
          claimed / ((2 ^ logSize : Nat) : GateSecure)) = 0) :
    claimed = ∑ i : Fin (2 ^ logSize),
      productionReciprocalSum (rows i).uses alpha z := by
  apply claimed_sum_of_cyclic_recurrence
    (2 ^ logSize) prev column
    (fun i => productionReciprocalSum (rows i).uses alpha z)
    (claimed / ((2 ^ logSize : Nat) : GateSecure)) claimed
  · exact mul_div_cancel₀ claimed (gateSecure_pow_two_nonzero logSize)
  · intro i
    have hpair := (pairResidual_iff _ _ _ (hleft i) (hright i)).mp (hair i)
    change column i - column (prev i) +
      claimed / ((2 ^ logSize : Nat) : GateSecure) =
      pairValue (eqPair (rows i) alpha z) at hpair
    rw [eq_pair_value_eq_event_sum] at hpair
    linear_combination hpair

theorem eq_rows_event_sum (rows : List EqRow)
    (alpha z : GateSecure) :
    productionReciprocalSum (rows.flatMap EqRow.uses) alpha z =
      (rows.map fun row => productionReciprocalSum row.uses alpha z).sum := by
  induction rows with
  | nil => simp [productionReciprocalSum]
  | cons row rest ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [productionReciprocalSum_append, ih]

theorem eq_claimed_sum_eq_event_sum
    (logSize : Nat) (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → EqRow)
    (column : Fin (2 ^ logSize) → GateSecure)
    (alpha z claimed : GateSecure)
    (hleft : ∀ i, (eqPair (rows i) alpha z).1.denominator ≠ 0)
    (hright : ∀ i, (eqPair (rows i) alpha z).2.denominator ≠ 0)
    (hair : ∀ i,
      pairResidual (eqPair (rows i) alpha z).1
        (eqPair (rows i) alpha z).2
        (column i - column (prev i) +
          claimed / ((2 ^ logSize : Nat) : GateSecure)) = 0) :
    claimed = productionReciprocalSum
      ((List.ofFn rows).flatMap EqRow.uses) alpha z := by
  have h := eq_claimed_sum logSize prev rows column alpha z claimed
    hleft hright hair
  rw [eq_rows_event_sum]
  simpa [List.map_ofFn, List.sum_ofFn] using h

/-- The two exact circuit components share one Gate closure. Other components
and public terms are represented by the external event lists. -/
theorem qm31_and_eq_closed_gate_balanced
    (arithLogSize eqLogSize : Nat)
    (arithPrev : Equiv.Perm (Fin (2 ^ arithLogSize)))
    (eqPrev : Equiv.Perm (Fin (2 ^ eqLogSize)))
    (arithRows : Fin (2 ^ arithLogSize) → GateLookup.Row)
    (eqRows : Fin (2 ^ eqLogSize) → EqRow)
    (arithFirst arithLast : Fin (2 ^ arithLogSize) → GateSecure)
    (eqColumn : Fin (2 ^ eqLogSize) → GateSecure)
    (externalUses externalYields : List GateLookup.Event)
    (alpha z arithClaim eqClaim : GateSecure)
    (hcanonical : ∀ event ∈
      GateLookup.allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
      GateLookup.allYields (List.ofFn arithRows) externalYields,
      event.1 < 2147483647)
    (huses : ∀ address,
      addressCount (GateLookup.allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)) address <
        2147483647)
    (hyields : ∀ address,
      addressCount (GateLookup.allYields
        (List.ofFn arithRows) externalYields) address < 2147483647)
    (halpha : alpha ∉ badAlpha
      (GateLookup.allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses) ++
      GateLookup.allYields (List.ofFn arithRows) externalYields))
    (hz : z ∉ badZ
      (GateLookup.allUses (List.ofFn arithRows)
        ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses))
      (GateLookup.allYields (List.ofFn arithRows) externalYields) alpha)
    (harith0 : ∀ i,
      (useTerm ((arithRows i).in0Address, (arithRows i).in0)
        alpha z).denominator ≠ 0)
    (harith1 : ∀ i,
      (useTerm ((arithRows i).in1Address, (arithRows i).in1)
        alpha z).denominator ≠ 0)
    (harithYield : ∀ i,
      (yieldTerm (arithRows i) alpha z).denominator ≠ 0)
    (harithPair : ∀ i,
      pairResidual (rowPair (arithRows i) alpha z).1
        (rowPair (arithRows i) alpha z).2 (arithFirst i) = 0)
    (harithLast : ∀ i,
      singleResidual (yieldTerm (arithRows i) alpha z)
        (arithLast i - arithLast (arithPrev i) - arithFirst i +
          arithClaim / ((2 ^ arithLogSize : Nat) : GateSecure)) = 0)
    (heq0 : ∀ i, (eqPair (eqRows i) alpha z).1.denominator ≠ 0)
    (heq1 : ∀ i, (eqPair (eqRows i) alpha z).2.denominator ≠ 0)
    (heqAir : ∀ i,
      pairResidual (eqPair (eqRows i) alpha z).1
        (eqPair (eqRows i) alpha z).2
        (eqColumn i - eqColumn (eqPrev i) +
          eqClaim / ((2 ^ eqLogSize : Nat) : GateSecure)) = 0)
    (hclosed : arithClaim + eqClaim +
      productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0) :
    GateLookup.balanced (List.ofFn arithRows)
      ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)
      externalYields := by
  have heqSum := eq_claimed_sum_eq_event_sum eqLogSize eqPrev
    eqRows eqColumn alpha z eqClaim heq0 heq1 heqAir
  apply qm31_ops_closed_gate_balanced arithLogSize arithPrev
    arithRows arithFirst arithLast
    ((List.ofFn eqRows).flatMap EqRow.uses ++ externalUses)
    externalYields alpha z arithClaim
    hcanonical huses hyields halpha hz
    harith0 harith1 harithYield harithPair harithLast
  rw [productionReciprocalSum_append, ← heqSum]
  simpa only [add_assoc] using hclosed

/-- An equality row has no local arithmetic residual. Under the shared Gate
balance, both of its reads must equal their unique produced values. -/
theorem eq_row_sound_of_shared_gate
    (arithRows : List GateLookup.Row) (eqRows : List EqRow)
    (externalUses externalYields : List GateLookup.Event)
    (r : EqRow) (hr : r ∈ eqRows)
    (hbalance : GateLookup.balanced arithRows
      (eqRows.flatMap EqRow.uses ++ externalUses) externalYields)
    (hunique : GateLookup.uniqueProduced
      (GateLookup.allYields arithRows externalYields))
    (left right : S31.Gadgets.Packed.Quad)
    (hleft : (r.leftAddress, left) ∈
      GateLookup.allYields arithRows externalYields)
    (hright : (r.rightAddress, right) ∈
      GateLookup.allYields arithRows externalYields) :
    left = right := by
  have hreadLeft : (r.leftAddress, r.value) ∈
      GateLookup.allUses arithRows
        (eqRows.flatMap EqRow.uses ++ externalUses) := by
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨r, hr, by simp [EqRow.uses]⟩
  have hreadRight : (r.rightAddress, r.value) ∈
      GateLookup.allUses arithRows
        (eqRows.flatMap EqRow.uses ++ externalUses) := by
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨r, hr, by simp [EqRow.uses]⟩
  have hl := GateLookup.balanced_read_matches _ _ hbalance hunique
    r.leftAddress r.value left hreadLeft hleft
  have hr' := GateLookup.balanced_read_matches _ _ hbalance hunique
    r.rightAddress r.value right hreadRight hright
  exact hl.symm.trans hr'

end S31.Gadgets.Air.EqGateInteraction
