import S31.Gadgets.Air.GateContributions
import S31.Gadgets.Air.LogUpInteraction

namespace S31.Gadgets.Air.Qm31GateInteraction
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.LogUpInteraction

abbrev Event := GateLookup.Event

def useTerm (event : Event) (alpha z : GateSecure) : Term GateSecure :=
  { numerator := 1,
    denominator := combineTerm (eventTuple event) alpha z }

def yieldTerm (row : Row) (alpha z : GateSecure) : Term GateSecure :=
  { numerator := -(row.multiplicity : GateSecure),
    denominator := combineTerm
      (eventTuple (row.outAddress, row.output)) alpha z }

def rowPair (row : Row) (alpha z : GateSecure) :
    Term GateSecure × Term GateSecure :=
  (useTerm (row.in0Address, row.in0) alpha z,
    useTerm (row.in1Address, row.in1) alpha z)

theorem row_terms_eq_contribution (row : Row) (alpha z : GateSecure) :
    pairValue (rowPair row alpha z) +
      finalValue (.inl (yieldTerm row alpha z)) =
      rowContribution row alpha z := by
  simp [rowPair, useTerm, yieldTerm, pairValue, finalValue,
    rowContribution, div_eq_mul_inv]
  ring

/-- The exact three-lookup `qm31_ops` schedule: the two Gate uses form the
first pair, and the multiplicity-weighted Gate yield is the final singleton.
The AIR residuals then force this component's claimed sum to equal the sum
of its row contributions. -/
theorem qm31_ops_claimed_sum
    (logSize : Nat) (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (firstColumn lastColumn : Fin (2 ^ logSize) → GateSecure)
    (alpha z claimed : GateSecure)
    (huse0 : ∀ i,
      (useTerm ((rows i).in0Address, (rows i).in0) alpha z).denominator ≠ 0)
    (huse1 : ∀ i,
      (useTerm ((rows i).in1Address, (rows i).in1) alpha z).denominator ≠ 0)
    (hyield : ∀ i, (yieldTerm (rows i) alpha z).denominator ≠ 0)
    (hpairair : ∀ i,
      pairResidual (rowPair (rows i) alpha z).1
        (rowPair (rows i) alpha z).2 (firstColumn i) = 0)
    (hlastair : ∀ i,
      singleResidual (yieldTerm (rows i) alpha z)
        (lastColumn i - lastColumn (prev i) - firstColumn i +
          claimed / ((2 ^ logSize : Nat) : GateSecure)) = 0) :
    claimed = ∑ i : Fin (2 ^ logSize),
      rowContribution (rows i) alpha z := by
  apply claimed_sum_of_cyclic_recurrence
    (2 ^ logSize) prev lastColumn
    (fun i => rowContribution (rows i) alpha z)
    (claimed / ((2 ^ logSize : Nat) : GateSecure)) claimed
  · exact mul_div_cancel₀ claimed (gateSecure_pow_two_nonzero logSize)
  · intro i
    have hden0 : (rowPair (rows i) alpha z).1.denominator ≠ 0 := by
      simpa [rowPair] using huse0 i
    have hden1 : (rowPair (rows i) alpha z).2.denominator ≠ 0 := by
      simpa [rowPair] using huse1 i
    have hp : firstColumn i = pairValue (rowPair (rows i) alpha z) :=
      (pairResidual_iff _ _ _ hden0 hden1).mp (hpairair i)
    have hy : lastColumn i - lastColumn (prev i) - firstColumn i +
        claimed / ((2 ^ logSize : Nat) : GateSecure) =
        finalValue (.inl (yieldTerm (rows i) alpha z)) :=
      (singleResidual_iff _ _ (hyield i)).mp (hlastair i)
    calc
      lastColumn i - lastColumn (prev i) =
          firstColumn i + finalValue (.inl (yieldTerm (rows i) alpha z)) -
            claimed / ((2 ^ logSize : Nat) : GateSecure) := by
        linear_combination hy
      _ = rowContribution (rows i) alpha z -
            claimed / ((2 ^ logSize : Nat) : GateSecure) := by
        rw [hp, row_terms_eq_contribution]

/-- Once the other Gate components and public terms provide their external
event sums, a closed verifier claim for this component yields exact Gate
balance under the bounded-challenge and address-count premises. -/
theorem qm31_ops_closed_gate_balanced
    (logSize : Nat) (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (firstColumn lastColumn : Fin (2 ^ logSize) → GateSecure)
    (externalUses externalYields : List GateLookup.Event)
    (alpha z claimed : GateSecure)
    (hcanonical : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields,
      event.1 < 2147483647)
    (huses : ∀ address,
      addressCount (allUses (List.ofFn rows) externalUses) address < 2147483647)
    (hyields : ∀ address,
      addressCount (allYields (List.ofFn rows) externalYields) address < 2147483647)
    (halpha : alpha ∉ badAlpha
      (allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields))
    (hz : z ∉ badZ
      (allUses (List.ofFn rows) externalUses)
      (allYields (List.ofFn rows) externalYields) alpha)
    (huse0 : ∀ i,
      (useTerm ((rows i).in0Address, (rows i).in0) alpha z).denominator ≠ 0)
    (huse1 : ∀ i,
      (useTerm ((rows i).in1Address, (rows i).in1) alpha z).denominator ≠ 0)
    (hyield : ∀ i, (yieldTerm (rows i) alpha z).denominator ≠ 0)
    (hpairair : ∀ i,
      pairResidual (rowPair (rows i) alpha z).1
        (rowPair (rows i) alpha z).2 (firstColumn i) = 0)
    (hlastair : ∀ i,
      singleResidual (yieldTerm (rows i) alpha z)
        (lastColumn i - lastColumn (prev i) - firstColumn i +
          claimed / ((2 ^ logSize : Nat) : GateSecure)) = 0)
    (hclosed : claimed + productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0) :
    balanced (List.ofFn rows) externalUses externalYields := by
  have hclaim := qm31_ops_claimed_sum logSize prev rows
    firstColumn lastColumn alpha z claimed
    huse0 huse1 hyield hpairair hlastair
  have hrows : ((List.ofFn rows).map fun row => rowContribution row alpha z).sum =
      ∑ i : Fin (2 ^ logSize), rowContribution (rows i) alpha z := by
    simp [List.map_ofFn, List.sum_ofFn]
  apply closed_gate_contribution_balanced_of_address_counts
    (List.ofFn rows) externalUses externalYields alpha z
    hcanonical huses hyields halpha hz
  rw [hrows]
  rw [← hclaim]
  exact hclosed

end S31.Gadgets.Air.Qm31GateInteraction
