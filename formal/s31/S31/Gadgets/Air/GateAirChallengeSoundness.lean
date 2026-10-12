import S31.Gadgets.Air.GateChallengeClosure
import S31.Gadgets.Air.Qm31GateInteraction

namespace S31.Gadgets.Air.GateAirChallengeSoundness
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateChallengePairs
open S31.Gadgets.Air.GateChallengeClosure
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.Qm31GateInteraction
open S31.Gadgets.Air.LogUpInteraction

abbrev Event := S31.Gadgets.Air.GateLookup.Event

/-- Acceptance by the modeled `qm31_ops` two-column interaction AIR with
explicit nonzero-denominator premises and a closed external Gate claim.
The raw AIR does not itself enforce those premises; see `GateAirRawSoundness`
for the bound that includes zero-denominator exceptions. -/
def interactionAccepts (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure) : Prop :=
  ∃ firstColumn lastColumn : Fin (2 ^ logSize) → GateSecure,
  ∃ claimed : GateSecure,
    (∀ i, (useTerm ((rows i).in0Address, (rows i).in0)
      alpha z).denominator ≠ 0) ∧
    (∀ i, (useTerm ((rows i).in1Address, (rows i).in1)
      alpha z).denominator ≠ 0) ∧
    (∀ i, (yieldTerm (rows i) alpha z).denominator ≠ 0) ∧
    (∀ i, pairResidual (rowPair (rows i) alpha z).1
      (rowPair (rows i) alpha z).2 (firstColumn i) = 0) ∧
    (∀ i, singleResidual (yieldTerm (rows i) alpha z)
      (lastColumn i - lastColumn (prev i) - firstColumn i +
        claimed / ((2 ^ logSize : Nat) : GateSecure)) = 0) ∧
    claimed + productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0

noncomputable def acceptingPairs (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List Event) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact Finset.univ.filter fun pair =>
    interactionAccepts logSize prev rows externalUses externalYields
      pair.1 pair.2

/-- Interaction AIR acceptance forces the exact modeled row equation to
close, including when the interaction columns are challenge-dependent. -/
theorem accepting_pairs_subset_closing_pairs (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List Event) :
    acceptingPairs logSize prev rows externalUses externalYields ⊆
      closingPairs (List.ofFn rows) externalUses externalYields := by
  classical
  intro pair hpair
  obtain ⟨firstColumn, lastColumn, claimed,
    huse0, huse1, hyield, hpairair, hlastair, hclosed⟩ :=
      (Finset.mem_filter.mp hpair).2
  have hclaim := qm31_ops_claimed_sum logSize prev rows
    firstColumn lastColumn pair.1 pair.2 claimed
    huse0 huse1 hyield hpairair hlastair
  have hrows : ((List.ofFn rows).map fun row =>
      rowContribution row pair.1 pair.2).sum =
      ∑ i : Fin (2 ^ logSize), rowContribution (rows i) pair.1 pair.2 := by
    simp [List.map_ofFn, List.sum_ofFn]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [hrows, ← hclaim]
  exact hclosed

theorem accepting_pairs_subset_bad_pairs (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List Event) :
    acceptingPairs logSize prev rows externalUses externalYields ⊆
      badPairs (allUses (List.ofFn rows) externalUses)
        (allYields (List.ofFn rows) externalYields) := by
  exact (accepting_pairs_subset_closing_pairs logSize prev rows
    externalUses externalYields).trans
    (closing_pairs_subset_bad_pairs (List.ofFn rows)
      externalUses externalYields)

/-- A fixed invalid Gate witness with nonzero denominators cannot satisfy
the modeled interaction AIR
and external closure on more than `(5s²+2s)·p⁴` of the `p⁸` ideal QM31
challenge pairs. This does not assert Fiat–Shamir or PCS soundness. -/
theorem invalid_witness_accepting_pairs_card_le (logSize : Nat)
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
    (acceptingPairs logSize prev rows externalUses externalYields).card ≤
      (5 * (allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn rows) externalUses ++
          allYields (List.ofFn rows) externalYields).toFinset.card) *
        Fintype.card GateSecure := by
  exact (Finset.card_le_card
    (accepting_pairs_subset_closing_pairs logSize prev rows
      externalUses externalYields)).trans
    (false_closing_pairs_card_le (List.ofFn rows)
      externalUses externalYields hcanonical huses hyields hwrong)

theorem invalid_witness_uniform_pair_rate_le (logSize : Nat)
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
    ((acceptingPairs logSize prev rows externalUses
      externalYields).card : ℚ) /
      (Fintype.card GateSecure : ℚ) ^ 2 ≤
      (((5 * (allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn rows) externalUses ++
          allYields (List.ofFn rows) externalYields).toFinset.card : Nat) : ℚ) /
        (Fintype.card GateSecure : ℚ)) := by
  have hcard := Finset.card_le_card
    (accepting_pairs_subset_closing_pairs logSize prev rows
      externalUses externalYields)
  have hcast : ((acceptingPairs logSize prev rows externalUses
      externalYields).card : ℚ) ≤
      ((closingPairs (List.ofFn rows) externalUses
        externalYields).card : ℚ) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hcast (sq_nonneg _)).trans
    (false_closing_pair_rate_le (List.ofFn rows)
      externalUses externalYields hcanonical huses hyields hwrong)

/-- Concrete wrong-wire corollary: a locally valid row that reads a value
different from its unique producer is covered by the same AIR acceptance
bound. The arithmetic constraints alone cannot detect this forgery. -/
theorem forged_input_accepting_pairs_card_le (logSize : Nat)
    (prev : Equiv.Perm (Fin (2 ^ logSize)))
    (rows : Fin (2 ^ logSize) → Row)
    (externalUses externalYields : List Event)
    (r : Row) (hr : r ∈ List.ofFn rows)
    (expected : S31.Gadgets.Packed.Quad)
    (hunique : uniqueProduced
      (allYields (List.ofFn rows) externalYields))
    (hexpected : (r.in0Address, expected) ∈
      allYields (List.ofFn rows) externalYields)
    (hforged : r.in0 ≠ expected)
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
      (allYields (List.ofFn rows) externalYields).count event < 2147483647) :
    (acceptingPairs logSize prev rows externalUses externalYields).card ≤
      (5 * (allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn rows) externalUses ++
          allYields (List.ofFn rows) externalYields).toFinset.card) *
        Fintype.card GateSecure := by
  exact invalid_witness_accepting_pairs_card_le logSize prev rows
    externalUses externalYields hcanonical huses hyields
    (forged_input_rejected (List.ofFn rows) externalUses externalYields
      r hr hunique expected hexpected hforged)

end S31.Gadgets.Air.GateAirChallengeSoundness
