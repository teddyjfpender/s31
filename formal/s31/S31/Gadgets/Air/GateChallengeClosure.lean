import S31.Gadgets.Air.GateChallengePairs
import S31.Gadgets.Air.GateContributions

namespace S31.Gadgets.Air.GateChallengeClosure
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateChallengePairs
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateLookup

abbrev Event := S31.Gadgets.Air.GateLookup.Event

/-- Challenge pairs that close the actual row-plus-external Gate reciprocal
equation for one fixed collection of rows and external events. -/
noncomputable def closingPairs (rows : List Row)
    (externalUses externalYields : List Event) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact Finset.univ.filter fun pair =>
    (rows.map fun row => rowContribution row pair.1 pair.2).sum +
      productionReciprocalSum externalUses pair.1 pair.2 -
      productionReciprocalSum externalYields pair.1 pair.2 = 0

theorem closing_pairs_subset_bad_pairs (rows : List Row)
    (externalUses externalYields : List Event) :
    closingPairs rows externalUses externalYields ⊆
      badPairs (allUses rows externalUses)
        (allYields rows externalYields) := by
  intro pair hpair
  have hclosed := (Finset.mem_filter.mp hpair).2
  exact reciprocal_closure_implies_bad_pair
    (allUses rows externalUses) (allYields rows externalYields)
    pair.1 pair.2
    (closed_gate_contribution_equal_event_sums
      rows externalUses externalYields pair.1 pair.2 hclosed)

/-- If the fixed Gate event lists differ, at most `(5s² + 2s) * p⁴`
of the `p⁸` ideal challenge pairs can close the row equation. The per-event
count condition prevents multiplicity from disappearing modulo `p`. -/
theorem false_closing_pairs_card_le (rows : List Row)
    (externalUses externalYields : List Event)
    (hcanonical : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      (allUses rows externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      (allYields rows externalYields).count event < 2147483647)
    (hwrong : ¬ (allUses rows externalUses).Perm
      (allYields rows externalYields)) :
    (closingPairs rows externalUses externalYields).card ≤
      (5 * (allUses rows externalUses ++
        allYields rows externalYields).toFinset.card ^ 2 +
        2 * (allUses rows externalUses ++
          allYields rows externalYields).toFinset.card) *
        Fintype.card GateSecure := by
  exact (Finset.card_le_card
    (closing_pairs_subset_bad_pairs rows externalUses externalYields)).trans
    (bad_pairs_card_le _ _ hcanonical huses hyields hwrong)

theorem false_closing_pair_rate_le (rows : List Row)
    (externalUses externalYields : List Event)
    (hcanonical : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      (allUses rows externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      (allYields rows externalYields).count event < 2147483647)
    (hwrong : ¬ (allUses rows externalUses).Perm
      (allYields rows externalYields)) :
    ((closingPairs rows externalUses externalYields).card : ℚ) /
      (Fintype.card GateSecure : ℚ) ^ 2 ≤
      (((5 * (allUses rows externalUses ++
        allYields rows externalYields).toFinset.card ^ 2 +
        2 * (allUses rows externalUses ++
          allYields rows externalYields).toFinset.card : Nat) : ℚ) /
        (Fintype.card GateSecure : ℚ)) := by
  have hcard := Finset.card_le_card
    (closing_pairs_subset_bad_pairs rows externalUses externalYields)
  have hcast : ((closingPairs rows externalUses externalYields).card : ℚ) ≤
      ((badPairs (allUses rows externalUses)
        (allYields rows externalYields)).card : ℚ) := by
    exact_mod_cast hcard
  exact (div_le_div_of_nonneg_right hcast (sq_nonneg _)).trans
    (uniform_pair_failure_rate_le _ _ hcanonical huses hyields hwrong)

end S31.Gadgets.Air.GateChallengeClosure
