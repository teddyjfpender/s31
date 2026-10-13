import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-!
Exact finite counting for ideal independent uniform FRI queries *with
replacement*. `Fin s → D` is the raw transcript-query vector. A fixed
consistency set `good` is passed by every query precisely when every raw
coordinate lies in it. The fraction of such vectors is the density of
`good` raised to `s`, including when raw positions repeat.

This is the query-phase combinatoric used by a Circle FRI soundness argument.
It does not prove that the native hash channel is a random oracle, that its
queries are independent, or that accepted openings define a fixed `good` set.
-/

namespace S31.Gadgets.PcsFri.QuerySampling

variable {D : Type*}

/-- Every raw draw lies in the same fixed consistency set. -/
def goodSequences (s : Nat) (good : Finset D) : Finset (Fin s → D) :=
  Fintype.piFinset (fun _ : Fin s => good)

theorem good_sequences_member (s : Nat) (good : Finset D) (draws : Fin s → D) :
    draws ∈ goodSequences s good ↔ ∀ i, draws i ∈ good := by
  simp [goodSequences]

/-- Deduplicating the raw query vector changes no all-query predicate. -/
theorem good_sequences_member_normalized [DecidableEq D]
    (s : Nat) (good : Finset D) (draws : Fin s → D) :
    draws ∈ goodSequences s good ↔
      ∀ q ∈ (List.ofFn draws).toFinset, q ∈ good := by
  simp [goodSequences]

theorem good_sequences_card (s : Nat) (good : Finset D) :
    (goodSequences s good).card = good.card ^ s := by
  simp [goodSequences]

/-- In the uniform product sample space, the exact probability of all
queries missing an inconsistency is `(good-density)^s`. A real FRI proof
still needs a theorem bounding this density from the committed oracle. -/
theorem ideal_all_good_fraction [Fintype D] [Nonempty D]
    (s : Nat) (good : Finset D) :
    ((goodSequences s good).card : ℚ) /
        (Fintype.card (Fin s → D) : ℚ) =
      ((good.card : ℚ) / (Fintype.card D : ℚ)) ^ s := by
  rw [good_sequences_card, Fintype.card_pi_const]
  simpa only [Nat.cast_pow] using
    (div_pow (good.card : ℚ) (Fintype.card D : ℚ) s).symm

/-- A finite-model union bound with all security assumptions exposed. `badAccept`
is the set of ideal raw-query vectors that make a false statement pass a native
verifier. The first premise is the **unproved native-to-IOP refinement**: every
such acceptance must arise from failed commitment binding, failed Fiat--Shamir
sampling, or an IOP query failure. The second premise is the **unproved IOP
consistency claim**: its failure event lies inside the all-good query set.
The remaining two bounds are also premises, not properties of BLAKE2s or the
actual Merkle scheme. Thus this theorem does not instantiate native security.
-/
theorem conditional_native_bad_accept_bound [Fintype D] [Nonempty D]
    [DecidableEq D] (s : Nat) (good : Finset D)
    (badAccept merkleFailure fiatShamirFailure iopFailure : Finset (Fin s → D))
    (merkleBudget fiatShamirBudget : ℚ)
    (h_refines : badAccept ⊆ merkleFailure ∪ fiatShamirFailure ∪ iopFailure)
    (h_iop : iopFailure ⊆ goodSequences s good)
    (h_merkle : (merkleFailure.card : ℚ) /
        (Fintype.card (Fin s → D) : ℚ) ≤ merkleBudget)
    (h_fiatShamir : (fiatShamirFailure.card : ℚ) /
        (Fintype.card (Fin s → D) : ℚ) ≤ fiatShamirBudget) :
    (badAccept.card : ℚ) / (Fintype.card (Fin s → D) : ℚ) ≤
      merkleBudget + fiatShamirBudget +
        ((good.card : ℚ) / (Fintype.card D : ℚ)) ^ s := by
  have hcard : badAccept.card ≤ merkleFailure.card +
      fiatShamirFailure.card + (goodSequences s good).card := by
    have h0 := Finset.card_le_card h_refines
    have h1 := Finset.card_union_le merkleFailure fiatShamirFailure
    have h2 := Finset.card_union_le (merkleFailure ∪ fiatShamirFailure) iopFailure
    have h3 := Finset.card_le_card h_iop
    omega
  have hden : (0 : ℚ) ≤ (Fintype.card (Fin s → D) : ℚ) := by positivity
  have hcast : (badAccept.card : ℚ) ≤
      (merkleFailure.card : ℚ) + (fiatShamirFailure.card : ℚ) +
        ((goodSequences s good).card : ℚ) := by exact_mod_cast hcard
  have hquot := div_le_div_of_nonneg_right hcast hden
  rw [add_div, add_div, ideal_all_good_fraction] at hquot
  linarith

end S31.Gadgets.PcsFri.QuerySampling
