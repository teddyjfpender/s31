import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Lemmas

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
theorem ideal_all_good_fraction [Fintype D]
    (s : Nat) (good : Finset D) :
    ((goodSequences s good).card : ℚ) /
        (Fintype.card (Fin s → D) : ℚ) =
      ((good.card : ℚ) / (Fintype.card D : ℚ)) ^ s := by
  rw [good_sequences_card, Fintype.card_pi_const]
  simpa only [Nat.cast_pow] using
    (div_pow (good.card : ℚ) (Fintype.card D : ℚ) s).symm

end S31.Gadgets.PcsFri.QuerySampling
