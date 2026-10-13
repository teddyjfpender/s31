import S31.Gadgets.PcsFri.SparseCascadeQueries
import S31.Gadgets.PcsFri.QuerySampling

/-!
The same CAS05 raw query visits every source height. This module counts the
joint event that its authenticated adjacent pair avoids a fixed bad-row set
at *all* heights. The bad sets are quantified outside the raw query vector:
they must be chosen from fixed committed oracles before ideal independent
uniform raw queries are sampled. Merkle binding and the adaptive BCS/ROM
reduction are not proved by this finite counting model.

The valid bound is by one joint good set (or by any single height with a
certified bad-pair density). Multiplying per-height miss probabilities is
invalid: one raw query can make the height events perfectly correlated.
The explicit eight-row counterexample at the end uses the native `pairBase`
formula and proves this strict inequality.
-/

namespace S31.Gadgets.PcsFri.SparseMultiHeightAgreement

open S31.Gadgets.PcsFri.SparseCascadeQueries
open S31.Gadgets.PcsFri.QuerySampling

/-- A fixed bad source-row set for each of `H` CAS05 heights. The height-
`i` source domain has `2^(k-i)` rows. The native profile has `H ≤ k`;
that shape condition can be supplied when this model is instantiated. -/
abbrev BadRows (k H : Nat) :=
  (i : Fin H) → Finset (Fin (2 ^ (k - i.val)))

/-- One raw row passes all adjacent-pair checks against these fixed bad sets.
`goodSparsePair` tests *both* opened rows at each height, not only the
selected projected source row. -/
noncomputable def jointGood (k H : Nat) (bad : BadRows k H) :
    Finset (Fin (2 ^ k)) := by
  classical
  exact Finset.univ.filter fun raw =>
    ∀ i : Fin H, raw ∈ goodSparsePair k i.val (bad i)

theorem mem_jointGood (k H : Nat) (bad : BadRows k H)
    (raw : Fin (2 ^ k)) :
    raw ∈ jointGood k H bad ↔
      ∀ i : Fin H, raw ∈ goodSparsePair k i.val (bad i) := by
  classical
  simp [jointGood]

/-- The raw positions at which one height's opened pair meets its fixed bad
rows. -/
noncomputable def detectedAt (k H : Nat) (bad : BadRows k H)
    (i : Fin H) : Finset (Fin (2 ^ k)) := by
  classical
  exact Finset.univ \ goodSparsePair k i.val (bad i)

/-- Union, rather than product, is the correct way to combine the detectable
positions of heights reached by the same raw query. -/
noncomputable def detectedUnion (k H : Nat) (bad : BadRows k H) :
    Finset (Fin (2 ^ k)) := by
  classical
  exact Finset.univ.biUnion (detectedAt k H bad)

theorem jointGood_eq_complement_detectedUnion (k H : Nat)
    (bad : BadRows k H) :
    jointGood k H bad = Finset.univ \ detectedUnion k H bad := by
  classical
  ext raw
  simp [mem_jointGood, detectedUnion, detectedAt]

/-- Exact single-query count including every overlap among heights. -/
theorem jointGood_card_eq_union_complement (k H : Nat)
    (bad : BadRows k H) :
    (jointGood k H bad).card = 2 ^ k - (detectedUnion k H bad).card := by
  rw [jointGood_eq_complement_detectedUnion]
  simp [Finset.card_sdiff]

/-- All-height consistency implies consistency at any specified height.
This is the correct direction for a conservative sparse-query soundness
bound. -/
theorem jointGood_subset_height (k H : Nat) (bad : BadRows k H)
    (i : Fin H) :
    jointGood k H bad ⊆ goodSparsePair k i.val (bad i) := by
  intro raw hraw
  exact (mem_jointGood k H bad raw).mp hraw i

/-- Exact count for `draws` independent ideal raw queries *with replacement*.
The exponent is over queries, not heights. -/
theorem joint_good_sequences_card (k H draws : Nat) (bad : BadRows k H) :
    (goodSequences draws (jointGood k H bad)).card =
      (jointGood k H bad).card ^ draws :=
  good_sequences_card draws (jointGood k H bad)

theorem joint_good_sequences_card_from_union (k H draws : Nat)
    (bad : BadRows k H) :
    (goodSequences draws (jointGood k H bad)).card =
      (2 ^ k - (detectedUnion k H bad).card) ^ draws := by
  rw [joint_good_sequences_card, jointGood_card_eq_union_complement]

/-- If a future global correlated-agreement theorem supplies one height with
at most `budget` safe raw positions, then the fixed-oracle ideal query miss
count is at most `budget^draws`. This does not establish that such a height
exists for CAS05's actual committed multi-domain ensemble. -/
theorem joint_miss_le_one_height (k H draws budget : Nat)
    (bad : BadRows k H) (i : Fin H)
    (hbudget : (goodSparsePair k i.val (bad i)).card ≤ budget) :
    (goodSequences draws (jointGood k H bad)).card ≤ budget ^ draws := by
  rw [joint_good_sequences_card]
  exact Nat.pow_le_pow_left
    ((Finset.card_le_card (jointGood_subset_height k H bad i)).trans hbudget)
    draws

/-- A quantified agreement interface: for every fixed false oracle roster,
some height exposes enough bad adjacent pairs. `bad` and the height witness
are fixed before `draws`; this is the missing multi-domain theorem premise,
not an established property of the native PCS. -/
theorem conditional_correlated_agreement_bound
    (k H draws budget : Nat) (bad : BadRows k H)
    (hcorrelated : ∃ i : Fin H,
      (goodSparsePair k i.val (bad i)).card ≤ budget) :
    (goodSequences draws (jointGood k H bad)).card ≤ budget ^ draws := by
  obtain ⟨i, hi⟩ := hcorrelated
  exact joint_miss_le_one_height k H draws budget bad i hi

/-- Height zero marks rows 0 and 2 as bad. Since the verifier opens adjacent
pairs, raw rows 0–3 encounter one of them. -/
def toyGood0 : Finset (Fin 8) :=
  goodSparsePair 3 0 ({0, 2} : Finset (Fin 8))

/-- Height one marks row 0 as bad. Its opened pair is `(0,1)` for the same
raw rows 0–3, despite its source domain having only four rows. -/
def toyGood1 : Finset (Fin 8) :=
  goodSparsePair 3 1 ({0} : Finset (Fin 4))

theorem toy_good_events_identical : toyGood0 = toyGood1 := by decide

theorem toy_good_event_card : toyGood0.card = 4 := by decide

/-- The actual one-query joint miss probability is `4/8 = 1/2`, while
multiplying the two individual `4/8` miss probabilities would give `1/4`.
Cross multiplication avoids embedding a probability formalism in this
finite counterexample. -/
theorem naive_height_product_is_false :
    (toyGood0 ∩ toyGood1).card * 8 >
      toyGood0.card * toyGood1.card := by decide

theorem toy_joint_draws_card (draws : Nat) :
    (goodSequences draws (toyGood0 ∩ toyGood1)).card = 4 ^ draws := by
  rw [good_sequences_card, ← toy_good_events_identical]
  simp [toy_good_event_card]

end S31.Gadgets.PcsFri.SparseMultiHeightAgreement
