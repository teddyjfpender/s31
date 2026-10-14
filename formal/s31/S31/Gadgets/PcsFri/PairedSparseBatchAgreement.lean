import S31.Gadgets.PcsFri.PairedBatchSourceBinding
import S31.Gadgets.PcsFri.PairedBatchNativeRefinement
import S31.Gadgets.PcsFri.SparseCascadeQueries
import S31.Gadgets.PcsFri.SparseMultiHeightAgreement
import Mathlib.Tactic

/-!
Fixed-oracle sparse CAS05 batch-correlation lemma. The source and candidate
rows, per-row own-quotient recipes, and challenge set are fixed *before* the
single batch challenge is drawn. Each distinct original-source row supplies
a nonzero `f, own-quotient` row polynomial. Union bounding its roots over all
different rows gives an explicit exceptional challenge set. Outside it, a
batched row differs exactly when the original row differs. The sparse query
bound then samples adjacent pairs from this fixed bad-row set, counting raw
draws with replacement.

This does not prove that a false CAS05 statement gives a candidate low-degree
oracle far from the authenticated source, that the source opening is bound to
a whole committed oracle, or that Blake2s produces independent challenges.
-/

namespace S31.Gadgets.PcsFri.PairedSparseBatchAgreement

open S31.Gadgets.PcsFri.PairedBatchSourceBinding
open S31.Gadgets.PcsFri.PairedProtocolRecurrence
open S31.Gadgets.PcsFri.SparseCascadeQueries
open S31.Gadgets.PcsFri.QuerySampling

variable {F : Type*} [Field F] [DecidableEq F]

/-- The field values batched at one authenticated source row. `recipes` is
fixed by ordered OOD claims and row geometry before `λ`; each quotient is
derived from the adjacent original word by the same recipe. -/
noncomputable def pairedRow {n : Nat} (challenge : F)
    (recipes : Fin n → Recipe F) (source : Fin n → F) : F :=
  batchLoop challenge 1 (sourcePairs recipes source)

/-- Specialize the fixed-row collision bound to the native-shaped CAS05
`QM31.fromBase(original)`/`nativeOwnQuotient` arithmetic already refined in
`PairedBatchNativeRefinement`. This still models field operations rather than
executing Zig or authenticating the entire source oracle. -/
theorem native_row_collision_card {n : Nat}
    (rowY : PairedBatchNativeRefinement.M31)
    (denominator : PairedBatchNativeRefinement.CM31)
    (coefficients : Fin n →
      S31.Gadgets.PcsFri.DeepQuotientAlgebra.LineCoeffs
        PairedBatchNativeRefinement.QM31)
    (source candidate : Fin n → PairedBatchNativeRefinement.M31)
    (hsource : source ≠ candidate)
    (challenges : Finset PairedBatchNativeRefinement.QM31) :
    (challenges.filter fun challenge =>
      PairedBatchNativeRefinement.nativeBatch challenge 1 rowY denominator
        (List.ofFn fun j => (source j, coefficients j)) =
      PairedBatchNativeRefinement.nativeBatch challenge 1 rowY denominator
        (List.ofFn fun j => (candidate j, coefficients j))).card ≤ 2 * n := by
  classical
  let recipes := fun j : Fin n =>
    PairedBatchNativeRefinement.recipe (coefficients j) rowY denominator
  let source' := fun j : Fin n => PairedBatchNativeRefinement.fromBase (source j)
  let candidate' := fun j : Fin n => PairedBatchNativeRefinement.fromBase (candidate j)
  have hbase (x y : PairedBatchNativeRefinement.M31)
      (h : PairedBatchNativeRefinement.fromBase x =
        PairedBatchNativeRefinement.fromBase y) : x = y := by
    have h0 := congrArg (fun z : PairedBatchNativeRefinement.QM31 => z.c0.a) h
    simpa [PairedBatchNativeRefinement.fromBase,
      PairedBatchNativeRefinement.fromCM,
      ConcreteCircleCount.embedCM] using h0
  have hsource' : source' ≠ candidate' := by
    intro h
    apply hsource
    funext j
    exact hbase (source j) (candidate j) (congrFun h j)
  have hnative (challenge : PairedBatchNativeRefinement.QM31)
      (rows : Fin n → PairedBatchNativeRefinement.M31) :
      PairedBatchNativeRefinement.nativeBatch challenge 1 rowY denominator
          (List.ofFn fun j => (rows j, coefficients j)) =
        batchLoop challenge 1 (sourcePairs recipes
          (fun j => PairedBatchNativeRefinement.fromBase (rows j))) := by
    rw [PairedBatchNativeRefinement.nativeBatch_eq_source_poly, rowPoly_eval]
  have hbound := source_batch_collision_card recipes source' candidate'
    hsource' challenges
  calc
    (challenges.filter fun challenge =>
      PairedBatchNativeRefinement.nativeBatch challenge 1 rowY denominator
        (List.ofFn fun j => (source j, coefficients j)) =
      PairedBatchNativeRefinement.nativeBatch challenge 1 rowY denominator
        (List.ofFn fun j => (candidate j, coefficients j))).card =
      (challenges.filter fun challenge =>
        batchLoop challenge 1 (sourcePairs recipes source') =
        batchLoop challenge 1 (sourcePairs recipes candidate')).card := by
          congr 1
          ext challenge
          simp only [Finset.mem_filter]
          rw [hnative challenge source, hnative challenge candidate]
    _ ≤ 2 * n := hbound

variable (k i n : Nat)

/-- All source rows on which the fixed authenticated source and a fixed
candidate original oracle differ at this height. -/
noncomputable def mismatchedRows
    (source candidate : Fin (2 ^ (k - i)) → Fin n → F) :
    Finset (Fin (2 ^ (k - i))) := by
  classical
  exact Finset.univ.filter fun row => source row ≠ candidate row

/-- A row where a challenge hides one *original* mismatch in the paired
original/own-quotient batch. -/
noncomputable def collisionAt
    (challenges : Finset F)
    (recipes : Fin (2 ^ (k - i)) → Fin n → Recipe F)
    (source candidate : Fin (2 ^ (k - i)) → Fin n → F)
    (row : Fin (2 ^ (k - i))) : Finset F := by
  classical
  exact challenges.filter fun challenge =>
    pairedRow challenge (recipes row) (source row) =
      pairedRow challenge (recipes row) (candidate row)

/-- One exceptional set for all mismatching source rows. Repeated raw
queries do not enlarge this set; the single `λ` is shared by all heights. -/
noncomputable def exceptionalChallenges
    (challenges : Finset F)
    (recipes : Fin (2 ^ (k - i)) → Fin n → Recipe F)
    (source candidate : Fin (2 ^ (k - i)) → Fin n → F) : Finset F :=
  (mismatchedRows k i n source candidate).biUnion
    (collisionAt k i n challenges recipes source candidate)

theorem exceptional_challenges_card_le
    (challenges : Finset F)
    (recipes : Fin (2 ^ (k - i)) → Fin n → Recipe F)
    (source candidate : Fin (2 ^ (k - i)) → Fin n → F) :
    (exceptionalChallenges k i n challenges recipes source candidate).card ≤
      (mismatchedRows k i n source candidate).card * (2 * n) := by
  classical
  unfold exceptionalChallenges
  calc
    ((mismatchedRows k i n source candidate).biUnion
      (collisionAt k i n challenges recipes source candidate)).card ≤
        ∑ row ∈ mismatchedRows k i n source candidate,
          (collisionAt k i n challenges recipes source candidate row).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _row ∈ mismatchedRows k i n source candidate, 2 * n := by
      apply Finset.sum_le_sum
      intro row hrow
      have hneq : source row ≠ candidate row :=
        (Finset.mem_filter.mp hrow).2
      exact source_batch_collision_card (recipes row) (source row)
        (candidate row) hneq challenges
    _ = (mismatchedRows k i n source candidate).card * (2 * n) := by simp

/-- The row-disagreement set after CAS05's shared-challenge batch. -/
noncomputable def batchedBadRows
    (challenge : F)
    (recipes : Fin (2 ^ (k - i)) → Fin n → Recipe F)
    (source candidate : Fin (2 ^ (k - i)) → Fin n → F) :
    Finset (Fin (2 ^ (k - i))) := by
  classical
  exact Finset.univ.filter fun row =>
    pairedRow challenge (recipes row) (source row) ≠
      pairedRow challenge (recipes row) (candidate row)

/-- Outside the explicit exceptional challenge set, batching neither
creates nor hides a row disagreement. The converse does not need a random
challenge: identical originals have identical derived quotients. -/
theorem batched_bad_rows_eq_mismatched
    (challenges : Finset F) (challenge : F)
    (recipes : Fin (2 ^ (k - i)) → Fin n → Recipe F)
    (source candidate : Fin (2 ^ (k - i)) → Fin n → F)
    (hmem : challenge ∈ challenges)
    (hnot : challenge ∉
      exceptionalChallenges k i n challenges recipes source candidate) :
    batchedBadRows k i n challenge recipes source candidate =
      mismatchedRows k i n source candidate := by
  classical
  ext row
  simp only [batchedBadRows, mismatchedRows, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hbatch hsame
    exact hbatch (congrArg (pairedRow challenge (recipes row)) hsame)
  · intro hsource heq
    apply hnot
    unfold exceptionalChallenges
    apply Finset.mem_biUnion.mpr
    refine ⟨row, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsource⟩
    · exact Finset.mem_filter.mpr ⟨hmem, heq⟩

/-- Conditional on a challenge outside the finite collision set, the
native adjacent-pair schedule detects the same fixed source mismatches. Raw
queries are independent uniform elements of `Fin (2^k)` with replacement;
the `draws` exponent does not multiply over heights. -/
theorem sparse_miss_le_after_good_challenge
    (hi : i < k) (draws : Nat)
    (challenges : Finset F) (challenge : F)
    (recipes : Fin (2 ^ (k - i)) → Fin n → Recipe F)
    (source candidate : Fin (2 ^ (k - i)) → Fin n → F)
    (hmem : challenge ∈ challenges)
    (hnot : challenge ∉
      exceptionalChallenges k i n challenges recipes source candidate) :
    (goodSequences draws
      (goodSparsePair k i
        (batchedBadRows k i n challenge recipes source candidate))).card ≤
      ((2 ^ (k - i) - (mismatchedRows k i n source candidate).card) *
        2 ^ i) ^ draws := by
  rw [batched_bad_rows_eq_mismatched k i n challenges challenge recipes
    source candidate hmem hnot]
  exact good_sparse_sequences_card_le k i draws hi
    (mismatchedRows k i n source candidate)

/-- A fixed CAS05 multi-height roster. All original source words, the
candidate words, and per-row quotient recipes are chosen before the shared
batch challenge. This structure is mathematical data, not a native
commitment-opening certificate. -/
structure FixedPairedRoster (F : Type*) [Field F] (k H : Nat) where
  columns : Fin H → Nat
  recipes : (height : Fin H) →
    Fin (2 ^ (k - height.val)) → Fin (columns height) → Recipe F
  source : (height : Fin H) →
    Fin (2 ^ (k - height.val)) → Fin (columns height) → F
  candidate : (height : Fin H) →
    Fin (2 ^ (k - height.val)) → Fin (columns height) → F

variable {k H : Nat} (roster : FixedPairedRoster F k H)

noncomputable def rosterMismatch (height : Fin H) :
    Finset (Fin (2 ^ (k - height.val))) :=
  mismatchedRows k height.val (roster.columns height)
    (roster.source height) (roster.candidate height)

/-- A single exceptional challenge set for every source height, retaining
the same challenge used by all height batches. -/
noncomputable def rosterExceptional (challenges : Finset F) : Finset F :=
  Finset.univ.biUnion fun height : Fin H =>
    exceptionalChallenges k height.val (roster.columns height)
      challenges (roster.recipes height)
      (roster.source height) (roster.candidate height)

theorem roster_exceptional_card_le (challenges : Finset F) :
    (rosterExceptional roster challenges).card ≤
      ∑ height : Fin H,
        (rosterMismatch roster height).card * (2 * roster.columns height) := by
  classical
  unfold rosterExceptional
  calc
    (Finset.univ.biUnion fun height : Fin H =>
      exceptionalChallenges k height.val (roster.columns height)
        challenges (roster.recipes height)
        (roster.source height) (roster.candidate height)).card ≤
        ∑ height : Fin H,
          (exceptionalChallenges k height.val (roster.columns height)
            challenges (roster.recipes height)
            (roster.source height) (roster.candidate height)).card := by
      simpa using Finset.card_biUnion_le
    _ ≤ ∑ height : Fin H,
        (rosterMismatch roster height).card * (2 * roster.columns height) := by
      apply Finset.sum_le_sum
      intro height _
      exact exceptional_challenges_card_le k height.val
        (roster.columns height) challenges (roster.recipes height)
        (roster.source height) (roster.candidate height)

/-- Batched mismatch rows at every height for one shared challenge. -/
noncomputable def rosterBatchedBad (challenge : F) :
    SparseMultiHeightAgreement.BadRows k H :=
  fun height => batchedBadRows k height.val (roster.columns height)
    challenge (roster.recipes height)
    (roster.source height) (roster.candidate height)

noncomputable def rosterBad : SparseMultiHeightAgreement.BadRows k H :=
  rosterMismatch roster

theorem roster_batched_bad_eq_fixed (challenges : Finset F) (challenge : F)
    (hmem : challenge ∈ challenges)
    (hnot : challenge ∉ rosterExceptional roster challenges) :
    rosterBatchedBad roster challenge = rosterBad roster := by
  funext height
  apply batched_bad_rows_eq_mismatched k height.val
    (roster.columns height) challenges challenge (roster.recipes height)
    (roster.source height) (roster.candidate height) hmem
  intro hcollision
  apply hnot
  exact Finset.mem_biUnion.mpr
    ⟨height, Finset.mem_univ height, hcollision⟩

/-- Outside the finite batch-collision set, ideal independent raw queries
miss all mismatched source pairs no more often than they miss the fixed
mismatches at any chosen height. A raw query opens both adjacent source rows
at every height; repeated raw positions remain separate draws. -/
theorem roster_sparse_miss_le (draws : Nat) (challenges : Finset F)
    (challenge : F) (hmem : challenge ∈ challenges)
    (hnot : challenge ∉ rosterExceptional roster challenges)
    (height : Fin H) (hi : height.val < k) :
    (goodSequences draws
      (SparseMultiHeightAgreement.jointGood k H
        (rosterBatchedBad roster challenge))).card ≤
      ((2 ^ (k - height.val) - (rosterMismatch roster height).card) *
        2 ^ height.val) ^ draws := by
  rw [roster_batched_bad_eq_fixed roster challenges challenge hmem hnot]
  apply SparseMultiHeightAgreement.joint_miss_le_one_height
    k H draws
    ((2 ^ (k - height.val) - (rosterMismatch roster height).card) *
      2 ^ height.val)
    (rosterBad roster) height
  have hsingle := good_sparse_sequences_card_le k height.val 1 hi
    (rosterMismatch roster height)
  simpa [good_sequences_card, rosterBad] using hsingle

/-- Every exceptional challenge comes from one of the fixed pre-challenge
row-polynomial collisions, so it lies in the announced challenge set. -/
theorem roster_exceptional_subset (challenges : Finset F) :
    rosterExceptional roster challenges ⊆ challenges := by
  intro challenge hchallenge
  obtain ⟨height, _, hheight⟩ :=
    Finset.mem_biUnion.mp hchallenge
  obtain ⟨row, _, hrow⟩ := Finset.mem_biUnion.mp hheight
  exact (Finset.mem_filter.mp hrow).1

/-- Count challenge/raw-query pairs, with one uniform challenge drawn after
the fixed source and candidate rosters and `draws` independent uniform raw
positions drawn afterward. The first term pays for all challenge collisions;
the second uses one selected source height's exact adjacent-pair miss bound.
This is a finite ideal experiment, not a BCS/ROM or native accept bound. -/
theorem joint_challenge_query_miss_count (draws : Nat)
    (challenges : Finset F) (height : Fin H) (hi : height.val < k) :
    (∑ challenge ∈ challenges,
      (goodSequences draws
        (SparseMultiHeightAgreement.jointGood k H
          (rosterBatchedBad roster challenge))).card) ≤
      (rosterExceptional roster challenges).card * (2 ^ k) ^ draws +
      (challenges.card - (rosterExceptional roster challenges).card) *
        ((2 ^ (k - height.val) - (rosterMismatch roster height).card) *
          2 ^ height.val) ^ draws := by
  classical
  let bad := rosterExceptional roster challenges
  let count (challenge : F) :=
    (goodSequences draws
      (SparseMultiHeightAgreement.jointGood k H
        (rosterBatchedBad roster challenge))).card
  let budget :=
    ((2 ^ (k - height.val) - (rosterMismatch roster height).card) *
      2 ^ height.val) ^ draws
  have hsubset : bad ⊆ challenges := roster_exceptional_subset roster challenges
  have hbad : ∑ challenge ∈ bad, count challenge ≤ bad.card * (2 ^ k) ^ draws := by
    calc
      _ ≤ ∑ _challenge ∈ bad, (2 ^ k) ^ draws := by
        apply Finset.sum_le_sum
        intro challenge _
        dsimp [count]
        rw [good_sequences_card]
        have hcard :
            (SparseMultiHeightAgreement.jointGood k H
              (rosterBatchedBad roster challenge)).card ≤ 2 ^ k := by
          simpa using Finset.card_le_card
            (Finset.subset_univ
              (SparseMultiHeightAgreement.jointGood k H
                (rosterBatchedBad roster challenge)))
        exact Nat.pow_le_pow_left hcard draws
      _ = bad.card * (2 ^ k) ^ draws := by simp
  have hgood : ∑ challenge ∈ challenges \ bad, count challenge ≤
      (challenges \ bad).card * budget := by
    calc
      _ ≤ ∑ _challenge ∈ challenges \ bad, budget := by
        apply Finset.sum_le_sum
        intro challenge hchallenge
        obtain ⟨hmem, hnot⟩ := Finset.mem_sdiff.mp hchallenge
        exact roster_sparse_miss_le roster draws challenges challenge
          hmem hnot height hi
      _ = (challenges \ bad).card * budget := by simp
  have hpartition :
      (∑ challenge ∈ challenges \ bad, count challenge) +
        (∑ challenge ∈ bad, count challenge) =
      ∑ challenge ∈ challenges, count challenge :=
    Finset.sum_sdiff hsubset
  have hcard : (challenges \ bad).card = challenges.card - bad.card := by
    simp [Finset.card_sdiff, Finset.inter_eq_left.mpr hsubset]
  change (∑ challenge ∈ challenges, count challenge) ≤
    bad.card * (2 ^ k) ^ draws + (challenges.card - bad.card) * budget
  calc
    (∑ challenge ∈ challenges, count challenge) =
        (∑ challenge ∈ challenges \ bad, count challenge) +
          (∑ challenge ∈ bad, count challenge) := hpartition.symm
    _ ≤ (challenges \ bad).card * budget + bad.card * (2 ^ k) ^ draws :=
      Nat.add_le_add hgood hbad
    _ = bad.card * (2 ^ k) ^ draws +
          (challenges.card - bad.card) * budget := by rw [hcard]; omega

end S31.Gadgets.PcsFri.PairedSparseBatchAgreement
