import S31.Gadgets.PcsFri.QuerySampling
import Mathlib.Data.Nat.Count
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic

/-!
Exact finite counting for the opt-in raw BLAKE2s Gate channel's FRI query
indices. The pinned native `drawQueries` masks each raw `u32` with
`2^k - 1`. For every `k ≤ 32`, each index has exactly `2^(32-k)` raw
preimages. Thus independent uniform raw words give independent uniform
queries, including duplicate positions.

The theorem does not establish that BLAKE2s is a random oracle, that an
adaptive adversary sees independent words, or that the native verifier
refines a sound IOP. It is one sampler-counting lemma for that reduction.
-/

namespace S31.Gadgets.PcsFri.RawMaskedQuery

def rawSize : Nat := 2 ^ 32
def domainSize (k : Nat) : Nat := 2 ^ k

def sampleIndex (k word : Nat) : Fin (domainSize k) :=
  ⟨word % domainSize k, Nat.mod_lt _ (by simp [domainSize])⟩

def preimages (k i : Nat) : Nat :=
  Nat.count (fun word => word % domainSize k = i) rawSize

private theorem raw_size_factor (k : Nat) (hk : k ≤ 32) :
    rawSize = domainSize k * 2 ^ (32 - k) := by
  unfold rawSize domainSize
  rw [← pow_add, Nat.add_sub_of_le hk]

/-- The pinned Zig `word & query_mask` operation is the arithmetic index
used below when the word is interpreted as an unsigned natural. -/
theorem native_mask_eq (k word : Nat) :
    word &&& (2 ^ k - 1) = (sampleIndex k word).val := by
  simpa only [sampleIndex, domainSize] using
    Nat.and_two_pow_sub_one_eq_mod word k

/-- Every native-masked index has the same raw-word fiber size. -/
theorem preimages_exact (k i : Nat) (hk : k ≤ 32) (hi : i < domainSize k) :
    preimages k i = 2 ^ (32 - k) := by
  have hpred : preimages k i =
      Nat.count (fun word => word ≡ i [MOD domainSize k]) rawSize := by
    apply Nat.le_antisymm
    · apply Nat.count_mono_left
      intro word _ h
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hi] using h
    · apply Nat.count_mono_left
      intro word _ h
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hi] using h
  have hdiv : rawSize / domainSize k = 2 ^ (32 - k) := by
    rw [raw_size_factor k hk]
    simp [domainSize]
  have hmod : rawSize % domainSize k = 0 := by
    rw [raw_size_factor k hk]
    simp [domainSize]
  have hm : 0 < domainSize k := by simp [domainSize]
  rw [hpred, Nat.count_modEq_card rawSize hm i, Nat.mod_eq_of_lt hi, hdiv, hmod]
  simp

def goodRawWords (k : Nat) (good : Finset (Fin (domainSize k))) :
    Finset Nat :=
  (Finset.range rawSize).filter (fun word => sampleIndex k word ∈ good)

theorem good_raw_words_card (k : Nat) (hk : k ≤ 32)
    (good : Finset (Fin (domainSize k))) :
    (goodRawWords k good).card = good.card * 2 ^ (32 - k) := by
  have hfiber (i : Fin (domainSize k)) :
      preimages k i.val =
        ((Finset.range rawSize).filter fun word => sampleIndex k word = i).card := by
    rw [preimages, Nat.count_eq_card_filter_range]
    apply congrArg Finset.card
    ext word
    simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    intro _
    change (sampleIndex k word).val = i.val ↔ sampleIndex k word = i
    exact (Fin.ext_iff).symm
  have hcard : (goodRawWords k good).card =
      (∑ i ∈ good, preimages k i.val) := by
    unfold goodRawWords
    simp_rw [hfiber]
    exact (Finset.sum_card_fiberwise_eq_card_filter
      (Finset.range rawSize) good (sampleIndex k)).symm
  rw [hcard]
  simp_rw [preimages_exact k _ hk (Fin.isLt _)]
  simp [Finset.sum_const, mul_comm]

def goodRawFin (k : Nat) (good : Finset (Fin (domainSize k))) :
    Finset (Fin rawSize) :=
  Finset.univ.filter (fun word => sampleIndex k word.val ∈ good)

theorem good_raw_fin_card (k : Nat) (good : Finset (Fin (domainSize k))) :
    (goodRawFin k good).card = (goodRawWords k good).card := by
  symm
  apply Finset.card_bij
    (fun n hn => (⟨n, Finset.mem_range.mp (Finset.mem_filter.mp hn).1⟩ : Fin rawSize))
  · intro n hn
    simp only [goodRawFin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Finset.mem_filter.mp hn).2
  · intro a ha b hb h
    exact congrArg Fin.val h
  · intro i hi
    refine ⟨i.val, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨i.isLt, (Finset.mem_filter.mp hi).2⟩
    · exact Fin.ext rfl

/-- The exact fixed-good-set probability in the ideal uniform raw-word
product space. Repeated query positions are counted as repeated draws. -/
theorem ideal_raw_all_good_fraction (k draws : Nat) (hk : k ≤ 32)
    (good : Finset (Fin (domainSize k))) :
    ((QuerySampling.goodSequences draws (goodRawFin k good)).card : ℚ) /
        (Fintype.card (Fin draws → Fin rawSize) : ℚ) =
      ((good.card : ℚ) / (domainSize k : ℚ)) ^ draws := by
  haveI : Nonempty (Fin rawSize) := ⟨⟨0, by norm_num [rawSize]⟩⟩
  rw [QuerySampling.ideal_all_good_fraction,
    good_raw_fin_card, good_raw_words_card k hk]
  have hratio : ((good.card * 2 ^ (32 - k) : Nat) : ℚ) / (rawSize : ℚ) =
      (good.card : ℚ) / (domainSize k : ℚ) := by
    rw [raw_size_factor k hk]
    push_cast
    field_simp
  simpa only [Fintype.card_fin] using
    congrArg (fun q : ℚ => q ^ draws) hratio

end S31.Gadgets.PcsFri.RawMaskedQuery
