import S31.Gadgets.PcsFri.QuerySampling
import S31.Gadgets.PcsFri.M31WordReduction
import Mathlib.Data.Nat.Count
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic

/-!
Exact counting for a single ideal uniform 32-bit hash word after the pinned
Blake2sM31 channel's Mersenne reduction and `drawQueries` low-bit mask.
The random-oracle independence of successive words is an external premise.
-/

namespace S31.Gadgets.PcsFri.M31MaskedQuery

private def p : Nat := 2 ^ 31 - 1
private def rawSize : Nat := 2 ^ 32
private def size (k : Nat) : Nat := 2 ^ k

private def index (k word : Nat) : Nat := (word % p) % size k

/-- The bit-folded native M31 word and the arithmetic query model yield the
same masked index for every 32-bit input. -/
theorem native_reduced_index_eq (k word : Nat) (hword : word < 2 ^ 32) :
    M31WordReduction.reducedWord word % size k = index k word := by
  rw [M31WordReduction.reduced_word_eq_modulus word hword]
  rfl

def preimages (k i : Nat) : Nat :=
  Nat.count (fun word => index k word = i) rawSize

private theorem raw_size_eq : rawSize = p + p + 2 := by
  norm_num [rawSize, p]

private theorem p_pos : 0 < p := by norm_num [p]

private theorem count_two_periods (k i : Nat) (hk : 1 ≤ k) :
    preimages k i =
      2 * Nat.count (fun r => r % size k = i) p +
      (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) := by
  let f : Nat → Prop := fun word => index k word = i
  have hperiod : ∀ word, f (p + word) = f word := by
    intro word
    simp [f, index, Nat.add_mod_left]
  have htwo : ∀ word, f (p + p + word) = f word := by
    intro word
    simpa only [Nat.add_assoc] using (hperiod (p + word)).trans (hperiod word)
  unfold preimages
  rw [raw_size_eq, show p + p + 2 = p + (p + 2) by omega,
    Nat.count_add (fun word => index k word = i) p (p + 2),
    Nat.count_add (fun word => index k (p + word) = i) p 2]
  simp only [Nat.add_assoc]
  have hfirst : Nat.count (fun word => index k word = i) p =
      Nat.count (fun r => r % size k = i) p := by
    apply Nat.le_antisymm
    · apply Nat.count_mono_left
      intro word hword h
      simpa [index, Nat.mod_eq_of_lt hword] using h
    · apply Nat.count_mono_left
      intro word hword h
      simpa [index, Nat.mod_eq_of_lt hword] using h
  have hsecond : Nat.count (fun word => index k (p + word) = i) p =
      Nat.count (fun r => r % size k = i) p := by
    apply Nat.le_antisymm
    · apply Nat.count_mono_left
      intro word hword h
      simpa [index, Nat.add_mod_left, Nat.mod_eq_of_lt hword] using h
    · apply Nat.count_mono_left
      intro word hword h
      simpa [index, Nat.add_mod_left, Nat.mod_eq_of_lt hword] using h
  have htail : Nat.count (fun word => index k (p + p + word) = i) 2 =
      (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) := by
    rw [Nat.count_succ, Nat.count_succ, Nat.count_zero]
    have hsize : 1 < size k := by
      unfold size
      exact one_lt_pow₀ (by omega) (by omega)
    have hp1 : 1 < p := by norm_num [p]
    have hmod : (p + p + 1) % p = 1 := by
      rw [show p + p + 1 = p + (p + 1) by omega]
      simp [Nat.add_mod_left, Nat.mod_eq_of_lt hp1]
    simp [index, hmod, Nat.mod_eq_of_lt hsize, eq_comm]
  have htail' : Nat.count (fun word => index k (p + (p + word)) = i) 2 =
      (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) := by
    simpa only [Nat.add_assoc] using htail
  rw [hfirst, hsecond, htail']
  omega

private theorem size_times_quotient (k : Nat) (hk : k ≤ 31) :
    size k * 2 ^ (31 - k) = p + 1 := by
  have hsum : k + (31 - k) = 31 := by omega
  unfold size p
  rw [← pow_add, hsum]
  norm_num

private theorem p_div_mod (k : Nat) (hk : k ≤ 31) :
    p / size k = 2 ^ (31 - k) - 1 ∧
    p % size k = size k - 1 := by
  let m := size k
  let q := 2 ^ (31 - k)
  have hm : 0 < m := by simp [m, size]
  have hq : 0 < q := by simp [q]
  have hpq : m * q = p + 1 := size_times_quotient k hk
  have hdecomp : p = m * (q - 1) + (m - 1) := by
    have hq' : q - 1 + 1 = q := by omega
    have hm' : m - 1 + 1 = m := by omega
    calc
      p = m * q - 1 := by omega
      _ = m * (q - 1 + 1) - 1 := by rw [hq']
      _ = m * (q - 1) + m - 1 := by rw [mul_add]; simp
      _ = m * (q - 1) + (m - 1) := by omega
  have hrem : m - 1 < m := by omega
  constructor
  · rw [hdecomp, Nat.mul_add_div hm]
    simp [q, Nat.div_eq_of_lt hrem]
  · rw [hdecomp, Nat.mul_add_mod]
    simp [m, Nat.mod_eq_of_lt hrem]

private theorem residue_count (k i : Nat) (hk : k ≤ 31)
    (hi : i < size k) :
    Nat.count (fun r => r % size k = i) p =
      2 ^ (31 - k) - 1 + (if i < size k - 1 then 1 else 0) := by
  have hm : 0 < size k := by simp [size]
  have hformula := Nat.count_modEq_card p hm i
  have hmod : i % size k = i := Nat.mod_eq_of_lt hi
  have hpred : Nat.count (fun r => r % size k = i) p =
      Nat.count (fun r => r ≡ i [MOD size k]) p := by
    apply Nat.le_antisymm
    · apply Nat.count_mono_left
      intro r _ h
      simpa [Nat.ModEq, hmod] using h
    · apply Nat.count_mono_left
      intro r _ h
      simpa [Nat.ModEq, hmod] using h
  rw [hpred, hformula, hmod]
  rw [(p_div_mod k hk).1, (p_div_mod k hk).2]

/-- The exact 32-bit preimage multiplicity of one masked query index. -/
theorem preimages_exact (k i : Nat) (hk : 1 ≤ k) (hk31 : k ≤ 31)
    (hi : i < size k) :
    preimages k i =
      2 * (2 ^ (31 - k) - 1 + (if i < size k - 1 then 1 else 0)) +
      (if i = 0 then 1 else 0) + (if i = 1 then 1 else 0) := by
  rw [count_two_periods k i hk, residue_count k i hk31 hi]

private def baseline (k : Nat) : Nat := 2 * 2 ^ (31 - k)

def weightedCount (k : Nat) (good : Finset (Fin (size k))) : Nat :=
  ∑ i ∈ good, preimages k i.val

private def sampleIndex (k word : Nat) : Fin (size k) :=
  ⟨index k word, Nat.mod_lt _ (by simp [size])⟩

/-- The actual finite set of 32-bit raw words mapping into `good`. -/
def goodRawWords (k : Nat) (good : Finset (Fin (size k))) : Finset Nat :=
  (Finset.range rawSize).filter (fun word => sampleIndex k word ∈ good)

theorem weighted_count_eq_good_raw_words (k : Nat)
    (good : Finset (Fin (size k))) :
    weightedCount k good = (goodRawWords k good).card := by
  have hfiber (i : Fin (size k)) :
      preimages k i.val =
        ((Finset.range rawSize).filter fun word => sampleIndex k word = i).card := by
    rw [preimages, Nat.count_eq_card_filter_range]
    apply congrArg Finset.card
    ext word
    simp only [Finset.mem_filter, Finset.mem_range, and_congr_right_iff]
    intro _
    change (sampleIndex k word).val = i.val ↔ sampleIndex k word = i
    exact (Fin.ext_iff).symm
  unfold weightedCount goodRawWords
  simp_rw [hfiber]
  exact Finset.sum_card_fiberwise_eq_card_filter
    (Finset.range rawSize) good (sampleIndex k)

/-- The same raw-word event represented in the finite uniform sample type. -/
def goodRawFin (k : Nat) (good : Finset (Fin (size k))) :
    Finset (Fin rawSize) :=
  Finset.univ.filter (fun word => sampleIndex k word.val ∈ good)

theorem good_raw_fin_card (k : Nat) (good : Finset (Fin (size k))) :
    (goodRawFin k good).card = weightedCount k good := by
  rw [weighted_count_eq_good_raw_words]
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

theorem preimages_one_zero : preimages 1 0 = baseline 1 + 1 := by
  rw [preimages_exact 1 0 (by omega) (by omega) (by norm_num [size])]
  norm_num [baseline, size]

theorem preimages_one_one : preimages 1 1 = baseline 1 - 1 := by
  rw [preimages_exact 1 1 (by omega) (by omega) (by norm_num [size])]
  norm_num [baseline, size]

theorem preimages_one_le (i : Fin (size 1)) :
    preimages 1 i.val ≤ baseline 1 + (if i.val = 0 then 1 else 0) := by
  have hi : i.val < 2 := by simpa [size] using i.isLt
  by_cases hz : i.val = 0
  · simp [hz, preimages_one_zero]
  · have ho : i.val = 1 := by omega
    simp [ho, preimages_one_one]

private theorem size_ge_four (k : Nat) (hk : 2 ≤ k) :
    4 ≤ size k := by
  unfold size
  have h := pow_le_pow_right₀ (by omega : (1 : Nat) ≤ 2) hk
  norm_num at h
  exact h

theorem preimages_ge_two (k i : Nat) (hk : 2 ≤ k) (hk31 : k ≤ 31)
    (hi : i < size k) :
    preimages k i ≤ baseline k + (if i = 0 then 1 else 0) +
      (if i = 1 then 1 else 0) := by
  rw [preimages_exact k i (by omega) hk31 hi]
  have hq : 0 < 2 ^ (31 - k) := by positivity
  have hm : 4 ≤ size k := size_ge_four k hk
  unfold baseline
  by_cases hlast : i = size k - 1
  · simp [hlast]
  · have hbefore : i < size k - 1 := by omega
    simp [hbefore]

theorem preimages_ge_two_zero (k : Nat) (hk : 2 ≤ k) (hk31 : k ≤ 31) :
    preimages k 0 = baseline k + 1 := by
  have hm := size_ge_four k hk
  have hq : 0 < 2 ^ (31 - k) := by positivity
  rw [preimages_exact k 0 (by omega) hk31 (by omega)]
  simp only [if_pos (show 0 < size k - 1 by omega),
    if_neg (by decide : 0 ≠ 1)]
  unfold baseline
  have hq1 : 1 ≤ 2 ^ (31 - k) := by omega
  simp [Nat.sub_add_cancel hq1]

theorem preimages_ge_two_one (k : Nat) (hk : 2 ≤ k) (hk31 : k ≤ 31) :
    preimages k 1 = baseline k + 1 := by
  have hm := size_ge_four k hk
  have hq : 0 < 2 ^ (31 - k) := by positivity
  rw [preimages_exact k 1 (by omega) hk31 (by omega)]
  simp only [if_pos (show 1 < size k - 1 by omega),
    if_neg (by decide : 1 ≠ 0)]
  unfold baseline
  have hq1 : 1 ≤ 2 ^ (31 - k) := by omega
  simp [Nat.sub_add_cancel hq1]

theorem weighted_count_ge_two_bound (k : Nat) (hk : 2 ≤ k)
    (hk31 : k ≤ 31) (good : Finset (Fin (size k))) :
    weightedCount k good ≤ baseline k * good.card + 2 := by
  have hpoint : ∀ i ∈ good, preimages k i.val ≤
      baseline k + (if i.val = 0 then 1 else 0) +
        (if i.val = 1 then 1 else 0) := by
    intro i _
    exact preimages_ge_two k i.val hk hk31 i.isLt
  calc
    weightedCount k good ≤ ∑ i ∈ good,
        (baseline k + (if i.val = 0 then 1 else 0) +
          (if i.val = 1 then 1 else 0)) := Finset.sum_le_sum hpoint
    _ ≤ baseline k * good.card + 2 := by
      simp only [Finset.sum_add_distrib]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.sum_ite,
        Finset.sum_const, nsmul_eq_mul,
        mul_one, mul_zero]
      have hz : (good.filter fun x => x.val = 0).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact Fin.ext ((Finset.mem_filter.mp ha).2.trans
          (Finset.mem_filter.mp hb).2.symm)
      have ho : (good.filter fun x => x.val = 1).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact Fin.ext ((Finset.mem_filter.mp ha).2.trans
          (Finset.mem_filter.mp hb).2.symm)
      have hmul : good.card * baseline k = baseline k * good.card :=
        Nat.mul_comm _ _
      norm_cast at *
      omega

theorem weighted_count_one_bound (good : Finset (Fin (size 1))) :
    weightedCount 1 good ≤ baseline 1 * good.card + 1 := by
  have hpoint : ∀ i ∈ good, preimages 1 i.val ≤
      baseline 1 + (if i.val = 0 then 1 else 0) := by
    intro i _
    exact preimages_one_le i
  calc
    weightedCount 1 good ≤ ∑ i ∈ good,
        (baseline 1 + (if i.val = 0 then 1 else 0)) :=
          Finset.sum_le_sum hpoint
    _ ≤ baseline 1 * good.card + 1 := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        nsmul_eq_mul, Finset.sum_ite, mul_one, mul_zero]
      have hz : (good.filter fun x => x.val = 0).card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        exact Fin.ext ((Finset.mem_filter.mp ha).2.trans
          (Finset.mem_filter.mp hb).2.symm)
      have hmul : good.card * baseline 1 = baseline 1 * good.card :=
        Nat.mul_comm _ _
      norm_cast at *
      omega

/-- The upper bound is attained by the one-element good set `{0}`. -/
theorem weighted_count_one_sharp :
    weightedCount 1 ({⟨0, by norm_num [size]⟩} : Finset (Fin (size 1))) =
      baseline 1 * 1 + 1 := by
  simp [weightedCount, preimages_one_zero]

/-- For every k ≥ 2, `{0,1}` attains the two-word excess. -/
theorem weighted_count_ge_two_sharp (k : Nat) (hk : 2 ≤ k)
    (hk31 : k ≤ 31) :
    let zero : Fin (size k) := ⟨0, by have := size_ge_four k hk; omega⟩
    let one : Fin (size k) := ⟨1, by have := size_ge_four k hk; omega⟩
    weightedCount k ({zero, one} : Finset (Fin (size k))) =
      baseline k * 2 + 2 := by
  intro zero one
  have hne : zero ≠ one := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [zero, one] at hv
    omega
  have hz : preimages k zero.val = baseline k + 1 := by
    simpa [zero] using preimages_ge_two_zero k hk hk31
  have ho : preimages k one.val = baseline k + 1 := by
    simpa [one] using preimages_ge_two_one k hk hk31
  simp [weightedCount, hne, hz, ho]
  omega

private theorem raw_size_factor (k : Nat) (hk31 : k ≤ 31) :
    rawSize = baseline k * size k := by
  have h := size_times_quotient k hk31
  have hr := raw_size_eq
  dsimp [baseline]
  nlinarith [h]

/-- The conditional distribution of one masked index from one ideal uniform
32-bit word. The native source binding verifies the index map separately. -/
def maskedMass (k : Nat) (good : Finset (Fin (size k))) : ℚ :=
  (weightedCount k good : ℚ) / (rawSize : ℚ)

def uniformMass (k : Nat) (good : Finset (Fin (size k))) : ℚ :=
  (good.card : ℚ) / (size k : ℚ)

/-- The product-space event checks each raw index before any deduplication. -/
theorem raw_good_sequence_iff (k draws : Nat)
    (good : Finset (Fin (size k))) (words : Fin draws → Fin rawSize) :
    words ∈ QuerySampling.goodSequences draws (goodRawFin k good) ↔
      ∀ j, sampleIndex k (words j).val ∈ good := by
  simp [QuerySampling.good_sequences_member, goodRawFin]

/-- Exact fraction of all `draws`-tuples of 32-bit words whose masked M31
indices lie in the fixed good set. This is finite product counting, not a
claim that the native Fiat-Shamir transcript is an ideal random oracle. -/
theorem exact_raw_product_fraction (k draws : Nat)
    (good : Finset (Fin (size k))) :
    ((QuerySampling.goodSequences draws (goodRawFin k good)).card : ℚ) /
      (Fintype.card (Fin draws → Fin rawSize) : ℚ) =
        maskedMass k good ^ draws := by
  haveI : Nonempty (Fin rawSize) :=
    ⟨⟨0, by norm_num [rawSize]⟩⟩
  rw [QuerySampling.ideal_all_good_fraction]
  simp only [good_raw_fin_card, Fintype.card_fin, maskedMass]

private theorem uniform_mass_as_raw (k : Nat) (hk31 : k ≤ 31)
    (good : Finset (Fin (size k))) :
    uniformMass k good =
      ((baseline k * good.card : Nat) : ℚ) / (rawSize : ℚ) := by
  have hf := raw_size_factor k hk31
  have hs : (size k : ℚ) ≠ 0 := by simp [size]
  have hb : (baseline k : ℚ) ≠ 0 := by
    simp [baseline]
  unfold uniformMass
  rw [hf]
  push_cast
  field_simp

/-- The k=1 positive deviation is at most exactly one raw word in 2^32. -/
theorem masked_mass_one_bound (good : Finset (Fin (size 1))) :
    maskedMass 1 good ≤ uniformMass 1 good + 1 / (rawSize : ℚ) := by
  rw [uniform_mass_as_raw 1 (by omega) good]
  unfold maskedMass
  rw [← add_div]
  have h := weighted_count_one_bound good
  have hq : (weightedCount 1 good : ℚ) ≤
      ((baseline 1 * good.card : Nat) : ℚ) + 1 := by exact_mod_cast h
  exact div_le_div_of_nonneg_right hq (by positivity)

/-- For 2 ≤ k ≤ 31, the positive deviation is at most exactly two raw
words in 2^32, independent of the size of the fixed good set. -/
theorem masked_mass_ge_two_bound (k : Nat) (hk : 2 ≤ k) (hk31 : k ≤ 31)
    (good : Finset (Fin (size k))) :
    maskedMass k good ≤ uniformMass k good + 2 / (rawSize : ℚ) := by
  rw [uniform_mass_as_raw k hk31 good]
  unfold maskedMass
  rw [← add_div]
  have h := weighted_count_ge_two_bound k hk hk31 good
  have hq : (weightedCount k good : ℚ) ≤
      ((baseline k * good.card : Nat) : ℚ) + 2 := by exact_mod_cast h
  exact div_le_div_of_nonneg_right hq (by positivity)

/-- A fixed good set with ideal uniform agreement at most `alpha` has the
corresponding one-draw upper bound for the masked native sampler. -/
theorem masked_mass_one_vs_alpha (good : Finset (Fin (size 1)))
    (alpha : ℚ) (hα : uniformMass 1 good ≤ alpha) :
    maskedMass 1 good ≤ alpha + 1 / (rawSize : ℚ) := by
  exact (masked_mass_one_bound good).trans (add_le_add_left hα _)

theorem masked_mass_ge_two_vs_alpha (k : Nat) (hk : 2 ≤ k)
    (hk31 : k ≤ 31) (good : Finset (Fin (size k)))
    (alpha : ℚ) (hα : uniformMass k good ≤ alpha) :
    maskedMass k good ≤ alpha + 2 / (rawSize : ℚ) := by
  exact (masked_mass_ge_two_bound k hk hk31 good).trans
    (add_le_add_left hα _)

/-- Conditional on independent ideal uniform 32-bit hash words, the
all-good probability for `draws` masked indices is `maskedMass ^ draws`.
This theorem bounds that probability; independence is not proved here. -/
theorem independent_masked_one_vs_alpha (good : Finset (Fin (size 1)))
    (draws : Nat) (alpha : ℚ) (hα : uniformMass 1 good ≤ alpha) :
    maskedMass 1 good ^ draws ≤
      (alpha + 1 / (rawSize : ℚ)) ^ draws := by
  have hn : 0 ≤ maskedMass 1 good := by unfold maskedMass; positivity
  exact pow_le_pow_left₀ hn (masked_mass_one_vs_alpha good alpha hα) draws

theorem independent_masked_ge_two_vs_alpha (k : Nat) (hk : 2 ≤ k)
    (hk31 : k ≤ 31) (good : Finset (Fin (size k)))
    (draws : Nat) (alpha : ℚ) (hα : uniformMass k good ≤ alpha) :
    maskedMass k good ^ draws ≤
      (alpha + 2 / (rawSize : ℚ)) ^ draws := by
  have hn : 0 ≤ maskedMass k good := by unfold maskedMass; positivity
  exact pow_le_pow_left₀ hn
    (masked_mass_ge_two_vs_alpha k hk hk31 good alpha hα) draws

/-- Exact finite product-space fraction, now bounded in terms of the ideal
uniform agreement parameter. Interpreting the fraction as native transcript
probability still requires independent ideal raw words and a fixed good set. -/
theorem exact_raw_product_one_vs_alpha (good : Finset (Fin (size 1)))
    (draws : Nat) (alpha : ℚ) (hα : uniformMass 1 good ≤ alpha) :
    ((QuerySampling.goodSequences draws (goodRawFin 1 good)).card : ℚ) /
      (Fintype.card (Fin draws → Fin rawSize) : ℚ) ≤
        (alpha + 1 / (rawSize : ℚ)) ^ draws := by
  rw [exact_raw_product_fraction]
  exact independent_masked_one_vs_alpha good draws alpha hα

theorem exact_raw_product_ge_two_vs_alpha (k : Nat) (hk : 2 ≤ k)
    (hk31 : k ≤ 31) (good : Finset (Fin (size k)))
    (draws : Nat) (alpha : ℚ) (hα : uniformMass k good ≤ alpha) :
    ((QuerySampling.goodSequences draws (goodRawFin k good)).card : ℚ) /
      (Fintype.card (Fin draws → Fin rawSize) : ℚ) ≤
        (alpha + 2 / (rawSize : ℚ)) ^ draws := by
  rw [exact_raw_product_fraction]
  exact independent_masked_ge_two_vs_alpha k hk hk31 good draws alpha hα

end S31.Gadgets.PcsFri.M31MaskedQuery
