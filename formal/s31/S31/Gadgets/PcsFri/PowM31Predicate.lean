import S31.Gadgets.PcsFri.M31MaskedQuery
import Mathlib.Tactic

/-!
The selected Gate channel checks PoW trailing zero bits *after* M31 reduction
of the first 32-bit BLAKE2s word. For native `bits ≤ 31`, the byte-level
predicate reduces to a low-bit mask of that word; the Zig check and source
pin are separate correspondence evidence. The finite count below is the
conditional uniform-raw-word count, not a random-oracle or grinding theorem.
-/

namespace S31.Gadgets.PcsFri.PowM31Predicate

open S31.Gadgets.PcsFri.M31MaskedQuery

/-- Arithmetic first-word predicate used by the M31 PoW hash for bit counts
up to 31, after the selected hasher's per-word reduction. -/
def acceptsFirstWord (bits word : Nat) : Prop :=
  M31WordReduction.reducedWord word &&& (size bits - 1) = 0

/-- The PoW predicate is the zero fiber of the same reduced-and-masked map
used for query positions, for *every* raw 32-bit first word. -/
theorem accepts_first_word_iff_zero_query (bits word : Nat)
    (hword : word < rawSize) :
    acceptsFirstWord bits word ↔ (sampleIndex bits word).val = 0 := by
  unfold acceptsFirstWord
  have hmod : M31WordReduction.reducedWord word &&& (size bits - 1) =
      M31WordReduction.reducedWord word % size bits := by
    simp [size, Nat.and_two_pow_sub_one_eq_mod]
  rw [hmod, native_reduced_index_eq bits word (by simpa [rawSize] using hword)]
  rfl

/-- A uniform raw 32-bit word has exactly this many favorable words for
`1 ≤ bits ≤ 31`. This is a count, not an assertion of native independence. -/
theorem favorable_raw_word_count (bits : Nat)
    (hbits : 1 ≤ bits) (hmax : bits ≤ 31) :
    preimages bits 0 = 2 * 2 ^ (31 - bits) + 1 := by
  rw [preimages_exact bits 0 hbits hmax (by simp [size])]
  have hlast : 0 < size bits - 1 := by
    have : 1 < size bits := by
      unfold size
      exact one_lt_pow₀ (by omega) (by omega)
    omega
  simp only [if_pos hlast, if_neg (by decide : 0 ≠ 1)]
  have hq : 0 < 2 ^ (31 - bits) := by positivity
  rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 ^ (31 - bits))]
  simp

/-- The actual finite set of raw first words accepted by the arithmetic
PoW predicate, without introducing a probability assumption. -/
noncomputable def acceptingRawWords (bits : Nat) : Finset (Fin rawSize) := by
  classical
  exact Finset.univ.filter (fun word => acceptsFirstWord bits word.val)

theorem accepting_raw_words_eq_zero_fiber (bits : Nat) :
    acceptingRawWords bits =
      goodRawFin bits {⟨0, by simp [size]⟩} := by
  classical
  ext word
  simp only [acceptingRawWords, goodRawFin, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_singleton]
  simpa [Fin.ext_iff] using
    (accepts_first_word_iff_zero_query bits word.val word.isLt)

/-- Gate interaction PoW uses 20 bits in the pinned circuit profile. -/
theorem interaction_twenty_favorable : preimages 20 0 = 4097 := by
  simpa using favorable_raw_word_count 20 (by omega) (by omega)

/-- Gate FRI PoW uses 26 bits in the pinned FRI profile. -/
theorem fri_twenty_six_favorable : preimages 26 0 = 65 := by
  simpa using favorable_raw_word_count 26 (by omega) (by omega)

/-- Each native M31 PoW predicate has one extra favorable raw first word
compared with an ideal direct low-bit check of an unmodified 32-bit word. -/
theorem favorable_exceeds_ideal (bits : Nat)
    (hbits : 1 ≤ bits) (hmax : bits ≤ 31) :
    preimages bits 0 = 2 ^ (32 - bits) + 1 := by
  rw [favorable_raw_word_count bits hbits hmax]
  have heq : 32 - bits = (31 - bits) + 1 := by omega
  rw [heq, pow_succ]
  omega

theorem accepting_raw_words_card (bits : Nat)
    (hbits : 1 ≤ bits) (hmax : bits ≤ 31) :
    (acceptingRawWords bits).card = 2 ^ (32 - bits) + 1 := by
  rw [accepting_raw_words_eq_zero_fiber, good_raw_fin_card]
  simp [weightedCount, favorable_exceeds_ideal bits hbits hmax]

end S31.Gadgets.PcsFri.PowM31Predicate
