import Mathlib.Tactic

/-!
Arithmetic correspondence for the native Blake2sM31 hasher's vectorized
`reduceToM31` path. `word` models one 32-bit lane. The source contract
pins the exact bit fold and conditional subtraction in Zig. This module
proves that arithmetic equals reduction modulo `p = 2^31 - 1`.
-/

namespace S31.Gadgets.PcsFri.M31WordReduction

private def p : Nat := 2 ^ 31 - 1
private def wordSize : Nat := 2 ^ 32

/-- The native first Mersenne fold, before its conditional subtraction. -/
def foldedWord (word : Nat) : Nat :=
  (word &&& p) + (word >>> 31)

/-- The native one-subtraction result, modeled in naturals. -/
def reducedWord (word : Nat) : Nat :=
  if p ≤ foldedWord word then foldedWord word - p else foldedWord word

theorem folded_word_eq_quotient_remainder (word : Nat) :
    foldedWord word = word % (2 ^ 31) + word / (2 ^ 31) := by
  unfold foldedWord p
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem folded_word_le_p_add_one (word : Nat) (hword : word < wordSize) :
    foldedWord word ≤ p + 1 := by
  rw [folded_word_eq_quotient_remainder]
  have hdiv : word / (2 ^ 31) ≤ 1 := by
    unfold wordSize at hword
    omega
  have hmod : word % (2 ^ 31) < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  unfold p
  omega

/-- The Zig `+%` in the vector path cannot overflow a u32 lane. -/
theorem folded_word_no_u32_overflow (word : Nat) (hword : word < wordSize) :
    foldedWord word < wordSize := by
  have h := folded_word_le_p_add_one word hword
  norm_num [p, wordSize] at *
  omega

theorem reduced_word_eq_mod (word : Nat) (hword : word < wordSize) :
    reducedWord word = word % p := by
  have hfold := folded_word_eq_quotient_remainder word
  have hbound := folded_word_le_p_add_one word hword
  unfold reducedWord
  rw [hfold]
  have hdiv : word / (2 ^ 31) ≤ 1 := by
    unfold wordSize at hword
    omega
  have hmod : word % (2 ^ 31) < 2 ^ 31 := Nat.mod_lt _ (by norm_num)
  have hdecomp := Nat.mod_add_div word (2 ^ 31)
  unfold p at *
  split_ifs with h
  · omega
  · omega

/-- Public numeral form for clients modeling the native 32-bit lane. -/
theorem reduced_word_eq_modulus (word : Nat) (hword : word < 2 ^ 32) :
    reducedWord word = word % (2 ^ 31 - 1) := by
  simpa [p] using reduced_word_eq_mod word (by simpa [wordSize] using hword)

theorem reduced_word_canonical (word : Nat) (hword : word < 2 ^ 32) :
    reducedWord word < 2 ^ 31 - 1 := by
  rw [reduced_word_eq_modulus word hword]
  exact Nat.mod_lt _ (by norm_num)

end S31.Gadgets.PcsFri.M31WordReduction
