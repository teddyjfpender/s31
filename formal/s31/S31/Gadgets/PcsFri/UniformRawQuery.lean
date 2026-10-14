import S31.Gadgets.PcsFri.RawMaskedQuery
import Mathlib.Data.Nat.Count
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Tactic

/-!
The arithmetic behind the candidate S31NAT9F raw-word query sampler.
For a domain of `n` elements, the sampler accepts exactly the initial
`⌊2^32/n⌋ * n` of the possible 32-bit words and then takes `word % n`.
Every output has the same number of accepted preimages. For native FRI
domains, `n = 2^k`, so this threshold is all of `2^32` and the cheaper
bit mask has the same value by `RawMaskedQuery.native_mask_eq`.

These finite counts assume an ideal uniform raw word. They do not establish
BLAKE2s randomness, independence across words, a bound on exceeding a finite
rejection budget, or native PCS/FRI security.
-/

namespace S31.Gadgets.PcsFri.UniformRawQuery

def rawSize : Nat := 2 ^ 32
def acceptedLimit (n : Nat) : Nat := rawSize / n * n
def preimages (n i : Nat) : Nat :=
  Nat.count (fun word => word % n = i) (acceptedLimit n)

/-- Rejection before reduction gives every residue the same accepted fiber. -/
theorem accepted_preimages_exact (n i : Nat) (hn : 0 < n) (hi : i < n) :
    preimages n i = rawSize / n := by
  have hpred : preimages n i =
      Nat.count (fun word => word ≡ i [MOD n]) (acceptedLimit n) := by
    apply Nat.le_antisymm
    · apply Nat.count_mono_left
      intro word _ h
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hi] using h
    · apply Nat.count_mono_left
      intro word _ h
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hi] using h
  have hdiv : acceptedLimit n / n = rawSize / n := by
    simp [acceptedLimit, Nat.mul_div_cancel _ hn]
  have hmod : acceptedLimit n % n = 0 := by
    simp [acceptedLimit]
  rw [hpred, Nat.count_modEq_card (acceptedLimit n) hn i,
    Nat.mod_eq_of_lt hi, hdiv, hmod]
  simp

/-- For a power-of-two FRI domain, rejection never occurs. -/
theorem power_two_no_rejection (k : Nat) (hk : k ≤ 32) :
    acceptedLimit (2 ^ k) = rawSize := by
  have hdiv : 2 ^ k ∣ 2 ^ 32 := pow_dvd_pow 2 hk
  simpa [acceptedLimit, rawSize] using (Nat.div_mul_cancel hdiv)

end S31.Gadgets.PcsFri.UniformRawQuery
