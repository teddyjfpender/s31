import S31.Gadgets.PcsFri.RawMaskedQuery
import Mathlib.Tactic

/-!
The raw Gate channel uses unreduced BLAKE2s words. These are finite-count and
byte-input results conditional on the source audit; they do not model an
adaptive adversary, BLAKE2s as a random oracle, or the native PCS relation.
-/

namespace S31.Gadgets.PcsFri.RawGateBcsBoundary

open S31.Gadgets.PcsFri

/-- The 20-bit raw PoW mask has exactly 4096 favorable first words. -/
theorem interaction_pow_zero_fiber :
    RawMaskedQuery.preimages 20 0 = 4096 := by
  simpa using RawMaskedQuery.preimages_exact 20 0 (by decide) (by decide)

/-- The 26-bit raw PoW mask has exactly 64 favorable first words. -/
theorem fri_pow_zero_fiber :
    RawMaskedQuery.preimages 26 0 = 64 := by
  simpa using RawMaskedQuery.preimages_exact 26 0 (by decide) (by decide)

/-- The accepted 70-query epoch requires nine fresh counter encodings. -/
theorem raw_gate_query_epoch_counter_bound :
    (70 + 8 - 1) / 8 = 9 ∧
    ∀ i ∈ List.range 9, i < 2 ^ 32 := by
  constructor
  · decide
  · intro i hi
    have h : i < 9 := List.mem_range.mp hi
    omega

/-- Paper-only ROM collision arithmetic at T=2^64 and lambda=256.
Applying this term to native S31 still needs a BCS/ROM reduction. -/
theorem ideal_paper_collision_work_factor_below_126 :
    (3 * (((2 : ℚ) ^ 64) ^ 2 + 1) / ((2 : ℚ) ^ 256 * 2 ^ 64)) <
      (1 : ℚ) / 2 ^ 126 := by
  norm_num

end S31.Gadgets.PcsFri.RawGateBcsBoundary
