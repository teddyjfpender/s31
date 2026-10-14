import Mathlib.Tactic

/-!
An exact arithmetic boundary for the *isolated* batching term in the
published multi-domain S-two expression. The parameters are the candidate
sparse Gate values `N = 2^16`, `B = 2`, `D₀ = N B² = 2^18`, `T = 2^64`, and the
most favorable BCS round count `R = 1`. This theorem does not identify a
native batch with the paper's padded width `M`, prove `D₀ = N B²` for the
selected protocol, account for the other positive error terms, or certify
native PCS/FRI soundness.
-/

namespace S31.PcsFri.SparseP05ConditionalBatchCap

private def q : ℕ := 2147483647
private def t : ℕ := 2 ^ 64
private def d0 : ℕ := 2 ^ 18

/-- The isolated work-factor inequality after clearing positive denominators.
The factor `M - 1` is the paper's common padded batch width term. -/
def isolatedFits (M : ℕ) : Prop :=
  (M - 1) * d0 * 2 ^ 96 * (t + 1) ≤ q ^ 4 * t

theorem isolated_fits_iff_cap {M : ℕ} (hM : 1 ≤ M) :
    isolatedFits M ↔ M ≤ 1024 := by
  unfold isolatedFits q t d0
  norm_num at *
  omega

theorem cap_1024_fits : isolatedFits 1024 := by
  exact (isolated_fits_iff_cap (by omega)).2 (by omega)

theorem cap_1025_fails : ¬ isolatedFits 1025 := by
  intro h
  have := (isolated_fits_iff_cap (M := 1025) (by omega)).1 h
  omega

end S31.PcsFri.SparseP05ConditionalBatchCap
