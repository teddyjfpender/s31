import Mathlib.Tactic

/-!
Exact rational arithmetic for one *published upper-bound expression* in
S-two Whitepaper (2026/532), Theorem 4, first FRI folding round. It is not a
lower bound on attack success. Application to native S31 needs a separate
protocol refinement, which is not proved here.

For candidate N >= 2^20 and B >= 2, the first line domain S₀=N*B/2 has at
least 2^20 elements. Its code rate is 1/B+1/S₀ <= 1/2+1/2^20 < 9/16.
The theorem's Guruswami-Sudan multiplicity m >= 3 therefore gives
ell=(m+1)/(2 sqrt(rate)) > 8/3. The positive leading term of the quoted
fold-error upper bound is 2*ell^5*S₀/(rate*|QM31|). This module verifies the
resulting favorable floor already exceeds 2^-96.
-/

namespace S31.PcsFri.StwoMultidomainEnvelope

private def q : ℕ := 2147483647

private def favorableFloor : ℚ :=
  2 * ((8 : ℚ) / 3) ^ 5 * (2 ^ 20 : ℚ) /
    (((9 : ℚ) / 16) * (q : ℚ) ^ 4)

theorem favorable_first_fold_floor_exceeds_96 :
    (1 : ℚ) / 2 ^ 96 < favorableFloor := by
  norm_num [favorableFloor, q]

theorem candidate_line_rate_below_nine_sixteenths
    {n b : ℕ} (hn : 2 ^ 20 ≤ n) (hb : 2 ≤ b) :
    (1 : ℚ) / b + 2 / ((n : ℚ) * b) < 9 / 16 := by
  have hnq : (2 ^ 20 : ℚ) ≤ n := by exact_mod_cast hn
  have hbq : (2 : ℚ) ≤ b := by exact_mod_cast hb
  have hbn : (0 : ℚ) < b := by linarith
  have hnn : (0 : ℚ) < n := by linarith
  have hnb : (2 ^ 20 : ℚ) * 2 ≤ (n : ℚ) * b := by nlinarith
  have hfirst : (1 : ℚ) / b ≤ 1 / 2 := by
    apply (div_le_div_iff₀ hbn (by norm_num)).2
    linarith
  have hsecond : (2 : ℚ) / ((n : ℚ) * b) ≤ 1 / 2 ^ 20 := by
    apply (div_le_div_iff₀ (mul_pos hnn hbn) (by norm_num)).2
    nlinarith
  linarith [hfirst, hsecond]

theorem guruswami_sudan_list_floor
    {rate : ℝ} {m : ℕ} (hrate : 0 < rate)
    (hrate_max : rate ≤ 9 / 16) (hm : 3 ≤ m) :
    (8 / 3 : ℝ) ≤ ((m : ℝ) + 1) / (2 * Real.sqrt rate) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt rate := Real.sqrt_nonneg rate
  have hsqrt_sq : (Real.sqrt rate) ^ 2 = rate :=
    Real.sq_sqrt (le_of_lt hrate)
  have hsqrt_max : Real.sqrt rate ≤ 3 / 4 := by nlinarith
  have hdenom : 0 < (2 : ℝ) * Real.sqrt rate := by
    have : 0 < Real.sqrt rate := Real.sqrt_pos.2 hrate
    positivity
  have hm_real : (3 : ℝ) ≤ m := by exact_mod_cast hm
  apply (le_div_iff₀ hdenom).2
  nlinarith

theorem b2_johnson_boundary_requires_m_at_least_nine :
    (8 : ℝ) < Real.sqrt (1 / 2) /
      (2 * ((3 / 4 : ℝ) - Real.sqrt (1 / 2))) := by
  have hroot_nonneg : 0 ≤ Real.sqrt (1 / 2 : ℝ) := Real.sqrt_nonneg _
  have hroot_sq : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = 1 / 2 := by
    norm_num [Real.sq_sqrt]
  have hroot_low : (12 / 17 : ℝ) < Real.sqrt (1 / 2) := by nlinarith
  have hroot_high : Real.sqrt (1 / 2 : ℝ) < 3 / 4 := by nlinarith
  apply (lt_div_iff₀ (by nlinarith :
    0 < (2 : ℝ) * ((3 / 4 : ℝ) - Real.sqrt (1 / 2)))).2
  nlinarith

private def remark15B2M9Floor : ℚ :=
  6 * (2 * (6 : ℚ) ^ 4 / (3 * (1 / 2)) + 1) * (2 ^ 20 : ℚ) /
    (q : ℚ) ^ 4

theorem remark15_b2_m9_favorable_floor_exceeds_96 :
    (1 : ℚ) / 2 ^ 96 < remark15B2M9Floor := by
  norm_num [remark15B2M9Floor, q]

end S31.PcsFri.StwoMultidomainEnvelope
