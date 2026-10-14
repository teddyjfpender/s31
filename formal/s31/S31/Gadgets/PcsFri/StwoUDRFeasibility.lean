import Mathlib.Tactic

/-!
Necessary arithmetic for S-two Whitepaper (2026/532), Appendix A Lemma 7
and Theorem 6, in the unique-decoding regime. This checks a limitation of the
*quoted proof expression*, not an attack bound or native PCS/FRI soundness.

The OOD round's published expression contains a positive numerator at least
one over a circle-point set of size less than |QM31|=(2^31-1)^4. The BCS
formula multiplies the maximum round error by T+R >= T. Even this favorable
floor exceeds 2^-96 when T >= 2^28. No grinding credit is assigned to OOD.
-/

namespace S31.PcsFri.StwoUDRFeasibility

private def q : ℕ := 2147483647

theorem qm31_order_below_two_pow_124 :
    ((q : ℚ) ^ 4) < (2 : ℚ) ^ 124 := by
  norm_num [q]

theorem qm31_inverse_order_below_two_pow_neg_96 :
    (1 : ℚ) / (q : ℚ) ^ 4 < (1 : ℚ) / 2 ^ 96 := by
  norm_num [q]

theorem bcs_ood_floor_exceeds_96_of_T_at_least_two_pow_28
    {T : ℕ} (hT : 2 ^ 28 ≤ T) :
    (1 : ℚ) / 2 ^ 96 < (T : ℚ) / (q : ℚ) ^ 4 := by
  have hTq : (2 ^ 28 : ℚ) ≤ T := by exact_mod_cast hT
  have hF : ((q : ℚ) ^ 4) < (2 : ℚ) ^ 124 :=
    qm31_order_below_two_pow_124
  have hFpos : (0 : ℚ) < (q : ℚ) ^ 4 := by norm_num [q]
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 2 ^ 96) hFpos).2
  nlinarith

theorem paper_ood_denominator_below_qm31 :
    ((q : ℚ) ^ 4 - q - 2) < (q : ℚ) ^ 4 := by
  norm_num [q]

/-! For B=2, the unique-decoding interval forces alpha=1-theta>3/4.
The native one-fold profiles draw 70 raw queries. This is a limitation of
the published *ungrinded expression*, not a lower bound on true error. -/

theorem seventy_queries_boundary_exceeds_96 :
    (1 : ℚ) / 2 ^ 96 < ((3 : ℚ) / 4) ^ 70 := by
  norm_num

theorem seventy_queries_udr_expression_exceeds_96
    {alpha : ℚ} (halpha : (3 : ℚ) / 4 < alpha) :
    (1 : ℚ) / 2 ^ 96 < alpha ^ 70 := by
  have hpow : ((3 : ℚ) / 4) ^ 70 < alpha ^ 70 := by
    gcongr
  exact lt_trans seventy_queries_boundary_exceeds_96 hpow

theorem seventy_queries_bcs_work_factor_exceeds_96
    {alpha : ℚ} {T R : ℕ} (halpha : (3 : ℚ) / 4 < alpha)
    (hT : 0 < T) :
    (1 : ℚ) / 2 ^ 96 < ((T : ℚ) + R) / T * alpha ^ 70 := by
  have hquery := seventy_queries_udr_expression_exceeds_96 halpha
  have hTq : (0 : ℚ) < T := by exact_mod_cast hT
  have hfactor : (1 : ℚ) ≤ ((T : ℚ) + R) / T := by
    apply (le_div_iff₀ hTq).2
    nlinarith
  have hpositive : (0 : ℚ) ≤ alpha ^ 70 := by
    positivity
  have hmul : alpha ^ 70 ≤ ((T : ℚ) + R) / T * alpha ^ 70 := by
    nlinarith
  exact lt_of_lt_of_le hquery hmul

end S31.PcsFri.StwoUDRFeasibility
