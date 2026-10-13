import Mathlib.Tactic

/-!
An arithmetic obstruction for one *published upper-bound expression* in
Circle STARKs, Appendix B, Remark 26. This says nothing about an attack on
the native verifier. Applying the expression to S31 first requires a protocol
refinement, which is not proved here.
-/

namespace S31.PcsFri.ConservativeEnvelope

private def floorTerm (n b m width : ℕ) : ℚ :=
  ((width : ℚ) - 2 / 3) * ((m : ℚ) + 1 / 2) ^ 7 / 3 *
    (b : ℚ) ^ 3 * (n : ℚ) ^ 2 / (2147483647 : ℚ) ^ 4

theorem favorable_floor_exceeds_96 :
    (1 : ℚ) / 2 ^ 96 < floorTerm 256 2 3 1 := by
  norm_num [floorTerm]

theorem floor_exceeds_96_of_at_least_256
    {n b m width : ℕ} (hn : 256 ≤ n) (hb : 2 ≤ b)
    (hm : 3 ≤ m) (hw : 1 ≤ width) :
    (1 : ℚ) / 2 ^ 96 < floorTerm n b m width := by
  have hmono : floorTerm 256 2 3 1 ≤ floorTerm n b m width := by
    have hw' : (1 : ℚ) ≤ width := by exact_mod_cast hw
    have hwidth : (0 : ℚ) ≤ (width : ℚ) - 2 / 3 := by linarith
    unfold floorTerm
    gcongr
  exact lt_of_lt_of_le favorable_floor_exceeds_96 hmono

private noncomputable def remark26Leading (n b m width : ℕ) : ℝ :=
  ((width : ℝ) - 2 / 3) * ((m : ℝ) + 1 / 2) ^ 7 / 3 *
    (b : ℝ) ^ 3 * Real.sqrt b * (n : ℝ) ^ 2 /
    (2147483647 : ℝ) ^ 4

theorem remark26_leading_exceeds_96_of_at_least_256
    {n b m width : ℕ} (hn : 256 ≤ n) (hb : 2 ≤ b)
    (hm : 3 ≤ m) (hw : 1 ≤ width) :
    (1 : ℝ) / 2 ^ 96 < remark26Leading n b m width := by
  have hsqrt : (1 : ℝ) ≤ Real.sqrt b := by
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast (by omega : 1 ≤ b)
    simpa using Real.sqrt_le_sqrt hb'
  have hw' : (1 : ℝ) ≤ width := by exact_mod_cast hw
  have hwidth : (0 : ℝ) ≤ (width : ℝ) - 2 / 3 := by linarith
  have hbase : (1 : ℝ) / 2 ^ 96 <
      ((1 : ℝ) - 2 / 3) * ((3 : ℝ) + 1 / 2) ^ 7 / 3 *
        (2 : ℝ) ^ 3 * (1 : ℝ) * (256 : ℝ) ^ 2 /
        (2147483647 : ℝ) ^ 4 := by norm_num
  have hmono :
      ((1 : ℝ) - 2 / 3) * ((3 : ℝ) + 1 / 2) ^ 7 / 3 *
        (2 : ℝ) ^ 3 * (1 : ℝ) * (256 : ℝ) ^ 2 /
        (2147483647 : ℝ) ^ 4 ≤ remark26Leading n b m width := by
    unfold remark26Leading
    gcongr
    · exact_mod_cast hm
    · exact_mod_cast hb
    · exact_mod_cast hn
  exact lt_of_lt_of_le hbase hmono

end S31.PcsFri.ConservativeEnvelope
