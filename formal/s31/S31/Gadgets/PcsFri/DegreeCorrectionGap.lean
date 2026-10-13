import Mathlib.Tactic

/-!
A deliberately small ordinary-polynomial model of the P05 logical gap.
It does not model circle polynomials, FRI, native execution, or an attack.
If a verifier checks only `q = (f-v)/(X-z)` against an original degree bound,
the quotient identity and that check alone do not imply the same bound on `f`.
This is why a native-to-paper degree-correction reduction is necessary.
-/

namespace S31.Gadgets.PcsFri.DegreeCorrectionGap

open Polynomial

/-- Any reconstructed polynomial agrees with its claimed value at the
sample point; this local OOD identity says nothing about its degree. -/
theorem reconstructed_sample (z v : ℚ) (q : Polynomial ℚ) :
    ((X - C z) * q + C v).eval z = v := by
  simp

/-- The toy quotient `X` satisfies the strict degree bound two. -/
theorem quotient_degree_below_two : (X : Polynomial ℚ).natDegree < 2 := by
  simp

/-- The corresponding original polynomial `X²` fails that same bound. -/
theorem original_degree_not_below_two :
    ¬ ((X : Polynomial ℚ) ^ 2).natDegree < 2 := by
  simp

/-- At sample point zero and claimed value zero, the quotient identity holds
while the original-degree conclusion fails. The native circle setting needs
its own relation and degree bounds; this theorem only refutes an inference. -/
theorem quotient_identity_and_degree_do_not_imply_original_degree :
    ∃ (f q : Polynomial ℚ),
      f = (X - C 0) * q + C 0 ∧
      f.eval 0 = 0 ∧
      q.natDegree < 2 ∧
      ¬ f.natDegree < 2 := by
  refine ⟨X ^ 2, X, ?_, ?_, quotient_degree_below_two,
    original_degree_not_below_two⟩
  · simp [pow_two]
  simp [pow_two]

end S31.Gadgets.PcsFri.DegreeCorrectionGap
