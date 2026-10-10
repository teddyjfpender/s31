import S31.Gadgets.Air.NativeLogUpBatches

namespace S31.Gadgets.Air.NativeLogUpBatchesProof
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.LogUpInteraction
open S31.Gadgets.Air.NativeLogUpBatches

/-- Four OODS coordinate samples reassemble in the QM31 basis. -/
def decode (limbs : Fin 4 → GateSecure) : GateSecure :=
  limbs 0 + limbs 1 * basisI + limbs 2 * basisU + limbs 3 * basisIU

/-- Symbolic execution of `finalizeLogupInPairs` with a zero initial
accumulator on three ordered terms
produces precisely a paired prefix residual followed by a singleton final
residual, folded with the verifier's composition coefficient. -/
theorem native_three_term_accumulator_eq
    (a b c : Term GateSecure)
    (first prev last : Fin 4 → GateSecure)
    (rho claimed nInstances : GateSecure) :
    threeTermAccumulator a b c first prev last rho claimed nInstances =
      rho * pairResidual a b (decode first) +
        singleResidual c
          (decode last - decode prev - decode first +
            claimed / nInstances) := by
  simp only [threeTermAccumulator, decode, pairResidual,
    singleResidual, div_eq_mul_inv]
  ring

/-- With an arbitrary preceding accumulator, the production finalizer
appends the pair and singleton in Horner order. In the full arithmetic
component, `prefix` is the fold of its nine local residuals. -/
theorem native_three_term_with_prefix_eq
    (prior : GateSecure) (a b c : Term GateSecure)
    (first prev last : Fin 4 → GateSecure)
    (rho claimed nInstances : GateSecure) :
    threeTermWithPrefix prior a b c first prev last rho claimed nInstances =
      rho ^ 2 * prior + rho * pairResidual a b (decode first) +
        singleResidual c
          (decode last - decode prev - decode first +
            claimed / nInstances) := by
  simp only [threeTermWithPrefix, decode, pairResidual,
    singleResidual, div_eq_mul_inv]
  ring

/-- `assert_eq` supplies two Gate reads, so the native finalizer emits one
paired final-column residual after the existing component accumulator. -/
theorem native_two_term_with_prefix_eq
    (prior : GateSecure) (a b : Term GateSecure)
    (prev last : Fin 4 → GateSecure)
    (rho claimed nInstances : GateSecure) :
    twoTermWithPrefix prior a b prev last rho claimed nInstances =
      rho * prior +
        pairResidual a b (decode last - decode prev +
          claimed / nInstances) := by
  simp only [twoTermWithPrefix, decode, pairResidual, div_eq_mul_inv]
  ring

/-- At fixed term and column samples, a folded zero at two distinct
composition coefficients forces both source-extracted residuals to zero. -/
theorem two_coefficients_force_both_residuals
    (a b c : Term GateSecure)
    (first prev last : Fin 4 → GateSecure)
    (rho₁ rho₂ claimed nInstances : GateSecure)
    (hne : rho₁ ≠ rho₂)
    (h₁ : threeTermAccumulator a b c first prev last
      rho₁ claimed nInstances = 0)
    (h₂ : threeTermAccumulator a b c first prev last
      rho₂ claimed nInstances = 0) :
    pairResidual a b (decode first) = 0 ∧
      singleResidual c
        (decode last - decode prev - decode first +
          claimed / nInstances) = 0 := by
  rw [native_three_term_accumulator_eq] at h₁ h₂
  have hproduct : (rho₁ - rho₂) * pairResidual a b (decode first) = 0 := by
    linear_combination h₁ - h₂
  have hpair : pairResidual a b (decode first) = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr hne)
  constructor
  · exact hpair
  · rw [hpair] at h₁
    simpa using h₁

end S31.Gadgets.Air.NativeLogUpBatchesProof
