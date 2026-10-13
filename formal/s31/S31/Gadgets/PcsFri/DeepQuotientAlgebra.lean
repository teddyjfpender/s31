import Mathlib.Tactic

/-!
Local algebra for the native DEEP row quotient. `complexConjugateLineCoeffs`
constructs a weighted line through a sampled value and its conjugate;
`finalizeRowQuotients` subtracts that line from a queried column value and
multiplies by an inverse circle denominator. These lemmas identify the exact
field identities needed for that calculation. They do not prove that native
Zig execution implements the model, that opened columns are committed, or
that the resulting quotient has the degree required by a PCS theorem.
-/

namespace S31.Gadgets.PcsFri.DeepQuotientAlgebra

variable {F : Type*} [Field F]

structure LineCoeffs (F : Type*) where
  a : F
  b : F
  c : F

def conjugateLineCoeffs (sampleY conjugateY sampleValue conjugateValue alpha : F) :
    LineCoeffs F :=
  let a := conjugateValue - sampleValue
  let c := conjugateY - sampleY
  { a := alpha * a
    b := alpha * (sampleValue * c - a * sampleY)
    c := alpha * c }

def lineResidual (coeffs : LineCoeffs F) (y value : F) : F :=
  coeffs.c * value - (coeffs.a * y + coeffs.b)

/-- The native weighted line has zero residual at the supplied sample. -/
theorem lineResidual_sample (sampleY conjugateY sampleValue conjugateValue alpha : F) :
    lineResidual (conjugateLineCoeffs sampleY conjugateY sampleValue
      conjugateValue alpha) sampleY sampleValue = 0 := by
  simp [lineResidual, conjugateLineCoeffs]
  ring

/-- The same line has zero residual at the conjugate sample. -/
theorem lineResidual_conjugate (sampleY conjugateY sampleValue conjugateValue alpha : F) :
    lineResidual (conjugateLineCoeffs sampleY conjugateY sampleValue
      conjugateValue alpha) conjugateY conjugateValue = 0 := by
  simp [lineResidual, conjugateLineCoeffs]
  ring

/-- The scalar denominator expansion used by the reusable native workspace. -/
theorem circleDenominator_expanded (prx pry pix piy x y : F) :
    (prx - x) * piy - (pry - y) * pix =
      (prx * piy - pry * pix) - x * piy + y * pix := by
  ring

def flatBatchNumerator {ι : Type*} (columns : Finset ι)
    (coeffs : ι → LineCoeffs F) (values : ι → F) (y : F) : F :=
  ∑ i ∈ columns, lineResidual (coeffs i) y (values i)

def nativeBatchNumerator {ι : Type*} (columns : Finset ι)
    (coeffs : ι → LineCoeffs F) (values : ι → F) (y : F) : F :=
  (∑ i ∈ columns, (coeffs i).c * values i) -
    ((∑ i ∈ columns, (coeffs i).a) * y +
      (∑ i ∈ columns, (coeffs i).b))

/-- Moving the row-independent linear coefficients outside the column loop
preserves the sum of every per-column line residual. -/
theorem nativeBatchNumerator_eq_flat {ι : Type*} (columns : Finset ι)
    (coeffs : ι → LineCoeffs F) (values : ι → F) (y : F) :
    nativeBatchNumerator columns coeffs values y =
      flatBatchNumerator columns coeffs values y := by
  classical
  simp only [nativeBatchNumerator, flatBatchNumerator, lineResidual,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]

/-- A nonzero circle denominator makes the batch quotient an actual quotient
of the line-residual sum. A zero denominator is an explicit failure case. -/
theorem batchQuotient_cross_mul {ι : Type*} (columns : Finset ι)
    (coeffs : ι → LineCoeffs F) (values : ι → F) (y denominator : F)
    (hden : denominator ≠ 0) :
    (nativeBatchNumerator columns coeffs values y * denominator⁻¹) * denominator =
      flatBatchNumerator columns coeffs values y := by
  rw [nativeBatchNumerator_eq_flat]
  field_simp [hden]

end S31.Gadgets.PcsFri.DeepQuotientAlgebra
