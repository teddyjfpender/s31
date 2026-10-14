import S31.Gadgets.PcsFri.CircleBasisM31Embedding

/-!
# Sixteen-cell circle basis for accepted source height five

This finite specialization unrolls the native low-block predecessor schedule
of `fillSubsetProductBasis` at coefficient log four. It relates every indexed
cell to `CircleBasisDot.basisWeight`. The source-bound Zig fixture separately
checks the native bit-clear/trailing-zero predecessor choices and optimized
field arithmetic. The theorem does not refine a runtime packed path.
-/

namespace S31.Gadgets.PcsFri.CircleH5BasisCells

open CircleBasisDot

variable {E : Type*} [Field E]

/-- The 16 writes of the native low-block fill, unrolled in index order.
For each positive index the expression uses the earlier cell obtained by
clearing its least-significant set bit, multiplied by that bit's factor. -/
def low4Cells (factor : Nat → E) : Array E :=
  #[1,
    factor 0,
    factor 1,
    factor 1 * factor 0,
    factor 2,
    factor 2 * factor 0,
    factor 2 * factor 1,
    (factor 2 * factor 1) * factor 0,
    factor 3,
    factor 3 * factor 0,
    factor 3 * factor 1,
    (factor 3 * factor 1) * factor 0,
    factor 3 * factor 2,
    (factor 3 * factor 2) * factor 0,
    (factor 3 * factor 2) * factor 1,
    ((factor 3 * factor 2) * factor 1) * factor 0]

def previousIndex : Array Nat :=
  #[0, 0, 0, 2, 0, 4, 4, 6, 0, 8, 8, 10, 8, 12, 12, 14]

def factorIndex : Array Nat :=
  #[0, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0]

theorem previousIndex_size : previousIndex.size = 16 := rfl
theorem factorIndex_size : factorIndex.size = 16 := rfl

theorem previousIndex_lt (j : Fin 16) (hj : j.val ≠ 0) :
    previousIndex[j] < j.val := by
  fin_cases j <;> simp_all [previousIndex]

/-- Every nonconstant cell is exactly the native bit-clearing recurrence
using a previously materialized cell. The Zig fixture independently checks
that `index & (index - 1)` and `ctz(index)` compute these two tables. -/
theorem low4Cells_recurrence (factor : Nat → E) (j : Fin 16)
    (hj : j.val ≠ 0) :
    (low4Cells factor)[j] =
      (low4Cells factor).getD previousIndex[j] 0 * factor factorIndex[j] := by
  fin_cases j <;> simp_all [low4Cells, previousIndex, factorIndex]

theorem low4Cells_size (factor : Nat → E) : (low4Cells factor).size = 16 := rfl

/-- Every in-range native low-block cell has the subset-product weight for
its exact array index; there is no zero padding or omitted high coefficient. -/
theorem low4Cells_index (factor : Nat → E) (j : Fin 16) :
    (low4Cells factor)[j] = basisWeight factor 4 j.val := by
  fin_cases j <;> simp [low4Cells, basisWeight] <;> ring

/-- The native scalar tail reduces four coefficient products at a time.
This is the algebraic value of one such group; the Zig fixture checks the
optimized packed `dot4` implementation against direct QM31 multiplication. -/
def block4 (factor : Nat → E) (coefficient : Nat → E) (start : Nat) : E :=
  ∑ t ∈ Finset.range 4,
    coefficient (start + t) * (low4Cells factor).getD (start + t) 0

/-- Four sequential `dot4` groups cover exactly the 16 coefficient slots. -/
def fourBlockAccumulation (factor : Nat → E) (coefficient : Nat → E) : E :=
  ((block4 factor coefficient 0 + block4 factor coefficient 4) +
    block4 factor coefficient 8) + block4 factor coefficient 12

theorem fourBlockAccumulation_eq_basisDot
    {F : Type*} [Field F] [Algebra F E]
    (factor : Nat → E) (coefficient : Nat → F) :
    fourBlockAccumulation factor (fun j => (algebraMap F E) (coefficient j)) =
      basisDot factor 4 coefficient := by
  simp [fourBlockAccumulation, block4, basisDot, Finset.sum_range_succ,
    low4Cells, basisWeight]
  ring

/-- With 16 native M31 coefficient slots embedded into CM31, the four
source-height-five scalar groups evaluate the exact bounded Laurent word.
The source coefficients and the Fourier factors still need native provenance. -/
theorem h5_m31_fourBlock_equals_laurent
    (z : CircleBasisM31Embedding.QM31ˣ)
    (coefficients : List CircleBasisM31Embedding.M31) :
    let factors := CircleRecursiveBasisDegree.nativeFactorValue
      (CircleLaurentDegree.fourierX z.val z⁻¹.val)
      (CircleLaurentDegree.fourierY
        ((algebraMap CircleBasisM31Embedding.CM31 CircleBasisM31Embedding.QM31)
          ConcreteCircleMinpoly.imaginary) z.val z⁻¹.val)
    fourBlockAccumulation factors
      (fun j => (algebraMap CircleBasisM31Embedding.CM31
        CircleBasisM31Embedding.QM31)
        (CircleBasisM31Embedding.m31ToCM31 (coefficients.getD j 0))) =
      LaurentPolynomial.eval₂
        (algebraMap CircleBasisM31Embedding.CM31 CircleBasisM31Embedding.QM31)
        z (CircleRecursiveBasisDegree.coefficientWord
          ConcreteCircleMinpoly.imaginary 4
          (coefficients.map CircleBasisM31Embedding.m31ToCM31)) := by
  dsimp
  calc
    _ = basisDot
      (CircleRecursiveBasisDegree.nativeFactorValue
        (CircleLaurentDegree.fourierX z.val z⁻¹.val)
        (CircleLaurentDegree.fourierY
          ((algebraMap CircleBasisM31Embedding.CM31 CircleBasisM31Embedding.QM31)
            ConcreteCircleMinpoly.imaginary) z.val z⁻¹.val))
      4 (fun j => CircleBasisM31Embedding.m31ToCM31 (coefficients.getD j 0)) :=
        fourBlockAccumulation_eq_basisDot _ _
    _ = _ := CircleBasisM31Embedding.embedded_m31_basisDot_eq_laurent
      z 4 coefficients

theorem sixteenSlotWord_length
    (coefficients : Fin 16 → CircleBasisM31Embedding.M31) :
    (List.ofFn coefficients).length = 16 := by simp

/-- A length-indexed native coefficient word has all 16 slots present.
This instantiates the four-group identity without zero-padded list tails. -/
theorem h5_sixteenSlotWord_equals_laurent
    (z : CircleBasisM31Embedding.QM31ˣ)
    (coefficients : Fin 16 → CircleBasisM31Embedding.M31) :
    let word := List.ofFn coefficients
    let factors := CircleRecursiveBasisDegree.nativeFactorValue
      (CircleLaurentDegree.fourierX z.val z⁻¹.val)
      (CircleLaurentDegree.fourierY
        ((algebraMap CircleBasisM31Embedding.CM31 CircleBasisM31Embedding.QM31)
          ConcreteCircleMinpoly.imaginary) z.val z⁻¹.val)
    fourBlockAccumulation factors
      (fun j => (algebraMap CircleBasisM31Embedding.CM31
        CircleBasisM31Embedding.QM31)
        (CircleBasisM31Embedding.m31ToCM31 (word.getD j 0))) =
      LaurentPolynomial.eval₂
        (algebraMap CircleBasisM31Embedding.CM31 CircleBasisM31Embedding.QM31)
        z (CircleRecursiveBasisDegree.coefficientWord
          ConcreteCircleMinpoly.imaginary 4
          (word.map CircleBasisM31Embedding.m31ToCM31)) := by
  exact h5_m31_fourBlock_equals_laurent z (List.ofFn coefficients)

end S31.Gadgets.PcsFri.CircleH5BasisCells
