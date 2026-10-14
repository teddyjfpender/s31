import S31.Gadgets.PcsFri.CircleBasisDot
import S31.Gadgets.PcsFri.ConcreteCircleMinpoly

/-!
# M31 coefficient embedding for the circle-basis theorem

The Laurent construction needs `i² = -1`, so its coefficient field cannot be
the native M31 field. The concrete modeled instantiation is CM31. This file
embeds each native M31 coefficient as `(a,0)` in CM31, shows its subsequent
QM31 image is the native-shaped base-field value, and instantiates the full
mathematical basis-dot identity on such embedded coefficient lists. It does
not prove that Zig's FFT/array bytes or sampled-value loops realize them.
-/

namespace S31.Gadgets.PcsFri.CircleBasisM31Embedding

open NativeTowerFormulas

abbrev M31 := S31.Field.F
abbrev CM31 := ConcreteCircleMinpoly.CM31
abbrev QM31 := ConcreteCircleMinpoly.QM31

theorem m31_has_no_imaginary : ¬ ∃ i : M31, i ^ 2 = -1 := by
  rintro ⟨i, hi⟩
  have hs : IsSquare (-1 : M31) := ⟨i, by simpa [pow_two] using hi.symm⟩
  have hcard := FiniteField.isSquare_neg_one_iff.mp hs
  norm_num [M31] at hcard

noncomputable def m31ToCM31 : M31 →+* CM31 where
  toFun a := ⟨a, 0⟩
  map_zero' := by ext <;> rfl
  map_one' := by ext <;> rfl
  map_add' := by
    intro a b
    rw [CM31FieldInstance.add_eq_cmAdd]
    ext <;> simp [cmAdd]
  map_mul' := by
    intro a b
    rw [CM31FieldInstance.mul_eq_cmMul]
    ext <;> simp [cmMul]

/-- Native `QM31.fromBase(a)` has this exact modeled coordinate shape. -/
theorem m31ToQM31_eq_native_base (a : M31) :
    PairedBatchNativeRefinement.fromCM (m31ToCM31 a) = qmFromBase a := by
  rfl

theorem m31ToCM31_list_getD (coefficients : List M31) (j : Nat) :
    (coefficients.map m31ToCM31).getD j 0 =
      m31ToCM31 (coefficients.getD j 0) := by
  simpa [List.getD] using
    (Option.getD_map (m31ToCM31 : M31 → CM31) (0 : M31)
      (coefficients[j]?))

/-- The all-slot recursive/basis identity is genuinely instantiable by an
M31 source coefficient array after its explicit CM31 embedding. -/
theorem embedded_m31_recursiveValue_eq_basisDot
    (x y : QM31) (k : Nat) (coefficients : List M31) :
    CircleRecursiveBasisDegree.recursiveValue x y k
        (coefficients.map m31ToCM31) =
      CircleBasisDot.basisDot
        (CircleRecursiveBasisDegree.nativeFactorValue x y) k
        (fun j => m31ToCM31 (coefficients.getD j 0)) := by
  rw [CircleBasisDot.recursiveValue_eq_basisDot]
  congr 1
  funext j
  exact m31ToCM31_list_getD coefficients j

/-- In the concrete modeled CM31/QM31 tower, the full dot on an explicitly
embedded M31 word evaluates its bounded Laurent polynomial at any QM31
Fourier parameter. The native array-to-list and machine-operation refinements
remain separate obligations. -/
theorem embedded_m31_basisDot_eq_laurent
    (z : QM31ˣ) (k : Nat) (coefficients : List M31) :
    CircleBasisDot.basisDot
      (CircleRecursiveBasisDegree.nativeFactorValue
        (CircleLaurentDegree.fourierX z.val z⁻¹.val)
        (CircleLaurentDegree.fourierY
          ((algebraMap CM31 QM31) ConcreteCircleMinpoly.imaginary)
          z.val z⁻¹.val))
      k (fun j => m31ToCM31 (coefficients.getD j 0)) =
        LaurentPolynomial.eval₂ (algebraMap CM31 QM31) z
          (CircleRecursiveBasisDegree.coefficientWord
            ConcreteCircleMinpoly.imaginary k
            (coefficients.map m31ToCM31)) := by
  simpa only [m31ToCM31_list_getD] using
    (CircleBasisDot.basisDot_eq_coefficientWord_eval
      ConcreteCircleMinpoly.imaginary
      ConcreteCircleMinpoly.imaginary_square z k
      (coefficients.map m31ToCM31))

end S31.Gadgets.PcsFri.CircleBasisM31Embedding
