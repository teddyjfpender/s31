import S31.Gadgets.PcsFri.PairedBatchNativeRefinement
import S31.Gadgets.PcsFri.GuardedCircleImage
import S31.Gadgets.PcsFri.CircleLaurentDegree
import Mathlib.Tactic

/-!
The guarded CAS05 OOD point lives in the concrete modeled QM31 quadratic
extension of CM31. This module removes the abstract degree-two minimal
polynomial premise from the circle quotient algebra for that point. It does
not interpret the native transcript or prove a PCS soundness bound.
-/

namespace S31.Gadgets.PcsFri.ConcreteCircleMinpoly

open NativeTowerFormulas
open PairedBatchNativeRefinement

abbrev CM31 := ConcreteCircleCount.CM31
abbrev QM31 := ConcreteCircleCount.QM31

noncomputable def cmToQm : CM31 →+* QM31 where
  toFun := fromCM
  map_zero' := fromCM_zero
  map_one' := fromCM_one
  map_add' := fromCM_add
  map_mul' := fromCM_mul

noncomputable instance : Algebra CM31 QM31 := RingHom.toAlgebra cmToQm

theorem algebra_map_eq (a : CM31) : algebraMap CM31 QM31 a = fromCM a := rfl

theorem outside_base_of_upper_ne_zero (z : QM31) (hz : z.c1 ≠ 0) :
    z ∉ Set.range (algebraMap CM31 QM31) := by
  rintro ⟨a, rfl⟩
  exact hz (by rfl)

noncomputable def normQ (z : QM31) : CM31 :=
  z.c0 ^ 2 - (r : CM31) * z.c1 ^ 2

noncomputable def quadratic (z : QM31) : Polynomial CM31 :=
  Polynomial.X ^ 2 - Polynomial.C (2 * z.c0) * Polynomial.X +
    Polynomial.C (normQ z)

theorem quadratic_monic (z : QM31) : (quadratic z).Monic := by
  unfold quadratic
  monicity!

theorem quadratic_natDegree (z : QM31) : (quadratic z).natDegree = 2 := by
  unfold quadratic
  compute_degree!

theorem quadratic_aeval (z : QM31) : (quadratic z).aeval z = 0 := by
  simp only [quadratic, map_add, map_sub, map_mul, map_pow,
    Polynomial.aeval_X, Polynomial.aeval_C]
  have hcore : z ^ 2 + fromCM (normQ z) = z * fromCM (2 * z.c0) := by
    rw [QM31FieldInstance.square_eq_qmSquare,
      ← nativeMulCM_eq_mul z (2 * z.c0),
      QM31FieldInstance.add_eq_qmAdd]
    apply QM.ext
    · change cmAdd (cmAdd (cmSquare z.c0) (cmMulByR (cmSquare z.c1)))
        (normQ z) = z.c0 * (2 * z.c0)
      rw [← CM31FieldInstance.add_eq_cmAdd,
        ← CM31FieldInstance.add_eq_cmAdd,
        ← CM31FieldInstance.square_eq_cmSquare,
        ← CM31FieldInstance.square_eq_cmSquare,
        cm_mul_by_r, ← CM31FieldInstance.mul_eq_cmMul]
      unfold normQ
      ring
    · change cmAdd (cmAdd (cmMul z.c0 z.c1) (cmMul z.c0 z.c1)) 0 =
        z.c1 * (2 * z.c0)
      rw [← CM31FieldInstance.add_eq_cmAdd,
        ← CM31FieldInstance.add_eq_cmAdd,
        ← CM31FieldInstance.mul_eq_cmMul]
      ring
  rw [← map_mul (algebraMap CM31 QM31)]
  change z ^ 2 - fromCM (2 * z.c0) * z + fromCM (normQ z) = 0
  rw [mul_comm (fromCM (2 * z.c0)) z]
  linear_combination hcore

theorem minpoly_degree_two_of_upper_ne_zero (z : QM31) (hz : z.c1 ≠ 0) :
    (minpoly CM31 z).natDegree = 2 := by
  have hle : (minpoly CM31 z).natDegree ≤ 2 := by
    rw [← quadratic_natDegree z]
    exact Polynomial.natDegree_le_of_dvd
      (minpoly.dvd CM31 z (quadratic_aeval z))
      (quadratic_monic z).ne_zero
  have hInt : IsIntegral CM31 z := ⟨quadratic z, quadratic_monic z,
    quadratic_aeval z⟩
  have hge : 2 ≤ (minpoly CM31 z).natDegree :=
    (minpoly.two_le_natDegree_iff hInt).2
      (outside_base_of_upper_ne_zero z hz)
  omega

theorem minpoly_monic_of_upper_ne_zero (z : QM31) (_hz : z.c1 ≠ 0) :
    (minpoly CM31 z).Monic := by
  exact minpoly.monic ⟨quadratic z, quadratic_monic z, quadratic_aeval z⟩

def imaginary : CM31 := ⟨0, 1⟩

theorem imaginary_square : imaginary ^ 2 = -1 :=
  CM31FieldInstance.imaginary_square

theorem embedded_imaginary_square : (fromCM imaginary) ^ 2 = -1 := by
  change (cmToQm imaginary) ^ 2 = -1
  rw [← map_pow, imaginary_square, map_neg, map_one]

theorem embedded_imaginary_ne_zero : fromCM imaginary ≠ 0 := by
  intro h
  have hs := embedded_imaginary_square
  rw [h, zero_pow (by omega : 2 ≠ 0)] at hs
  exact one_ne_zero (neg_eq_zero.mp hs.symm)

noncomputable def fourierParameter (x y : QM31) : QM31 :=
  x + y * fromCM imaginary

noncomputable def fourierConjugate (x y : QM31) : QM31 :=
  x - y * fromCM imaginary

theorem fourier_product (x y : QM31) (hcircle : x ^ 2 + y ^ 2 = 1) :
    fourierParameter x y * fourierConjugate x y = 1 := by
  unfold fourierParameter fourierConjugate
  calc
    (x + y * fromCM imaginary) * (x - y * fromCM imaginary) =
        x ^ 2 - y ^ 2 * (fromCM imaginary) ^ 2 := by ring
    _ = x ^ 2 + y ^ 2 := by rw [embedded_imaginary_square]; ring
    _ = 1 := hcircle

theorem fourier_inverse (x y : QM31) (hcircle : x ^ 2 + y ^ 2 = 1) :
    (fourierParameter x y)⁻¹ = fourierConjugate x y := by
  exact (eq_inv_of_mul_eq_one_right (fourier_product x y hcircle)).symm

theorem fourier_x_eq (x y : QM31) (hcircle : x ^ 2 + y ^ 2 = 1) :
    CircleLaurentDegree.fourierX
      (fourierParameter x y) (fourierParameter x y)⁻¹ = x := by
  rw [fourier_inverse x y hcircle]
  unfold CircleLaurentDegree.fourierX fourierParameter fourierConjugate
  field_simp
  ring

theorem fourier_y_eq (x y : QM31) (hcircle : x ^ 2 + y ^ 2 = 1) :
    CircleLaurentDegree.fourierY (fromCM imaginary)
      (fourierParameter x y) (fourierParameter x y)⁻¹ = y := by
  rw [fourier_inverse x y hcircle]
  unfold CircleLaurentDegree.fourierY fourierParameter fourierConjugate
  field_simp [embedded_imaginary_ne_zero]
  ring

theorem fourier_upper (x y : QM31) :
    (fourierParameter x y).c1 = x.c1 + y.c1 * imaginary := by
  unfold fourierParameter
  rw [← nativeMulCM_eq_mul y imaginary,
    QM31FieldInstance.add_eq_qmAdd]
  change cmAdd x.c1 (y.c1 * imaginary) = _
  rw [← CM31FieldInstance.add_eq_cmAdd]

/-- A point satisfying the concrete QM31 circle equation and CAS05's guard
cannot have its Fourier parameter in the CM31 subfield. -/
theorem fourier_upper_nonzero (x y : QM31)
    (hcircle : x ^ 2 + y ^ 2 = 1) (hguard : y.c1 ≠ 0) :
    (fourierParameter x y).c1 ≠ 0 := by
  have hpair : PairedTowerCircle.add
      (PairedTowerCircle.square (r : CM31) (QM31FieldInstance.toPair x))
      (PairedTowerCircle.square (r : CM31) (QM31FieldInstance.toPair y)) =
      PairedTowerCircle.one := by
    rw [← QM31FieldInstance.toPair_square,
      ← QM31FieldInstance.toPair_square,
      ← QM31FieldInstance.toPair_add,
      ← QM31FieldInstance.toPair_one, hcircle]
  obtain ⟨h0, h1⟩ := PairedTowerCircle.circle_coefficients
    (r : CM31) (QM31FieldInstance.toPair x)
    (QM31FieldInstance.toPair y) hpair
  dsimp [QM31FieldInstance.toPair] at h0 h1
  intro hz
  rw [fourier_upper] at hz
  have hx1 : x.c1 = -(y.c1 * imaginary) := by
    linear_combination hz
  have hy0 : y.c0 = imaginary * x.c0 := by
    rw [hx1] at h1
    have hmul : y.c1 * (y.c0 - imaginary * x.c0) = 0 := by
      linear_combination h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left hguard)
  rw [hx1, hy0] at h0
  have hzero : x.c0 ^ 2 + (imaginary * x.c0) ^ 2 +
      (r : CM31) * ((-(y.c1 * imaginary)) ^ 2 + y.c1 ^ 2) = 0 := by
    calc
      _ = (1 + imaginary ^ 2) * x.c0 ^ 2 +
          (r : CM31) * (1 + imaginary ^ 2) * y.c1 ^ 2 := by ring
      _ = 0 := by rw [imaginary_square]; ring
  exact zero_ne_one (hzero.symm.trans h0)

theorem guarded_fourier_minpoly_degree_two (x y : QM31)
    (hcircle : x ^ 2 + y ^ 2 = 1) (hguard : y.c1 ≠ 0) :
    (minpoly CM31 (fourierParameter x y)).natDegree = 2 :=
  minpoly_degree_two_of_upper_ne_zero _
    (fourier_upper_nonzero x y hcircle hguard)

theorem guarded_fourier_minpoly_monic (x y : QM31)
    (hcircle : x ^ 2 + y ^ 2 = 1) (hguard : y.c1 ≠ 0) :
    (minpoly CM31 (fourierParameter x y)).Monic :=
  minpoly_monic_of_upper_ne_zero _
    (fourier_upper_nonzero x y hcircle hguard)

end S31.Gadgets.PcsFri.ConcreteCircleMinpoly
