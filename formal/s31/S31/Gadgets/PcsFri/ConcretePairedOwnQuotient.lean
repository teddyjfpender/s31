import S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
import S31.Gadgets.PcsFri.ConcreteCircleMinpoly

/-!
Specialize the local four-block CAS05 quotient construction to the concrete
CM31/QM31 tower and a guarded circle point. The generic degree-two minimal
polynomial assumptions are derived from the guard instead of supplied by a
caller. This is an algebraic honest-oracle theorem, not a degree test on an
authenticated native proof.
-/

namespace S31.Gadgets.PcsFri.ConcretePairedOwnQuotient

open S31.Gadgets.PcsFri.NativeTowerFormulas
open S31.Gadgets.PcsFri.PairedBatchNativeRefinement
open S31.Gadgets.PcsFri.ConcreteCircleMinpoly
open S31.Gadgets.PcsFri.CanonicalCircleLaurentRows

abbrev CM31 := ConcreteCircleCount.CM31
abbrev QM31 := ConcreteCircleCount.QM31

noncomputable def upper : QM31 := ⟨0, 1⟩

theorem split_upper (v : QM31) :
    v = fromCM v.c0 + upper * fromCM v.c1 := by
  rw [← nativeMulCM_eq_mul upper v.c1, QM31FieldInstance.add_eq_qmAdd]
  apply QM.ext
  · change v.c0 = cmAdd v.c0 ((0 : CM31) * v.c1)
    rw [← CM31FieldInstance.add_eq_cmAdd]
    simp
  · change v.c1 = cmAdd (0 : CM31) ((1 : CM31) * v.c1)
    rw [← CM31FieldInstance.add_eq_cmAdd]
    simp

theorem fourier_nonzero (x y : QM31) (hcircle : x ^ 2 + y ^ 2 = 1) :
    fourierParameter x y ≠ 0 := by
  intro hz
  have h := fourier_product x y hcircle
  rw [hz] at h
  simp at h

/-- A guarded concrete QM31 OOD point and a matching four-block claim yield
an own quotient of Laurent radius one. No abstract minpoly premise remains. -/
theorem guarded_four_block_own_quotient
    (x y : QM31) (hcircle : x ^ 2 + y ^ 2 = 1)
    (hguard : y.c1 ≠ 0)
    (v₀ v₁ c₀ c₁ c₂ c₃ : CM31)
    (hclaim : nativeFourBlock
      (fromCM c₀) (fromCM c₁) (fromCM c₂) (fromCM c₃) x y =
        fromCM v₀ + upper * fromCM v₁) :
    ∃ q : CircleLaurentDegree.CirclePoly CM31,
      CircleLaurentDegree.InCircleBand 1 q ∧
      fourBlockLaurent imaginary c₀ c₁ c₂ c₃ =
        NativeCircleQuotientRows.interpolationLaurent imaginary v₀ v₁ y.c0 y.c1 +
          CircleLaurentDegree.nativeLineLaurent imaginary
            x.c0 y.c0 x.c1 y.c1 * q := by
  let z : QM31ˣ := Units.mk0 (fourierParameter x y)
    (fourier_nonzero x y hcircle)
  have hpair : PairedTowerCircle.add
      (PairedTowerCircle.square (r : CM31) (QM31FieldInstance.toPair x))
      (PairedTowerCircle.square (r : CM31) (QM31FieldInstance.toPair y)) =
      PairedTowerCircle.one := by
    rw [← QM31FieldInstance.toPair_square,
      ← QM31FieldInstance.toPair_square,
      ← QM31FieldInstance.toPair_add,
      ← QM31FieldInstance.toPair_one, hcircle]
  obtain ⟨h₀, h₁⟩ := PairedTowerCircle.circle_coefficients
    (r : CM31) (QM31FieldInstance.toPair x)
    (QM31FieldInstance.toPair y) hpair
  dsimp [QM31FieldInstance.toPair] at h₀ h₁
  have hx : CircleLaurentDegree.fourierX z.val z⁻¹.val =
      fromCM x.c0 + upper * fromCM x.c1 := by
    rw [Units.val_inv_eq_inv_val,
      show z.val = fourierParameter x y by rfl,
      fourier_x_eq x y hcircle]
    exact split_upper x
  have hy : CircleLaurentDegree.fourierY (fromCM imaginary)
      z.val z⁻¹.val = fromCM y.c0 + upper * fromCM y.c1 := by
    rw [Units.val_inv_eq_inv_val,
      show z.val = fourierParameter x y by rfl,
      fourier_y_eq x y hcircle]
    exact split_upper y
  have hc : nativeFourBlock
      (fromCM c₀) (fromCM c₁) (fromCM c₂) (fromCM c₃)
      (CircleLaurentDegree.fourierX z.val z⁻¹.val)
      (CircleLaurentDegree.fourierY (fromCM imaginary) z.val z⁻¹.val) =
        fromCM v₀ + upper * fromCM v₁ := by
    rw [Units.val_inv_eq_inv_val,
      show z.val = fourierParameter x y by rfl,
      fourier_x_eq x y hcircle,
      fourier_y_eq x y hcircle]
    exact hclaim
  exact four_block_native_claim_constructs_own_quotient z
    (r : CM31) imaginary x.c0 y.c0 x.c1 y.c1 v₀ v₁ c₀ c₁ c₂ c₃
    imaginary_square h₀ h₁ hguard
    (guarded_fourier_minpoly_monic x y hcircle hguard)
    (guarded_fourier_minpoly_degree_two x y hcircle hguard)
    upper hx hy hc

end S31.Gadgets.PcsFri.ConcretePairedOwnQuotient
