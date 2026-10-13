import S31.Gadgets.PcsFri.GuardedCircleImage
import Mathlib.Tactic

namespace S31.Gadgets.PcsFri.OodGuardFieldCount

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048

open OodRationalMap ConcreteCircleCount NativeTowerFormulas

abbrev CM31 := ConcreteCircleCount.CM31
abbrev QM31 := ConcreteCircleCount.QM31

theorem qm_mul_c0 (z w : QM31) :
    (z * w).c0 = z.c0 * w.c0 + (r : CM31) * z.c1 * w.c1 := by
  change ((QM31FieldInstance.toQuadratic.symm
      (QM31FieldInstance.toQuadratic z * QM31FieldInstance.toQuadratic w))).c0 = _
  ext
  all_goals
    dsimp [QM31FieldInstance.toQuadratic]
    simp [CM31FieldInstance.mul_eq_cmMul, CM31FieldInstance.add_eq_cmAdd,
      cmMul, cmAdd, r, Air.QuadField.twoPlusI]
    ring

theorem qm_mul_c1 (z w : QM31) :
    (z * w).c1 = z.c0 * w.c1 + z.c1 * w.c0 := by
  change ((QM31FieldInstance.toQuadratic.symm
      (QM31FieldInstance.toQuadratic z * QM31FieldInstance.toQuadratic w))).c1 = _
  ext
  all_goals
    dsimp [QM31FieldInstance.toQuadratic]
    simp [CM31FieldInstance.mul_eq_cmMul, CM31FieldInstance.add_eq_cmAdd,
      cmMul, cmAdd]
    ring

noncomputable def normQ (z : QM31) : CM31 :=
  z.c0 ^ 2 - (r : CM31) * z.c1 ^ 2

noncomputable def inverseQ (z : QM31) : QM31 :=
  ⟨z.c0 * (normQ z)⁻¹, -z.c1 * (normQ z)⁻¹⟩

theorem inverseQ_mul (z : QM31) (hn : normQ z ≠ 0) :
    z * inverseQ z = 1 := by
  rw [QM31FieldInstance.one_eq_qmOne]
  apply QM.ext
  · rw [qm_mul_c0]
    change z.c0 * (z.c0 * (normQ z)⁻¹) +
      (r : CM31) * z.c1 * (-z.c1 * (normQ z)⁻¹) = 1
    dsimp [normQ] at hn ⊢
    field_simp [hn]
    ring
  · rw [qm_mul_c1]
    change z.c0 * (-z.c1 * (normQ z)⁻¹) +
      z.c1 * (z.c0 * (normQ z)⁻¹) = 0
    ring

theorem inverseQ_eq_inv (z : QM31) (hn : normQ z ≠ 0) :
    inverseQ z = z⁻¹ := by
  have hm := inverseQ_mul z hn
  have hz : z ≠ 0 := by
    intro h
    rw [h, zero_mul] at hm
    exact zero_ne_one hm
  calc
    inverseQ z = 1 * inverseQ z := by ring
    _ = (z⁻¹ * z) * inverseQ z := by rw [inv_mul_cancel₀ hz]
    _ = z⁻¹ := by rw [mul_assoc, hm, mul_one]

theorem qm_zero_eq : (0 : QM31) = ⟨0, 0⟩ := by
  change QM31FieldInstance.toQuadratic.symm 0 = _
  rfl

theorem normQ_ne_zero (z : QM31) (hz : z ≠ 0) : normQ z ≠ 0 := by
  apply NativeTowerInverse.norm_ne_zero (r : CM31)
    CM31FieldInstance.r_nonsquare (QM31FieldInstance.toPair z)
  by_contra h
  push Not at h
  exact hz (by
    rw [qm_zero_eq]
    exact QM.ext h.1 h.2)

theorem denominator_c0 (a b : CM31) :
    (1 + (⟨a, b⟩ : QM31) ^ 2).c0 =
      1 + a ^ 2 + (r : CM31) * b ^ 2 := by
  have hs := congrArg PairedTowerCircle.Pair.c0
    (QM31FieldInstance.toPair_square (⟨a, b⟩ : QM31))
  have hs0 : ((⟨a, b⟩ : QM31) ^ 2).c0 =
      a ^ 2 + (r : CM31) * b ^ 2 := by
    simpa [QM31FieldInstance.toPair, PairedTowerCircle.square] using hs
  rw [QM31FieldInstance.add_eq_qmAdd,
    QM31FieldInstance.one_eq_qmOne]
  change cmAdd 1 ((⟨a, b⟩ : QM31) ^ 2).c0 = _
  rw [← CM31FieldInstance.add_eq_cmAdd, hs0]
  ring

theorem denominator_c1 (a b : CM31) :
    (1 + (⟨a, b⟩ : QM31) ^ 2).c1 = 2 * a * b := by
  have hs := congrArg PairedTowerCircle.Pair.c1
    (QM31FieldInstance.toPair_square (⟨a, b⟩ : QM31))
  have hs1 : ((⟨a, b⟩ : QM31) ^ 2).c1 = 2 * a * b := by
    simpa [QM31FieldInstance.toPair, PairedTowerCircle.square] using hs
  rw [QM31FieldInstance.add_eq_qmAdd,
    QM31FieldInstance.one_eq_qmOne]
  change cmAdd 0 ((⟨a, b⟩ : QM31) ^ 2).c1 = _
  rw [← CM31FieldInstance.add_eq_cmAdd, hs1]
  ring

theorem denominatorNorm_eq_normQ (a b : CM31) :
    OodGuardFiniteCount.denominatorNorm (r : CM31) a b =
      normQ (1 + (⟨a, b⟩ : QM31) ^ 2) := by
  rw [normQ, denominator_c0, denominator_c1]
  rfl

theorem regular_iff_denominatorNorm (a b : CM31) :
    regular (⟨a, b⟩ : QM31) ↔
      OodGuardFiniteCount.denominatorNorm (r : CM31) a b ≠ 0 := by
  rw [regular, denominatorNorm_eq_normQ]
  constructor
  · exact normQ_ne_zero _
  · intro hn hz
    apply hn
    rw [hz]
    simp [normQ, qm_zero_eq]

theorem double_c0 (a b : CM31) :
    (2 * (⟨a, b⟩ : QM31)).c0 = 2 * a := by
  rw [two_mul, QM31FieldInstance.add_eq_qmAdd]
  change cmAdd a a = 2 * a
  rw [← CM31FieldInstance.add_eq_cmAdd]
  ring

theorem double_c1 (a b : CM31) :
    (2 * (⟨a, b⟩ : QM31)).c1 = 2 * b := by
  rw [two_mul, QM31FieldInstance.add_eq_qmAdd]
  change cmAdd b b = 2 * b
  rw [← CM31FieldInstance.add_eq_cmAdd]
  ring

/-- The counted upper-coordinate rational formula is exactly the upper
coefficient of the actual modeled QM31 field division. -/
theorem y_upper_eq_field (a b : CM31)
    (hreg : regular (⟨a, b⟩ : QM31)) :
    (y (⟨a, b⟩ : QM31)).c1 =
      OodGuardFiniteCount.yUpper (r : CM31) a b := by
  let z : QM31 := ⟨a, b⟩
  let d : QM31 := 1 + z ^ 2
  have hn : normQ d ≠ 0 := normQ_ne_zero d hreg
  have hden : OodGuardFiniteCount.denominatorNorm (r : CM31) a b ≠ 0 :=
    (regular_iff_denominatorNorm a b).mp hreg
  have hm : ((2 : QM31) * z).c0 = 2 * a := double_c0 a b
  have hu : ((2 : QM31) * z).c1 = 2 * b := double_c1 a b
  have hd0 : d.c0 = 1 + a ^ 2 + (r : CM31) * b ^ 2 :=
    denominator_c0 a b
  have hd1 : d.c1 = 2 * a * b := denominator_c1 a b
  unfold OodRationalMap.y
  rw [div_eq_mul_inv]
  rw [← inverseQ_eq_inv d hn]
  rw [qm_mul_c1]
  change ((2 : QM31) * z).c0 * (-d.c1 * (normQ d)⁻¹) +
    ((2 : QM31) * z).c1 * (d.c0 * (normQ d)⁻¹) = _
  rw [hm, hu, hd0, hd1]
  have hnorm : normQ d =
      OodGuardFiniteCount.denominatorNorm (r : CM31) a b :=
    (denominatorNorm_eq_normQ a b).symm
  rw [hnorm]
  unfold OodGuardFiniteCount.yUpper
  field_simp [hden]
  ring

/-- The generic counted pair guard and the concrete QM31 rational-map
guard are the same predicate under the field's two CM31 coordinates. -/
theorem accepted_guard_iff_field (z : CM31 × CM31) :
    z ∈ OodGuardFiniteCount.acceptedGuard (r : CM31) ↔
      regular (⟨z.1, z.2⟩ : QM31) ∧
        (y (⟨z.1, z.2⟩ : QM31)).c1 ≠ 0 := by
  rw [CM31FieldInstance.accepted_guard_iff_cm31]
  constructor
  · rintro ⟨hd, hy⟩
    have hr := (regular_iff_denominatorNorm z.1 z.2).mpr hd
    refine ⟨hr, ?_⟩
    rw [y_upper_eq_field z.1 z.2 hr]
    exact hy
  · rintro ⟨hr, hy⟩
    refine ⟨(regular_iff_denominatorNorm z.1 z.2).mp hr, ?_⟩
    rw [← y_upper_eq_field z.1 z.2 hr]
    exact hy

noncomputable instance : Fintype GuardedCircleImage.guardedSeed := by
  classical
  unfold GuardedCircleImage.guardedSeed
  infer_instance

noncomputable def guardedSeedEquivAccepted :
    GuardedCircleImage.guardedSeed ≃
      { z : CM31 × CM31 //
        z ∈ OodGuardFiniteCount.acceptedGuard (r : CM31) } := by
  apply Equiv.subtypeEquiv (qmEquiv S31.Field.F)
  intro t
  exact (accepted_guard_iff_field (t.c0, t.c1)).symm

/-- The previously counted generic guard is now connected to the concrete
QM31 field expression; this is a seed-set cardinality, with no distribution
claim about the native transcript. -/
theorem card_guarded_seed :
    Fintype.card GuardedCircleImage.guardedSeed =
      (2147483647 ^ 2 - 1) ^ 2 := by
  classical
  calc
    Fintype.card GuardedCircleImage.guardedSeed =
        Fintype.card { z : CM31 × CM31 //
          z ∈ OodGuardFiniteCount.acceptedGuard (r : CM31) } :=
      Fintype.card_congr guardedSeedEquivAccepted
    _ = (OodGuardFiniteCount.acceptedGuard (r : CM31)).card := by
      simp
    _ = (2147483647 ^ 2 - 1) ^ 2 :=
      CM31FieldInstance.accepted_guard_card_cm31

/-- Exact cardinality of the modeled successful OOD circle image. -/
theorem card_guarded_circle_image :
    (Set.range (fun t : GuardedCircleImage.guardedSeed =>
      (GuardedCircleImage.seedToGuardedCircle t).1)).ncard =
      (2147483647 ^ 2 - 1) ^ 2 := by
  rw [GuardedCircleImage.guarded_image_ncard,
    Nat.card_eq_fintype_card, card_guarded_seed]

/-- The guarded image is strictly smaller than the two-point universe by
exactly the size of the embedded lower-field circle. -/
theorem two_point_minus_guarded_image_card :
    (Set.range ConcreteCircleCount.lowerCircle)ᶜ.ncard -
      (Set.range (fun t : GuardedCircleImage.guardedSeed =>
        (GuardedCircleImage.seedToGuardedCircle t).1)).ncard =
      2147483647 ^ 2 - 1 := by
  rw [ConcreteCircleCount.two_point_universe_card,
    card_guarded_circle_image]
  norm_num

end S31.Gadgets.PcsFri.OodGuardFieldCount
