import S31.Gadgets.Air.QuadField
import S31.Gadgets.Air.Qm31Ops

namespace S31.Gadgets.Air.BitRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

/-- The `anchor + value = anchor` row used by `assertZeroArithmetic`. -/
def acceptsZero (value : Quad) : Prop :=
  ∃ anchor : Quad, accepts (encode .add) anchor value anchor

theorem toQM_add (x y : Quad) :
    QuadField.toQM (Packed.add x y) =
      QuadField.toQM x + QuadField.toQM y := by
  ext <;> rfl

theorem acceptsZero_iff (value : Quad) :
    acceptsZero value ↔ value = base 0 := by
  constructor
  · rintro ⟨anchor, h⟩
    have hrow := (accepts_encoded .add anchor value anchor).mp h
    have heq : QuadField.toQM anchor =
        QuadField.toQM anchor + QuadField.toQM value := by
      simpa [evaluate, toQM_add] using congrArg QuadField.toQM hrow
    have hz : QuadField.toQM value = 0 := by
      apply add_left_cancel (a := QuadField.toQM anchor)
      simpa using heq.symm
    exact QuadField.toQM_injective
      (by simpa [QuadField.toQM_base_zero] using hz)
  · rintro rfl
    refine ⟨base 0, ?_⟩
    simpa [evaluate, Packed.add, base] using
      (honest_row .add (base 0) (base 0))

/-- Ordinary `checkedBitWord` uses multiply, subtract, and a zero assertion.
The direct input path uses a separate self-loop handled in `SelectRows`. -/
def acceptsBit (wire : Quad) : Prop :=
  ∃ square difference : Quad,
    accepts (encode .mul) wire wire square ∧
    accepts (encode .sub) square wire difference ∧
    acceptsZero difference

theorem acceptsBit_iff (wire : Quad) :
    acceptsBit wire ↔ wire = base 0 ∨ wire = base 1 := by
  constructor
  · rintro ⟨square, difference, hs, hd, hz⟩
    have hs' := (accepts_encoded .mul wire wire square).mp hs
    have hd' := (accepts_encoded .sub square wire difference).mp hd
    have hz' := (acceptsZero_iff difference).mp hz
    rw [hd', hs'] at hz'
    have hself : Packed.mul wire wire = wire := by
      apply Quad.ext
      · have h := congrArg Quad.a hz'
        exact sub_eq_zero.mp (by simpa [evaluate, subtract, base] using h)
      · have h := congrArg Quad.b hz'
        exact sub_eq_zero.mp (by simpa [evaluate, subtract, base] using h)
      · have h := congrArg Quad.c hz'
        exact sub_eq_zero.mp (by simpa [evaluate, subtract, base] using h)
      · have h := congrArg Quad.d hz'
        exact sub_eq_zero.mp (by simpa [evaluate, subtract, base] using h)
    exact (QuadField.self_product_iff wire).mp hself
  · intro hbit
    let square := evaluate .mul wire wire
    let difference := evaluate .sub square wire
    refine ⟨square, difference, honest_row _ _ _, honest_row _ _ _, ?_⟩
    apply (acceptsZero_iff difference).mpr
    rcases hbit with hzero | hone
    · subst wire
      simp [difference, square, evaluate, Packed.mul, subtract, base]
    · subst wire
      simp [difference, square, evaluate, Packed.mul, subtract, base]

/-- The arithmetic check used for an ordinary scalar bit also canonicalizes
an arbitrary four-coordinate witness once its base coordinate is bound to a
source M31 value. -/
theorem acceptsBit_bound_iff (selector : S31.M31)
    (wire : Quad) (hcoord : wire.a = S31.Field.toZMod selector) :
    acceptsBit wire ↔
      wire = base (S31.Field.toZMod selector) ∧
        (selector = 0 ∨ selector = 1) := by
  rw [acceptsBit_iff]
  constructor
  · rintro (hzero | hone)
    · have hz : selector = 0 :=
        S31.Field.toZMod_injective
          (by simpa [hzero, base, S31.Field.toZMod_zero] using hcoord.symm)
      subst selector
      exact ⟨by simpa [S31.Field.toZMod_zero] using hzero,
        Or.inl rfl⟩
    · have ho : selector = 1 :=
        S31.Field.toZMod_injective
          (by simpa [hone, base, S31.Field.toZMod_one] using hcoord.symm)
      subst selector
      exact ⟨by simpa [S31.Field.toZMod_one] using hone,
        Or.inr rfl⟩
  · rintro ⟨hwire, hbit⟩
    rw [hwire]
    rcases hbit with hzero | hone
    · subst selector
      simp [S31.Field.toZMod_zero]
    · subst selector
      simp [S31.Field.toZMod_one]

theorem nonbit_two_rejected : ¬ acceptsBit (base 2) := by
  intro h
  rcases (acceptsBit_iff (base 2)).mp h with hzero | hone
  · exact (by decide : (base 2 : Quad) ≠ base 0) hzero
  · exact (by decide : (base 2 : Quad) ≠ base 1) hone

end S31.Gadgets.Air.BitRows
