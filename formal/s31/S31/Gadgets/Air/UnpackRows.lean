import S31.Gadgets.Air.SimdChunks

namespace S31.Gadgets.Air.UnpackRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

/-- The exact one- or two-row schedule emitted by SIMD `unpackIdx`.
The first coordinate aliases the pointwise-mask output; other coordinates
multiply that output by the corresponding extension-basis inverse. -/
def acceptsUnpack (i : Fin 4) (input output : Quad) : Prop :=
  ∃ masked : Quad,
    accepts (encode .pointwiseMul) input (unit i) masked ∧
    (if i.val = 0 then output = masked else
      accepts (encode .mul) masked (unitInverse i) output)

theorem acceptsUnpack_iff (i : Fin 4) (input output : Quad) :
    acceptsUnpack i input output ↔ output = base (coord input i) := by
  constructor
  · rintro ⟨masked, hmask, hout⟩
    have hmask' := (accepts_encoded .pointwiseMul input (unit i) masked).mp hmask
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte] at hout
      rw [hout, hmask']
      fin_cases i <;> simp_all [evaluate, pointwise, unit, base, coord]
    · simp only [hi, ↓reduceIte] at hout
      have hout' := (accepts_encoded .mul masked (unitInverse i) output).mp hout
      calc
        output = Packed.mul masked (unitInverse i) := by simpa [evaluate] using hout'
        _ = Packed.mul (Packed.pointwise input (unit i)) (unitInverse i) := by
          rw [hmask']; rfl
        _ = base (coord input i) := unpack_coordinate input i
  · intro hout
    refine ⟨Packed.pointwise input (unit i), honest_row _ _ _, ?_⟩
    by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte]
      rw [hout]
      fin_cases i <;> simp_all [pointwise, unit, base, coord]
    · simp only [hi, ↓reduceIte]
      apply (accepts_encoded .mul _ _ _).mpr
      simpa [evaluate] using hout.trans (unpack_coordinate input i).symm

/-- A scalar row extracted from any packed source word is exactly its active
M31 coordinate, regardless of the unused source padding. -/
theorem packedUnpack_iff {n : Nat} (source : Fin n → S31.M31)
    (tail : Nat → Fin 4 → S31.M31)
    (block : Fin ((n + 3) / 4)) (i : Fin 4)
    (hi : block.val * 4 + i.val < n) (claimed : S31.M31) :
    acceptsUnpack i
      (packM31 (SimdChunks.chunk4 source block.val (tail block.val)))
      (base (S31.Field.toZMod claimed)) ↔
      claimed = source ⟨block.val * 4 + i.val, hi⟩ := by
  rw [acceptsUnpack_iff, coord_packM31]
  rw [SimdChunks.chunk4_active source block.val (tail block.val) i hi]
  constructor
  · intro h
    apply S31.Field.toZMod_injective
    exact congrArg Quad.a h
  · intro h
    rw [h]

theorem lane_two_honest :
    acceptsUnpack ⟨2, by decide⟩ ⟨8, 13, 21, 34⟩ (base 21) := by
  rw [acceptsUnpack_iff]
  rfl

theorem lane_two_forged_rejected :
    ¬ acceptsUnpack ⟨2, by decide⟩ ⟨8, 13, 21, 34⟩ (base 22) := by
  rw [acceptsUnpack_iff]
  intro h
  have hvalue := congrArg Quad.a h
  have hbad : (22 : F) = 21 := by simpa [base, coord] using hvalue
  exact (by decide : (22 : F) ≠ 21) hbad

end S31.Gadgets.Air.UnpackRows
