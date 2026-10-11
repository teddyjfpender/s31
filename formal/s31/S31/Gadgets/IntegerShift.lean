import S31.Gadgets.IntegerBits

/-!
Width-generic pointwise model for S31's static integer shifts and rotations.
Each output bit is wired to a proved input bit, zero, or the proved sign bit.
Packing the output words and correspondence to production Zig are separate
obligations; these theorems establish the exact bit-vector meaning of the
local wiring relation.
-/

namespace S31.Gadgets.IntegerShift

abbrev flag (b : Bool) : Field.F := Gadgets.encodeBool b

private theorem flag_injective : Function.Injective flag := by
  intro a b h
  cases a <;> cases b <;> simp_all [flag, Gadgets.encodeBool]

private theorem decode_ones (count : Nat) :
    Words.decode 2 (List.replicate count 1) = 2 ^ count - 1 := by
  induction count with
  | zero => simp [Words.decode]
  | succ count ih =>
    simp only [List.replicate_succ, Words.decode, ih, pow_succ]
    have positive : 0 < 2 ^ count := by positivity
    omega

/-- A sign-fill byte or limb packs to exactly 255·sign or 65535·sign. -/
theorem repeated_fill_pack (count : Nat) (sign : Bool) :
    Words.decode 2 (List.replicate count (if sign then 1 else 0)) =
      (2 ^ count - 1) * (if sign then 1 else 0) := by
  cases sign
  · simp [Radix.decode_zeros]
  · simpa using decode_ones count

def shlConstraint {width : Nat} (a y : BitVec width) (count : Nat) : Prop :=
  ∀ i, i < width → flag (y.getLsbD i) =
    flag ((!decide (i < count)) && a.getLsbD (i - count))

def shrLogicalConstraint {width : Nat} (a y : BitVec width) (count : Nat) : Prop :=
  ∀ i, i < width → flag (y.getLsbD i) = flag (a.getLsbD (count + i))

def shrArithmeticConstraint {width : Nat} (a y : BitVec width) (count : Nat) : Prop :=
  ∀ i, i < width → flag (y.getLsbD i) =
    flag (if count + i < width then a.getLsbD (count + i) else a.msb)

def rotlIndex (width count i : Nat) : Nat :=
  if i < count % width then width - count % width + i else i - count % width

def rotrIndex (width count i : Nat) : Nat :=
  if i < width - count % width then count % width + i else i - (width - count % width)

def rotlConstraint {width : Nat} (a y : BitVec width) (count : Nat) : Prop :=
  ∀ i, i < width → flag (y.getLsbD i) = flag (a.getLsbD (rotlIndex width count i))

def rotrConstraint {width : Nat} (a y : BitVec width) (count : Nat) : Prop :=
  ∀ i, i < width → flag (y.getLsbD i) = flag (a.getLsbD (rotrIndex width count i))

theorem shl_sound_complete {width : Nat} (a y : BitVec width) (count : Nat) :
    shlConstraint a y count ↔ y = a <<< count := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simpa [BitVec.getLsbD_shiftLeft, hi] using flag_injective (h i hi)
  · rintro rfl i hi
    simp [BitVec.getLsbD_shiftLeft, hi, ← BitVec.getLsbD_eq_getElem]

theorem shr_logical_sound_complete {width : Nat} (a y : BitVec width) (count : Nat) :
    shrLogicalConstraint a y count ↔ y = a >>> count := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simpa [BitVec.getLsbD_ushiftRight] using flag_injective (h i hi)
  · rintro rfl i hi
    simp [BitVec.getLsbD_ushiftRight]

theorem shr_arithmetic_sound_complete {width : Nat} (a y : BitVec width) (count : Nat) :
    shrArithmeticConstraint a y count ↔ y = a.sshiftRight count := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hnot : ¬ width ≤ i := Nat.not_le_of_gt hi
    simpa [BitVec.getLsbD_sshiftRight, hnot, ← BitVec.getLsbD_eq_getElem]
      using flag_injective (h i hi)
  · rintro rfl i hi
    have hnot : ¬ width ≤ i := Nat.not_le_of_gt hi
    simp [BitVec.getLsbD_sshiftRight, hnot, ← BitVec.getLsbD_eq_getElem]

theorem rotl_sound_complete {width : Nat} (a y : BitVec width) (count : Nat) :
    rotlConstraint a y count ↔ y = a.rotateLeft count := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    apply flag_injective
    by_cases route : i < count % width <;>
      simpa [BitVec.getLsbD_rotateLeft, rotlIndex, hi, Bool.cond_eq_ite, route]
        using h i hi
  · rintro rfl i hi
    by_cases route : i < count % width <;>
      simp [BitVec.getLsbD_rotateLeft, rotlIndex, hi, Bool.cond_eq_ite, route,
        ← BitVec.getLsbD_eq_getElem]

theorem rotr_sound_complete {width : Nat} (a y : BitVec width) (count : Nat) :
    rotrConstraint a y count ↔ y = a.rotateRight count := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    apply flag_injective
    by_cases route : i < width - count % width <;>
      simpa [BitVec.getLsbD_rotateRight, rotrIndex, hi, Bool.cond_eq_ite, route]
        using h i hi
  · rintro rfl i hi
    by_cases route : i < width - count % width <;>
      simp [BitVec.getLsbD_rotateRight, rotrIndex, hi, Bool.cond_eq_ite, route,
        ← BitVec.getLsbD_eq_getElem]

end S31.Gadgets.IntegerShift
