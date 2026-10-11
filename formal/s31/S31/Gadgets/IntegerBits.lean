import S31.Gadgets.Word
import S31.Gadgets.Packing

/-!
Pointwise bitwise constraints for any fixed width. A native S31 integer word
is first decomposed into Boolean bits and each output word is reconstructed;
these theorems cover the Boolean operation independently of width. The
production Zig circuit-to-model correspondence remains unproved.
-/

namespace S31.Gadgets.IntegerBits

open S31.Gadgets

abbrev flag (b : Bool) : Field.F := encodeBool b

private theorem flag_injective : Function.Injective flag := by
  intro a b h
  cases a <;> cases b <;> simp_all [flag, encodeBool]

def andConstraint {width : Nat} (a b y : BitVec width) : Prop := ∀ i, i < width →
  Gadgets.andConstraint (flag (a.getLsbD i)) (flag (b.getLsbD i)) (flag (y.getLsbD i))
def orConstraint {width : Nat} (a b y : BitVec width) : Prop := ∀ i, i < width →
  Gadgets.orConstraint (flag (a.getLsbD i)) (flag (b.getLsbD i)) (flag (y.getLsbD i))
def xorConstraint {width : Nat} (a b y : BitVec width) : Prop := ∀ i, i < width →
  Gadgets.xorConstraint (flag (a.getLsbD i)) (flag (b.getLsbD i)) (flag (y.getLsbD i))
def notConstraint {width : Nat} (a y : BitVec width) : Prop := ∀ i, i < width →
  Gadgets.notConstraint (flag (a.getLsbD i)) (flag (y.getLsbD i))

theorem and_sound_complete {width : Nat} (a b y : BitVec width) :
    andConstraint a b y ↔ y = a &&& b := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    apply flag_injective
    simpa [flag] using (Gadgets.and_sound_complete (a.getLsbD i) (b.getLsbD i)
      (flag (y.getLsbD i))).mp (h i hi)
  · rintro rfl i hi
    apply (Gadgets.and_sound_complete _ _ _).mpr
    simp [flag]

theorem or_sound_complete {width : Nat} (a b y : BitVec width) :
    orConstraint a b y ↔ y = a ||| b := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    apply flag_injective
    simpa [flag] using (Gadgets.or_sound_complete (a.getLsbD i) (b.getLsbD i)
      (flag (y.getLsbD i))).mp (h i hi)
  · rintro rfl i hi
    apply (Gadgets.or_sound_complete _ _ _).mpr
    simp [flag]

theorem xor_sound_complete {width : Nat} (a b y : BitVec width) :
    xorConstraint a b y ↔ y = a ^^^ b := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    apply flag_injective
    simpa [flag] using (Gadgets.xor_sound_complete (a.getLsbD i) (b.getLsbD i)
      (flag (y.getLsbD i))).mp (h i hi)
  · rintro rfl i hi
    apply (Gadgets.xor_sound_complete _ _ _).mpr
    simp [flag]

theorem not_sound_complete {width : Nat} (a y : BitVec width) :
    notConstraint a y ↔ y = ~~~a := by
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    apply flag_injective
    simpa [flag, hi] using (Gadgets.not_sound_complete (a.getLsbD i)
      (flag (y.getLsbD i))).mp (h i hi)
  · rintro rfl i hi
    apply (Gadgets.not_sound_complete _ _).mpr
    simp [flag, hi]

end S31.Gadgets.IntegerBits
