import S31.Gadgets.IntegerMultiply

/-!
Local arithmetic model for checked fixed-width numeric casts. The Zig circuit
checks the same low-byte split, high-limb sign extension, and destination sign
bit, but correspondence of emitted gates to this model is still a separate
compiler-correctness obligation.
-/

namespace S31.Gadgets.IntegerCast

/-- The narrowing byte split cannot hide an alternate high byte in M31. -/
theorem narrow_byte_sound (word low high sign : Nat)
    (split : IntegerMultiply.SplitLimb word low high)
    (high_sign : high = 255 * sign) :
    word = low + 65280 * sign := by
  have h := (IntegerMultiply.split_high_byte_sound word low high split).2
  omega

/-- Every removed u16 limb equals the sign extension as an integer, since
both field operands are strictly below the M31 modulus. -/
theorem high_limb_sound (high sign : Nat)
    (high_bound : high < 65536) (sign_bit : sign ≤ 1)
    (field_eq : ((high : Nat) : Field.F) = ((sign * 65535 : Nat) : Field.F)) :
    high = sign * 65535 := by
  exact (Field.bounded_equation _ _ (by omega) (by omega)).mp field_eq

/-- Sign extension from modulus `sourceMod` to `targetMod` preserves the
interpreted signed value. This is the equation used by widening casts. -/
theorem widening_value_sound (source output sourceMod targetMod sign : Int)
    (extension : output = source + sign * (targetMod - sourceMod)) :
    output - sign * targetMod = source - sign * sourceMod := by
  rw [extension]
  ring

/-- If all removed high limbs match the sign and the remaining sign bit
agrees, narrowing preserves the interpreted signed value. -/
theorem narrowing_value_sound (source output sourceMod targetMod sign : Int)
    (removed : source = output + sign * (sourceMod - targetMod)) :
    source - sign * sourceMod = output - sign * targetMod := by
  rw [removed]
  ring

/-- The source or destination sign is constrained to zero when a checked cast
crosses from a signed negative pattern to an unsigned value, or from an
unsigned pattern into a signed destination of the same width. -/
theorem zero_sign_value (pattern modulus : Int) :
    pattern - 0 * modulus = pattern := by ring

/-- Any integer in the destination's representable modulus interval has a
canonical output pattern and Boolean sign witness. The narrower signed range
check is a separate premise of the cast operation. -/
theorem representable_pattern (modulus value : Int)
    (positive : 0 < modulus) (lower : -modulus ≤ value) (upper : value < modulus) :
    ∃ pattern sign : Int,
      (sign = 0 ∨ sign = 1) ∧ 0 ≤ pattern ∧ pattern < modulus ∧
        value = pattern - sign * modulus := by
  by_cases negative : value < 0
  · refine ⟨value + modulus, 1, Or.inr rfl, ?_, ?_, ?_⟩ <;> omega
  · refine ⟨value, 0, Or.inl rfl, ?_, ?_, ?_⟩ <;> omega

end S31.Gadgets.IntegerCast
