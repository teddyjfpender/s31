import S31.Gadgets.Field
import Mathlib.FieldTheory.Finite.Basic

/-!
Static power fusion is valid for every M31 value, including zero. Reducing a
positive exponent to the range `1..p-1` preserves zero's result; reducing to
`0..p-2` would turn a positive power of zero into `zero^0 = 1`.

`PowerChains.lean` proves the meaning of a valid star chain, and finite source
tests compare selected compiler schedules with checked reference lists. This
file proves the exponent rewrite used before a chain is selected; general
compiler and native AIR correspondence remain separate obligations.
-/

namespace S31.Field

def positiveExponent (exponent : Nat) : Nat :=
  (exponent - 1) % (2147483647 - 1) + 1

theorem positiveExponent_pos (exponent : Nat) :
    0 < positiveExponent exponent := by
  simp [positiveExponent]

theorem positiveExponent_lt_prime (exponent : Nat) :
    positiveExponent exponent < 2147483647 := by
  unfold positiveExponent
  have h := Nat.mod_lt (exponent - 1) (by decide : 0 < 2147483647 - 1)
  omega

theorem positiveExponent_sound (x : F) (exponent : Nat)
    (positive : 0 < exponent) :
    x ^ positiveExponent exponent = x ^ exponent := by
  by_cases zero : x = 0
  · subst x
    simp [zero_pow (Nat.ne_of_gt (positiveExponent_pos exponent)),
          zero_pow (Nat.ne_of_gt positive)]
  · have fermat : x ^ (2147483647 - 1) = 1 :=
      ZMod.pow_card_sub_one_eq_one zero
    have reduced : x ^ (exponent - 1) =
        x ^ ((exponent - 1) % (2147483647 - 1)) :=
      pow_eq_pow_mod _ fermat
    unfold positiveExponent
    rw [pow_succ, ← reduced]
    exact pow_sub_one_mul (Nat.ne_of_gt positive) x

theorem composed_positive_power_sound (x : F) (first second : Nat)
    (first_pos : 0 < first) (second_pos : 0 < second) :
    (x ^ first) ^ second = x ^ positiveExponent (first * second) := by
  rw [← pow_mul]
  exact (positiveExponent_sound x (first * second)
    (Nat.mul_pos first_pos second_pos)).symm

end S31.Field
