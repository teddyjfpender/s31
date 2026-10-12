import S31.Gadgets.Schoolbook

namespace S31.Gadgets.UnsignedCheckedShortcut
open S31.Gadgets

/-- The arithmetic meaning of the low-column gates. The production circuit
also proves digit and carry ranges; this model starts after each field equation
has been lifted to the corresponding equation over natural numbers. -/
inductive LowColumns (base : Nat) : List Nat → List Nat → Nat → Nat → Prop where
  | nil (carry : Nat) : LowColumns base [] [] carry carry
  | cons {coefficient incoming digit next terminal : Nat}
      {coefficients digits : List Nat}
      (equation : coefficient + incoming = digit + base * next)
      (tail : LowColumns base coefficients digits next terminal) :
      LowColumns base (coefficient :: coefficients) (digit :: digits) incoming terminal

theorem low_columns_equation {base : Nat} {coefficients digits : List Nat}
    {incoming terminal : Nat}
    (h : LowColumns base coefficients digits incoming terminal) :
    Words.decode base coefficients + incoming =
      Words.decode base digits + base ^ coefficients.length * terminal := by
  induction h with
  | nil carry => simp [Words.decode]
  | cons equation tail ih =>
    simp only [Words.decode, List.length_cons, Nat.pow_succ]
    nlinarith

/-- The quotient is the portion of the normalized low word at bit positions
`width` and above. In production it is zero because those bits are constrained
to zero, including the unused bits of a partial top radix digit. -/
def NoSpill (base width : Nat) (digits : List Nat) : Prop :=
  Words.decode base digits / 2 ^ width = 0

theorem no_spill_lt {base width : Nat} {digits : List Nat}
    (h : NoSpill base width digits) : Words.decode base digits < 2 ^ width := by
  unfold NoSpill at h
  have hp : 0 < 2 ^ width := Nat.pow_pos (by decide)
  have hdiv : Words.decode base digits / 2 ^ width < 1 := by omega
  simpa using (Nat.div_lt_iff_lt_mul hp).mp hdiv

/-- A concrete way to discharge `NoSpill` for a partial top digit: the low
digits have radix `2^digitBits`, and the final digit uses only `topBits` bits.
The prefix bound is supplied by the circuit's bit decompositions. -/
theorem partial_top_no_spill (digitBits topBits : Nat) (lowPrefix : List Nat) (top : Nat)
    (hprefix : Radix.Bounded (2 ^ digitBits) lowPrefix)
    (htop : top < 2 ^ topBits) (_hpartial : topBits ≤ digitBits) :
    NoSpill (2 ^ digitBits) (digitBits * lowPrefix.length + topBits) (lowPrefix ++ [top]) := by
  have hp : 0 < 2 ^ digitBits := Nat.pow_pos (by decide)
  have hprefixBound := Radix.decode_lt (2 ^ digitBits) hp lowPrefix hprefix
  have htopBound : top + 1 ≤ 2 ^ topBits := by omega
  have hmul := Nat.mul_le_mul_left ((2 ^ digitBits) ^ lowPrefix.length) htopBound
  have hbound : Words.decode (2 ^ digitBits) (lowPrefix ++ [top]) <
      (2 ^ digitBits) ^ lowPrefix.length * 2 ^ topBits := by
    rw [Radix.decode_append]
    simp only [Words.decode, mul_zero, add_zero]
    nlinarith
  have hpower : (2 ^ digitBits) ^ lowPrefix.length * 2 ^ topBits =
      2 ^ (digitBits * lowPrefix.length + topBits) := by
    rw [pow_add, pow_mul]
  unfold NoSpill
  exact Nat.div_eq_of_lt (hpower ▸ hbound)

private theorem decode_all_zero (base : Nat) (xs : List Nat)
    (h : ∀ x ∈ xs, x = 0) : Words.decode base xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx : x = 0 := h x (by simp)
    have ht : ∀ y ∈ xs, y = 0 := by
      intro y hy
      exact h y (by simp [hy])
    simp [Words.decode, hx, ih ht]

/-- Arithmetic soundness of the unsigned checked shortcut. `LowColumns`
represents the first `n` recurrence equations, `terminal = 0` rules out a
truncated carry, and every omitted high convolution coefficient is zero.
`NoSpill` rules out overflow within the partial top low digit. This theorem
does not establish the compiler's operand provenance or field-to-integer
lifting; those are explicit preconditions of this model. -/
theorem product_eq_low_and_fits (base width n : Nat) (left right low : List Nat)
    (terminal : Nat)
    (hlow : LowColumns base ((Schoolbook.convolve left right).take n) low 0 terminal)
    (hterminal : terminal = 0)
    (hhigh : ∀ c ∈ (Schoolbook.convolve left right).drop n, c = 0)
    (hspill : NoSpill base width low) :
    Words.decode base left * Words.decode base right = Words.decode base low ∧
      Words.decode base left * Words.decode base right < 2 ^ width := by
  let coefficients := Schoolbook.convolve left right
  have hzero : Words.decode base (coefficients.drop n) = 0 :=
    decode_all_zero base _ hhigh
  have hcolumns := low_columns_equation hlow
  have hlowEq : Words.decode base (coefficients.take n) = Words.decode base low := by
    simpa [coefficients, hterminal] using hcolumns
  have hsplit : Words.decode base coefficients =
      Words.decode base (coefficients.take n) +
        base ^ (coefficients.take n).length * Words.decode base (coefficients.drop n) := by
    calc
      Words.decode base coefficients =
          Words.decode base (coefficients.take n ++ coefficients.drop n) := by
            rw [List.take_append_drop]
      _ = _ := Radix.decode_append base _ _
  have heq : Words.decode base left * Words.decode base right = Words.decode base low := by
    rw [← Schoolbook.convolution_decode base left right]
    change Words.decode base coefficients = _
    rw [hsplit, hzero, mul_zero, add_zero, hlowEq]
  exact ⟨heq, heq ▸ no_spill_lt hspill⟩

end S31.Gadgets.UnsignedCheckedShortcut
