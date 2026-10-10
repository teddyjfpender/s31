import S31.Gadgets.Schoolbook

/-!
The integer-bound argument for one byte-convolution column in the native
fixed-width multiplication gadget. This proves that its M31 equality cannot
hide modular wrap and that its byte and carry witnesses are unique. The
low-column chain theorem composes the arithmetic into a wrapping product;
the full-chain and high-word theorems cover checked multiplication.
Correspondence to Zig emission remains outside these theorems.
-/

namespace S31.Gadgets.IntegerMultiply

private theorem sum_le_length_mul (terms : List Nat) (bound : Nat)
    (bounded : ∀ term ∈ terms, term ≤ bound) :
    terms.sum ≤ terms.length * bound := by
  induction terms with
  | nil => simp
  | cons head tail ih =>
      have hh := bounded head (by simp)
      have ht : ∀ term ∈ tail, term ≤ bound := by
        intro term member
        exact bounded term (by simp [member])
      have hs := ih ht
      simp only [List.sum_cons, List.length_cons, Nat.succ_mul]
      omega

/-- One low-product column has at most 16 products of two bytes. -/
def Column (products : List Nat) (incoming digit outgoing : Nat) : Prop :=
  products.length ≤ 16 ∧
  (∀ term ∈ products, term ≤ 255 * 255) ∧
  incoming < 65536 ∧ digit < 256 ∧ outgoing < 65536 ∧
  ((products.sum + incoming : Nat) : Field.F) =
    ((digit + 256 * outgoing : Nat) : Field.F)

/-- The low byte needs its own byte check. The high byte is bounded by the
u16 limb and reconstruction equation, saving one range lookup per limb. -/
def SplitLimb (word low high : Nat) : Prop :=
  word < 65536 ∧ low < 256 ∧ high < 65536 ∧
    ((word : Nat) : Field.F) = ((low + 256 * high : Nat) : Field.F)

theorem split_high_byte_sound (word low high : Nat)
    (h : SplitLimb word low high) :
    high < 256 ∧ word = low + 256 * high := by
  obtain ⟨hw, hl, hh, equation⟩ := h
  have integer_equation : word = low + 256 * high :=
    (Field.bounded_equation _ _ (by omega) (by omega)).mp equation
  omega

private theorem sum_bound (products : List Nat)
    (length : products.length ≤ 16)
    (bounded : ∀ term ∈ products, term ≤ 255 * 255) :
    products.sum ≤ 16 * 255 * 255 := by
  have h := sum_le_length_mul products (255 * 255) bounded
  nlinarith

/-- Both sides of the column equation are below p, so equality in M31
is exactly equality over the natural numbers. -/
theorem column_integer_equation (products : List Nat)
    (incoming digit outgoing : Nat)
    (h : Column products incoming digit outgoing) :
    products.sum + incoming = digit + 256 * outgoing := by
  obtain ⟨length, bounded, hin, hd, hout, equation⟩ := h
  have hsum := sum_bound products length bounded
  exact (Field.bounded_equation _ _ (by omega) (by omega)).mp equation

/-- The accepted output byte and next carry are uniquely determined. -/
theorem column_sound (products : List Nat) (incoming digit outgoing : Nat)
    (h : Column products incoming digit outgoing) :
    digit = (products.sum + incoming) % 256 ∧
      outgoing = (products.sum + incoming) / 256 := by
  have equality := column_integer_equation products incoming digit outgoing h
  have hd := h.2.2.2.1
  rw [equality]
  constructor
  · simp [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
  · rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hd]
    simp

/-- The honest byte and carry satisfy the field column relation. -/
theorem column_complete (products : List Nat) (incoming : Nat)
    (length : products.length ≤ 16)
    (bounded : ∀ term ∈ products, term ≤ 255 * 255)
    (hin : incoming < 65536) :
    Column products incoming ((products.sum + incoming) % 256)
      ((products.sum + incoming) / 256) := by
  have hsum := sum_bound products length bounded
  refine ⟨length, bounded, hin, Nat.mod_lt _ (by omega), ?_, ?_⟩
  · omega
  · congr 1
    exact (Nat.mod_add_div (products.sum + incoming) 256).symm

private theorem column_chain_low_value {coefficients digits : List Nat}
    {outgoing : Nat}
    (chain : Schoolbook.Columns coefficients digits 0 outgoing) :
    Words.decode 256 digits =
      Words.decode 256 coefficients % 256 ^ coefficients.length := by
  have bounded := (Schoolbook.columns_bounded chain).1
  have lengths := Schoolbook.columns_lengths chain
  have digits_lt : Words.decode 256 digits < 256 ^ coefficients.length := by
    rw [lengths]
    exact Radix.decode_lt 256 (by omega) digits bounded
  have equality := Schoolbook.columns_equation chain
  have modulo := congrArg (fun value : Nat => value % 256 ^ coefficients.length) equality
  simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt digits_lt] using modulo.symm

private theorem decode_take_mod (words : List Nat) (count : Nat)
    (enough : count ≤ words.length) :
    Words.decode 256 words % 256 ^ count =
      Words.decode 256 (words.take count) % 256 ^ count := by
  have length_take : (words.take count).length = count := by
    simp [List.length_take, Nat.min_eq_left enough]
  have split : Words.decode 256 words =
      Words.decode 256 (words.take count) +
        256 ^ count * Words.decode 256 (words.drop count) := by
    calc
      Words.decode 256 words =
          Words.decode 256 (words.take count ++ words.drop count) := by
            rw [List.take_append_drop]
      _ = _ := by simpa [length_take] using
        (Radix.decode_append 256 (words.take count) (words.drop count))
  rw [split]
  simp [Nat.add_mul_mod_self_left]

/-- Any accepted low-column chain for the mathematical convolution binds the
decoded output to the product modulo the declared byte width. The final carry
is intentionally unrestricted by the wrapping operation. -/
theorem wrapping_product_sound (left right digits : List Nat)
    (byte_count outgoing : Nat)
    (enough : byte_count ≤ (Schoolbook.convolve left right).length)
    (chain : Schoolbook.Columns
      ((Schoolbook.convolve left right).take byte_count) digits 0 outgoing) :
    Words.decode 256 digits =
      (Words.decode 256 left * Words.decode 256 right) % 256 ^ byte_count := by
  have length_take : ((Schoolbook.convolve left right).take byte_count).length = byte_count := by
    simp [List.length_take, Nat.min_eq_left enough]
  have low := column_chain_low_value chain
  rw [length_take] at low
  calc
    Words.decode 256 digits =
        Words.decode 256 ((Schoolbook.convolve left right).take byte_count) %
          256 ^ byte_count := low
    _ = Words.decode 256 (Schoolbook.convolve left right) % 256 ^ byte_count :=
      (decode_take_mod _ _ enough).symm
    _ = (Words.decode 256 left * Words.decode 256 right) % 256 ^ byte_count := by
      rw [Schoolbook.convolution_decode]

/-- The final carry of a complete convolution is zero, so the output is the
exact unsigned product, not just its low bytes. -/
theorem full_product_sound (left right digits : List Nat)
    (chain : Schoolbook.Columns (Schoolbook.convolve left right) digits 0 0) :
    Words.decode 256 digits = Words.decode 256 left * Words.decode 256 right := by
  have h := Schoolbook.columns_equation chain
  simpa [Schoolbook.convolution_decode] using h.symm

/-- A zero high word is precisely the unsigned checked-product condition. -/
theorem unsigned_checked_sound (a b low high modulus : Nat)
    (low_bounded : low < modulus)
    (product : a * b = low + modulus * high)
    (high_zero : high = 0) : a * b < modulus := by
  rw [high_zero] at product
  omega

theorem unsigned_checked_complete (a b low high modulus : Nat)
    (product : a * b = low + modulus * high)
    (fits : a * b < modulus) : high = 0 := by
  by_contra not_zero
  have one_le : 1 ≤ high := by omega
  have large : modulus ≤ modulus * high := by
    simpa using Nat.mul_le_mul_left modulus one_le
  omega

/-- The signed high-word correction includes its terminal carry. Together
with the exact unsigned product, it proves the mathematical signed product
equals the sign-extended low word. -/
theorem signed_checked_sound (a b low high modulus sa sb sr carry : Nat)
    (positive : 0 < modulus)
    (product : a * b = low + modulus * high)
    (correction : high + modulus * carry =
      sa * b + sb * a + sr * (modulus - 1))
    (terminal : carry = sa * sb + sr) :
    ((a : Int) - sa * modulus) * ((b : Int) - sb * modulus) =
      (low : Int) - sr * modulus := by
  have product_int : (a : Int) * b = low + modulus * high := by
    exact_mod_cast product
  have correction_int : (high : Int) + modulus * carry =
      sa * b + sb * a + sr * ((modulus : Int) - 1) := by
    have hsub : ((modulus - 1 : Nat) : Int) = (modulus : Int) - 1 := by omega
    have casted : (high : Int) + modulus * carry =
        sa * b + sb * a + sr * ((modulus - 1 : Nat) : Int) := by
      exact_mod_cast correction
    simpa [hsub] using casted
  have multiplied := congrArg (fun x : Int => x * modulus) correction_int
  rw [terminal] at multiplied
  simp only [Nat.cast_add, Nat.cast_mul] at multiplied
  nlinarith [product_int, multiplied]

/-- A representable signed product satisfies the exact high-word correction
with terminal carry `sa*sb+sr`; the column witnesses then exist by division. -/
theorem signed_checked_complete (a b low high modulus sa sb sr : Nat)
    (positive : 0 < modulus)
    (product : a * b = low + modulus * high)
    (signed_product :
      ((a : Int) - sa * modulus) * ((b : Int) - sb * modulus) =
        (low : Int) - sr * modulus) :
    high + modulus * (sa * sb + sr) =
      sa * b + sb * a + sr * (modulus - 1) := by
  have product_int : (a : Int) * b = low + modulus * high := by
    exact_mod_cast product
  have shifted : (modulus : Int) * (high + modulus * (sa * sb + sr)) =
      modulus * (sa * b + sb * a + sr * ((modulus : Int) - 1)) := by
    nlinarith [product_int, signed_product]
  have hsub : ((modulus - 1 : Nat) : Int) = (modulus : Int) - 1 := by omega
  have desired_int : (high : Int) + modulus * (sa * sb + sr) =
      sa * b + sb * a + sr * ((modulus : Int) - 1) := by
    exact mul_left_cancel₀ (by omega : (modulus : Int) ≠ 0) shifted
  exact_mod_cast (show (high : Int) + modulus * (sa * sb + sr) =
      sa * b + sb * a + sr * ((modulus - 1 : Nat) : Int) by
        simpa [hsub] using desired_int)

end S31.Gadgets.IntegerMultiply
