import Mathlib.Tactic

/-!
Arithmetic semantics of `deps/stwo-zig/src/core/fields/m31.zig` at the
canonical-word boundary. These are proofs about the operations below, whose
source shapes are checked by
`scripts/s31_formal_lib/pcs_fri_native_m31_arithmetic.py`.
The native source is responsible for ensuring operands are canonical; a caller
of `fromU32Unchecked` does not get that invariant for free. SIMD vector lanes
obey the same equations if Zig's lane-wise operations and AArch64 `sqdmulh`
obey their documented integer instruction semantics.
-/

namespace S31.Gadgets.PcsFri.NativeM31Arithmetic

def p : Nat := 2 ^ 31 - 1
def base : Nat := 2 ^ 31
def wordSize : Nat := 2 ^ 32
def wideSize : Nat := 2 ^ 64

private theorem p_pos : 0 < p := by norm_num [p]
private theorem base_eq : base = p + 1 := by norm_num [base, p]

/-- One Mersenne fold, corresponding to `(x & p) + (x >> 31)`. -/
def fold (x : Nat) : Nat := x % base + x / base

theorem fold_preserves_residue (x : Nat) : fold x % p = x % p := by
  have hs := Nat.mod_add_div x base
  have hp : base = p + 1 := base_eq
  have heq : x = fold x + p * (x / base) := by
    dsimp [fold, base, p] at hs ⊢
    omega
  calc
    fold x % p = (fold x + p * (x / base)) % p := by
      simp [Nat.add_mod]
    _ = x % p := by rw [← heq]

/-- The `@min(r, r -% p)` canonicalizer, with the u32 wrap explicit. -/
def minCanonical (r : Nat) : Nat := min r ((r + wordSize - p) % wordSize)

theorem min_canonical_eq (r : Nat) (hr : r < 2 * p) :
    minCanonical r = r % p := by
  have hp : p = 2147483647 := by norm_num [p]
  have hw : wordSize = 4294967296 := by norm_num [wordSize]
  unfold minCanonical
  by_cases h : r < p
  · have hmod : r % p = r := Nat.mod_eq_of_lt h
    rw [hmod]
    have hwrap : (r + wordSize - p) % wordSize = r + wordSize - p := by
      apply Nat.mod_eq_of_lt
      omega
    rw [hwrap]
    omega
  · have hrep : r = p + (r - p) := by omega
    have hmod : r % p = r - p := by
      conv_lhs => rw [hrep]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : r - p < p)]
    rw [hmod]
    have hwrap : (r + wordSize - p) % wordSize = r - p := by
      have heq : r + wordSize - p = wordSize + (r - p) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : r - p < wordSize)]
    rw [hwrap]
    omega

/-- The exact two-fold u64 path, with all intermediates in natural numbers. -/
def reduce64 (x : Nat) : Nat := minCanonical (fold (fold x))

theorem fold_twice_lt_two_p (x : Nat) (hx : x < wideSize) :
    fold (fold x) < 2 * p := by
  have hs := Nat.mod_add_div x base
  have hrem := Nat.mod_lt x (by norm_num [base] : 0 < base)
  have hp : p = 2147483647 := by norm_num [p]
  have hb : base = 2147483648 := by norm_num [base]
  have hw : wideSize = 18446744073709551616 := by norm_num [wideSize]
  have hq : x / base < 8589934592 := by
    dsimp [base, wideSize] at hs hx ⊢
    omega
  have hf : fold x < 10737418240 := by unfold fold; omega
  have hs2 := Nat.mod_add_div (fold x) base
  have hrem2 := Nat.mod_lt (fold x) (by norm_num [base] : 0 < base)
  have hq2 : fold x / base ≤ 4 := by
    dsimp [base] at hs2 hf ⊢
    omega
  change (fold x) % base + (fold x) / base < 2 * p
  omega

theorem reduce64_eq_mod (x : Nat) (hx : x < wideSize) :
    reduce64 x = x % p := by
  unfold reduce64
  rw [min_canonical_eq _ (fold_twice_lt_two_p x hx),
      fold_preserves_residue, fold_preserves_residue]

theorem reduce64_canonical (x : Nat) (hx : x < wideSize) :
    reduce64 x < p := by
  rw [reduce64_eq_mod x hx]
  exact Nat.mod_lt _ p_pos

theorem reduce64_precast_fits_u32 (x : Nat) (hx : x < wideSize) :
    fold (fold x) < wordSize := by
  have h := fold_twice_lt_two_p x hx
  norm_num [p, wordSize] at *
  omega

/-- The one-fold product path has a stronger precondition: `x < p²`. -/
def reduceProduct (x : Nat) : Nat :=
  if p ≤ fold x then fold x - p else fold x

theorem fold_product_lt_two_p (x : Nat) (hx : x < p * p) :
    fold x < 2 * p := by
  have hs := Nat.mod_add_div x base
  have hr := Nat.mod_lt x (by norm_num [base] : 0 < base)
  have hp : p = 2147483647 := by norm_num [p]
  have hb : base = 2147483648 := by norm_num [base]
  have hq : x / base < p := by
    dsimp [base, p] at hs hx ⊢
    omega
  unfold fold
  omega

theorem reduce_product_eq_mod (x : Nat) (hx : x < p * p) :
    reduceProduct x = x % p := by
  have hb := fold_product_lt_two_p x hx
  have hf := fold_preserves_residue x
  unfold reduceProduct
  split_ifs with h
  · have hrep : fold x = p + (fold x - p) := by omega
    have : fold x % p = fold x - p := by
      conv_lhs => rw [hrep]
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : fold x - p < p)]
    rw [← this, hf]
  · have : fold x % p = fold x := Nat.mod_eq_of_lt (by omega)
    rw [← this, hf]

theorem reduce_product_precast_fits_u32 (x : Nat) (hx : x < p * p) :
    fold x < wordSize := by
  have h := fold_product_lt_two_p x hx
  norm_num [p, wordSize] at *
  omega

theorem canonical_product_lt (a b : Nat) (ha : a < p) (hb : b < p) :
    a * b < p * p := by nlinarith

theorem native_mul_eq_mod (a b : Nat) (ha : a < p) (hb : b < p) :
    reduceProduct (a * b) = (a * b) % p :=
  reduce_product_eq_mod _ (canonical_product_lt a b ha hb)

/-- Scalar `M31.add`: no u32 overflow because both operands are canonical. -/
def add (a b : Nat) : Nat := if p ≤ a + b then a + b - p else a + b

theorem add_eq_mod (a b : Nat) (ha : a < p) (hb : b < p) :
    add a b = (a + b) % p := by
  unfold add
  split_ifs with h
  · have hrep : a + b = p + (a + b - p) := by omega
    conv_rhs => rw [hrep]
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : a + b - p < p)]
  · exact (Nat.mod_eq_of_lt (by omega)).symm

theorem add_no_u32_overflow (a b : Nat) (ha : a < p) (hb : b < p) :
    a + b < wordSize := by
  norm_num [p, wordSize] at *
  omega

theorem add_cast_eq (a b : Nat) (ha : a < p) (hb : b < p) :
    (add a b : ZMod 2147483647) =
      (a : ZMod 2147483647) + b := by
  rw [add_eq_mod a b ha hb]
  simp [p, ZMod.natCast_mod]

/-- The `@min(sum, sum -% p)` AArch64 Vec4 lane agrees with scalar add. -/
theorem add_vec_aarch64_eq (a b : Nat) (ha : a < p) (hb : b < p) :
    minCanonical (a + b) = add a b := by
  rw [min_canonical_eq _ (by omega), add_eq_mod a b ha hb]

/-- Scalar `M31.sub` and AArch64 `subVec4` share this result. -/
def sub (a b : Nat) : Nat :=
  if b ≤ a then a - b else a + p - b

theorem sub_canonical (a b : Nat) (ha : a < p) (hb : b < p) :
    sub a b < p := by
  unfold sub
  split_ifs <;> omega

theorem sub_intermediate_fits_u32 (a : Nat) (ha : a < p) :
    a + p < wordSize := by
  norm_num [p, wordSize] at *
  omega

theorem sub_cast_eq (a b : Nat) (ha : a < p) (hb : b < p) :
    (sub a b : ZMod 2147483647) = (a : ZMod 2147483647) - b := by
  have hp : p = 2147483647 := by norm_num [p]
  unfold sub
  split_ifs with h
  · simp only [Nat.cast_sub h]
  · have hba : b ≤ a + p := by omega
    rw [Nat.cast_sub hba, Nat.cast_add]
    have hp0 : (p : ZMod 2147483647) = 0 := by
      simpa [p] using ZMod.natCast_self 2147483647
    rw [hp0]
    simp

/-- The unsigned-minimum subtraction expression used by AArch64 Vec4. -/
def subVecAarch64 (a b : Nat) : Nat :=
  let d := (a + wordSize - b) % wordSize
  min d ((d + p) % wordSize)

theorem sub_vec_aarch64_eq (a b : Nat) (ha : a < p) (hb : b < p) :
    subVecAarch64 a b = sub a b := by
  have hp : p = 2147483647 := by norm_num [p]
  have hw : wordSize = 4294967296 := by norm_num [wordSize]
  unfold subVecAarch64 sub
  by_cases h : b ≤ a
  · simp only [if_pos h]
    have hd : (a + wordSize - b) % wordSize = a - b := by
      have heq : a + wordSize - b = wordSize + (a - b) := by omega
      rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : a - b < wordSize)]
    rw [hd]
    have hdp : (a - b + p) % wordSize = a - b + p :=
      Nat.mod_eq_of_lt (by omega)
    rw [hdp]
    exact min_eq_left (by omega)
  · simp only [if_neg h]
    have hd : (a + wordSize - b) % wordSize = a + wordSize - b :=
      Nat.mod_eq_of_lt (by omega)
    rw [hd]
    have heq : a + wordSize - b + p = wordSize + (a + p - b) := by omega
    rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : a + p - b < wordSize)]
    exact min_eq_right (by omega)

/-- The low 31 bits of AArch64 `mul` are the product modulo `2^31`. -/
theorem low_mul_bits_eq (x : Nat) :
    (x % wordSize) % base = x % base := by
  have hd : base ∣ wordSize := by norm_num [base, wordSize]
  exact Nat.mod_mod_of_dvd x hd

/-- Under the canonical operand contract, signed doubling in `SQDMULH`
cannot saturate its 64-bit intermediate. -/
theorem sqdmulh_no_saturation (a b : Nat) (ha : a < p) (hb : b < p) :
    2 * (a * b) < 2 ^ 63 := by
  have hprod := canonical_product_lt a b ha hb
  norm_num [p] at hprod ⊢
  nlinarith

/-- AArch64 `sqdmulh` computes `(2ab) >> 32 = (ab) >> 31`
for the nonnegative canonical operands. -/
theorem sqdmulh_high_eq (a b : Nat) :
    2 * (a * b) / wordSize = a * b / base := by
  have hw : wordSize = 2 * base := by norm_num [wordSize, base]
  rw [hw]
  exact Nat.mul_div_mul_left _ _ (by decide : 0 < 2)

/-- One AArch64 vector lane, modeling `mul`, `sqdmulh`, mask, add, and
unsigned minimum. The only hardware premise is the instruction semantics
spelled out by `low_mul_bits_eq` and `sqdmulh_high_eq`. -/
def mulVecAarch64Lane (a b : Nat) : Nat :=
  minCanonical ((a * b % wordSize) % base + 2 * (a * b) / wordSize)

theorem mul_vec_aarch64_eq (a b : Nat) (ha : a < p) (hb : b < p) :
    mulVecAarch64Lane a b = reduceProduct (a * b) := by
  have hx := canonical_product_lt a b ha hb
  unfold mulVecAarch64Lane
  rw [low_mul_bits_eq, sqdmulh_high_eq]
  change minCanonical (fold (a * b)) = reduceProduct (a * b)
  rw [min_canonical_eq _ (fold_product_lt_two_p _ hx),
      reduce_product_eq_mod _ hx, fold_preserves_residue]

theorem mul_vec_aarch64_cast (a b : Nat) (ha : a < p) (hb : b < p) :
    (mulVecAarch64Lane a b : ZMod 2147483647) =
      (a : ZMod 2147483647) * b := by
  rw [mul_vec_aarch64_eq a b ha hb, native_mul_eq_mod a b ha hb]
  simp [p, ZMod.natCast_mod]

end S31.Gadgets.PcsFri.NativeM31Arithmetic
