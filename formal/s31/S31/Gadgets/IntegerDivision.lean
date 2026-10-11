import S31.Gadgets.Bitcoin

/-!
Width-generic mathematical model for the unsigned `int_div_rem` relation.
The existing schoolbook proof turns bounded base-256 column equalities with
zero terminal carry into one integer equation. The strict remainder bound
then determines the Euclidean quotient and remainder uniquely. This file
does not assert a machine-checked refinement from production Zig gates to
the Lean column model.
-/

namespace S31.Gadgets.IntegerDivision
open Words Radix

def unsignedConstraint {width : Nat} (a b q r : BitVec width) : Prop :=
  Bitcoin.divisionConstraint a.toNat b.toNat q.toNat r.toNat

theorem unsigned_sound_complete {width : Nat} (a b q r : BitVec width) :
    unsignedConstraint a b q r ↔
      0 < b.toNat ∧ q.toNat = a.toNat / b.toNat ∧
      r.toNat = a.toNat % b.toNat := by
  exact Bitcoin.division_sound_complete _ _ _ _

theorem zero_divisor_rejected {width : Nat} (a q r : BitVec width) :
    ¬ unsignedConstraint a 0 q r := by
  intro h
  have hd := (unsigned_sound_complete a 0 q r).mp h |>.1
  simp at hd

theorem quotient_remainder_unique {width : Nat} (a b q₁ q₂ r₁ r₂ : BitVec width)
    (h₁ : unsignedConstraint a b q₁ r₁)
    (h₂ : unsignedConstraint a b q₂ r₂) : q₁ = q₂ ∧ r₁ = r₂ := by
  have e₁ := (unsigned_sound_complete a b q₁ r₁).mp h₁
  have e₂ := (unsigned_sound_complete a b q₂ r₂).mp h₂
  constructor
  · apply BitVec.eq_of_toNat_eq
    exact e₁.2.1.trans e₂.2.1.symm
  · apply BitVec.eq_of_toNat_eq
    exact e₁.2.2.trans e₂.2.2.symm

def signedValue (negative : Bool) (magnitude : Nat) : Int :=
  if negative then -(magnitude : Int) else magnitude

/-- Applying the quotient's XOR sign and the dividend's remainder sign to
an unsigned Euclidean relation reconstructs the signed equation. -/
theorem signed_reconstruction (negativeA negativeB : Bool) (a b q r : Nat)
    (h : a = q * b + r) :
    signedValue negativeA a =
      signedValue (negativeA != negativeB) q * signedValue negativeB b +
        signedValue negativeA r := by
  cases negativeA <;> cases negativeB <;> simp [signedValue, h] <;> omega

/-! A signed wide conversion selects either the original 16-bit limb or its
one's complement, then adds the incoming carry. The native circuit constrains
the sign, incoming carry, outgoing carry, and output bits. This bound upgrades
the resulting M31 equation to an exact integer equation per limb. -/
def directSignedLimbConstraint
    (sign input incoming digit outgoing : Nat) : Prop :=
  sign < 2 ∧ input < 65536 ∧ incoming < 2 ∧
    digit < 65536 ∧ outgoing < 2 ∧
    ((if sign = 0 then input else 65535 - input) + incoming) % 2147483647 =
      (digit + 65536 * outgoing) % 2147483647

theorem direct_signed_limb_no_wrap
    (sign input incoming digit outgoing : Nat)
    (h : directSignedLimbConstraint sign input incoming digit outgoing) :
    (if sign = 0 then input else 65535 - input) + incoming =
      digit + 65536 * outgoing := by
  rcases h with ⟨hs, hi, hc, hd, ho, heq⟩
  have hl : (if sign = 0 then input else 65535 - input) + incoming < 2147483647 := by
    split_ifs <;> omega
  have hr : digit + 65536 * outgoing < 2147483647 := by omega
  simpa [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using heq

/-- The fused base-256 columns prove the full product-plus-remainder
equation, including high product bytes. The hypotheses make the range and
same-length obligations explicit. -/
theorem fused_columns_exact (q d r n : List Nat)
    (hc : ∀ c ∈ Schoolbook.addPad (Schoolbook.convolve q d) r,
      c ≤ Schoolbook.coefficientLimit)
    (hn : Bounded 256 n)
    (hlen : (Schoolbook.addPad (Schoolbook.convolve q d) r).length = n.length) :
    Schoolbook.Columns (Schoolbook.addPad (Schoolbook.convolve q d) r) n 0 0 ↔
      decode 256 n = decode 256 q * decode 256 d + decode 256 r := by
  rw [Schoolbook.schoolbook_product_sound_complete q d r n hc hn hlen, eq_comm]

/-- The direct byte circuit uses field equalities rather than a range table.
Once its five byte wires are bounded, both sides of each equation lie below
the M31 modulus, so a field equality is an exact integer equality. -/
def directByteConstraint (n d q r difference : Nat) : Prop :=
  n < 256 ∧ d < 256 ∧ q < 256 ∧ r < 256 ∧ difference < 256 ∧
    (q * d + r) % 2147483647 = n % 2147483647 ∧
    d % 2147483647 = (r + 1 + difference) % 2147483647

theorem direct_byte_no_wrap (n d q r difference : Nat)
    (h : directByteConstraint n d q r difference) :
    n = q * d + r ∧ r < d := by
  rcases h with ⟨hn, hd, hq, hr, hdiff, hproduct, hcompare⟩
  have hq' : q ≤ 255 := by omega
  have hd' : d ≤ 255 := by omega
  have hmul : q * d ≤ 255 * 255 := Nat.mul_le_mul hq' hd'
  have hn_field : n < 2147483647 := by omega
  have hd_field : d < 2147483647 := by omega
  have hproduct_bound : q * d + r < 2147483647 := by omega
  have hcompare_bound : r + 1 + difference < 2147483647 := by omega
  constructor
  · simpa [Nat.mod_eq_of_lt hproduct_bound, Nat.mod_eq_of_lt hn_field] using hproduct.symm
  · have hexact : d = r + 1 + difference := by
      simpa [Nat.mod_eq_of_lt hd_field, Nat.mod_eq_of_lt hcompare_bound] using hcompare
    omega

theorem direct_byte_division (n d q r difference : Nat)
    (h : directByteConstraint n d q r difference) :
    0 < d ∧ q = n / d ∧ r = n % d := by
  obtain ⟨hproduct, hrem⟩ := direct_byte_no_wrap n d q r difference h
  exact (Bitcoin.division_sound_complete n d q r).mp ⟨hproduct, hrem⟩

/-- For the direct 16-bit circuit, a base-256 product column contains at most
two byte products, one remainder byte, and one 16-bit incoming carry. Both
sides are below M31, so the circuit's field equation is an integer equation. -/
def directWordColumnConstraint (coefficient incoming digit outgoing : Nat) : Prop :=
  coefficient ≤ 2 * 255 * 255 + 255 ∧ incoming < 65536 ∧
    digit < 256 ∧ outgoing < 65536 ∧
    (coefficient + incoming) % 2147483647 =
      (digit + 256 * outgoing) % 2147483647

theorem direct_word_column_no_wrap (coefficient incoming digit outgoing : Nat)
    (h : directWordColumnConstraint coefficient incoming digit outgoing) :
    coefficient + incoming = digit + 256 * outgoing := by
  rcases h with ⟨hc, hi, hd, ho, heq⟩
  have hl : coefficient + incoming < 2147483647 := by omega
  have hr : digit + 256 * outgoing < 2147483647 := by omega
  simpa [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using heq

/-- The two byte borrow equations prove a strict 16-bit remainder bound.
The final borrow must be zero, including when the divisor itself is zero. -/
def directWordStrict (d₀ d₁ r₀ r₁ e₀ e₁ b₀ b₁ : Nat) : Prop :=
  d₀ < 256 ∧ d₁ < 256 ∧ r₀ < 256 ∧ r₁ < 256 ∧
    e₀ < 256 ∧ e₁ < 256 ∧ b₀ < 2 ∧ b₁ = 0 ∧
    (d₀ + 256 * b₀) % 2147483647 = (r₀ + 1 + e₀) % 2147483647 ∧
    (d₁ + 256 * b₁) % 2147483647 = (r₁ + b₀ + e₁) % 2147483647

theorem direct_word_strict_remainder (d₀ d₁ r₀ r₁ e₀ e₁ b₀ b₁ : Nat)
    (h : directWordStrict d₀ d₁ r₀ r₁ e₀ e₁ b₀ b₁) :
    r₀ + 256 * r₁ < d₀ + 256 * d₁ := by
  rcases h with ⟨hd₀, hd₁, hr₀, hr₁, he₀, he₁, hb₀, hb₁, hlow, hhigh⟩
  have hl₁ : d₀ + 256 * b₀ < 2147483647 := by omega
  have hr₁' : r₀ + 1 + e₀ < 2147483647 := by omega
  have hl₂ : d₁ + 256 * b₁ < 2147483647 := by omega
  have hr₂ : r₁ + b₀ + e₁ < 2147483647 := by omega
  have low : d₀ + 256 * b₀ = r₀ + 1 + e₀ := by
    simpa [Nat.mod_eq_of_lt hl₁, Nat.mod_eq_of_lt hr₁'] using hlow
  have high : d₁ + 256 * b₁ = r₁ + b₀ + e₁ := by
    simpa [Nat.mod_eq_of_lt hl₂, Nat.mod_eq_of_lt hr₂] using hhigh
  omega

/-- The arithmetic-only wide divider has at most sixteen byte products per
column at width 128. Including one remainder byte and a bounded incoming
carry, the column still lies below the M31 modulus. -/
def directWideColumnConstraint (coefficient incoming digit outgoing : Nat) : Prop :=
  coefficient ≤ 16 * 255 * 255 + 255 ∧ incoming < 65536 ∧
    digit < 256 ∧ outgoing < 65536 ∧
    (coefficient + incoming) % 2147483647 =
      (digit + 256 * outgoing) % 2147483647

theorem direct_wide_column_no_wrap (coefficient incoming digit outgoing : Nat)
    (h : directWideColumnConstraint coefficient incoming digit outgoing) :
    coefficient + incoming = digit + 256 * outgoing := by
  rcases h with ⟨hc, hi, hd, ho, heq⟩
  have hl : coefficient + incoming < 2147483647 := by omega
  have hr : digit + 256 * outgoing < 2147483647 := by omega
  simpa [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hr] using heq

end S31.Gadgets.IntegerDivision
