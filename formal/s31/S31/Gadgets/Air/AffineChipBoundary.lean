import Mathlib.Tactic

/-!
The source-level affine-square step accepted by S31's direct private chip is
`x ↦ c * (a*x + b)^2 + d`. The chip itself only evaluates `s ↦ s^2 + k`.
These lemmas justify the algebraic change of coordinates for every round and
show exactly why the compiler must reject zero scales. They do not establish
the production compiler's gate emission or the LogUp boundary argument.
-/

namespace S31.Gadgets.Air.AffineChipBoundary

variable {F : Type*} [Field F]

def scale (a c : F) : F := c * a * a
def offset (a b c : F) : F := c * a * b
def encode (a b c x : F) : F := scale a c * x + offset a b c
def sourceStep (a b c d x : F) : F := c * (a * x + b)^2 + d
def chipConstant (a b c d : F) : F := scale a c * d + offset a b c
def chipStep (a b c d s : F) : F := s^2 + chipConstant a b c d

/-- The chip computes one source step in the encoded coordinates. -/
theorem encode_sourceStep (a b c d x : F) :
    encode a b c (sourceStep a b c d x) =
      chipStep a b c d (encode a b c x) := by
  unfold encode sourceStep chipStep chipConstant scale offset
  ring

/-- Both nonzero scales are needed to recover the source state. -/
theorem scale_ne_zero (a c : F) (ha : a ≠ 0) (hc : c ≠ 0) :
    scale a c ≠ 0 := by
  unfold scale
  exact mul_ne_zero (mul_ne_zero hc ha) ha

def decode (a b c s : F) : F :=
  (s - offset a b c) / scale a c

theorem decode_encode (a b c x : F) (ha : a ≠ 0) (hc : c ≠ 0) :
    decode a b c (encode a b c x) = x := by
  unfold decode encode
  field_simp [scale_ne_zero a c ha hc]
  ring

theorem encode_decode (a b c s : F) (ha : a ≠ 0) (hc : c ≠ 0) :
    encode a b c (decode a b c s) = s := by
  unfold decode encode
  field_simp [scale_ne_zero a c ha hc]
  ring

def sourceRounds (a b c d : F) : Nat → F → F
  | 0, x => x
  | n + 1, x => sourceStep a b c d (sourceRounds a b c d n x)

def chipRounds (a b c d : F) : Nat → F → F
  | 0, s => s
  | n + 1, s => chipStep a b c d (chipRounds a b c d n s)

/-- Every length of the chip recurrence equals the source recurrence after
encoding the initial state. This is a functional statement; it assumes the
chip rows and boundary lookup actually enforce that recurrence. -/
theorem encode_sourceRounds (a b c d x : F) (n : Nat) :
    encode a b c (sourceRounds a b c d n x) =
      chipRounds a b c d n (encode a b c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sourceRounds, chipRounds, encode_sourceStep, ih]

theorem decode_chipRounds (a b c d x : F) (n : Nat)
    (ha : a ≠ 0) (hc : c ≠ 0) :
    decode a b c (chipRounds a b c d n (encode a b c x)) =
      sourceRounds a b c d n x := by
  rw [← encode_sourceRounds, decode_encode a b c _ ha hc]

end S31.Gadgets.Air.AffineChipBoundary
