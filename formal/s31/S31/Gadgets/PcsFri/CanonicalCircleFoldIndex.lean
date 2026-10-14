import S31.Gadgets.PcsFri.CanonicalCircleLaurentRows

/-!
The group-index part of two canonical FRI folds. Adjacent bit-reversed circle
rows use opposite signs of one half-coset index. The first line domain retains
that half-coset; its next line fold doubles the index and lands in the next
canonical half-coset. Native point arithmetic, line-coordinate evaluation,
authenticated rows and FRI soundness are separate.
-/

namespace S31.Gadgets.PcsFri.CanonicalCircleFoldIndex

open S31.Gadgets.PcsFri.CanonicalCircleLaurentRows

/-- The first circle-to-line fold reads one conjugate pair and writes the
line row at the shared half-coset index. The line domain itself is the native
`LineDomain.fromCircleDomain` half-coset, so there is no doubling yet. -/
theorem circle_pair_first_line_index (k row : Nat) (hk : 1 ≤ k) :
    canonicalStorageIndex k (2 * row) =
      canonicalHalfIndex k (bitReverse (k - 1) row) ∧
    canonicalStorageIndex k (2 * row + 1) =
      -canonicalHalfIndex k (bitReverse (k - 1) row) := by
  have h := canonical_storage_pair (k - 1) row
  simpa [show k - 1 + 1 = k by omega] using h

/-- The following line-to-line fold calls `LineDomain.double()`. Its group
index is twice the first line row's index. -/
theorem doubled_half_index (k natural : Nat)
    (hk : 2 ≤ k) (hmax : k ≤ 30) :
    (2 : CircleIndex) * canonicalHalfIndex k natural =
      canonicalHalfIndex (k - 1) natural := by
  have hfirst : 2 * 2 ^ (30 - k) = 2 ^ (30 - (k - 1)) := by
    have he : 30 - (k - 1) = (30 - k) + 1 := by omega
    rw [he, pow_succ]
    omega
  have hstep : 2 * 2 ^ (32 - k) = 2 ^ (32 - (k - 1)) := by
    have he : 32 - (k - 1) = (32 - k) + 1 := by omega
    rw [he, pow_succ]
    omega
  simp only [canonicalHalfIndex]
  calc
    (2 : CircleIndex) *
        (((2 ^ (30 - k) : Nat) : CircleIndex) +
          (natural : CircleIndex) * ((2 ^ (32 - k) : Nat) : CircleIndex)) =
      ((2 * 2 ^ (30 - k) : Nat) : CircleIndex) +
        (natural : CircleIndex) * ((2 * 2 ^ (32 - k) : Nat) : CircleIndex) := by
          push_cast
          ring
    _ = _ := by rw [hfirst, hstep]

theorem half_index_period (k natural : Nat)
    (hk : 1 ≤ k) (hmax : k ≤ 30) :
    canonicalHalfIndex k (natural + 2 ^ (k - 1)) =
      canonicalHalfIndex k natural := by
  have hperiod : 2 ^ (k - 1) * 2 ^ (32 - k) = 2 ^ 31 := by
    rw [← pow_add]
    congr 1
    omega
  have hzero : (((2 ^ 31 : Nat) : CircleIndex)) = 0 :=
    ZMod.natCast_self _
  have hproduct :
      (((2 ^ (k - 1) : Nat) : CircleIndex)) *
        (((2 ^ (32 - k) : Nat) : CircleIndex)) = 0 := by
    rw [← Nat.cast_mul, hperiod]
    exact hzero
  simp only [canonicalHalfIndex, Nat.cast_add, add_mul]
  rw [hproduct]
  ring

/-- Both adjacent first-line rows double to the same second-line index,
at the line row selected by integer division by two. -/
theorem doubled_first_line_pair (k row : Nat)
    (hk : 3 ≤ k) (hmax : k ≤ 30) :
    (2 : CircleIndex) *
        canonicalHalfIndex k (bitReverse (k - 1) (2 * row)) =
      canonicalHalfIndex (k - 1) (bitReverse (k - 2) row) ∧
    (2 : CircleIndex) *
        canonicalHalfIndex k (bitReverse (k - 1) (2 * row + 1)) =
      canonicalHalfIndex (k - 1) (bitReverse (k - 2) row) := by
  have heven : bitReverse (k - 1) (2 * row) =
      bitReverse (k - 2) row := by
    simpa [show k - 2 + 1 = k - 1 by omega] using
      bitReverse_even (k - 2) row
  have hodd : bitReverse (k - 1) (2 * row + 1) =
      2 ^ (k - 2) + bitReverse (k - 2) row := by
    simpa [show k - 2 + 1 = k - 1 by omega] using
      bitReverse_odd (k - 2) row
  have hnext : 2 ≤ k := by omega
  constructor
  · rw [heven]
    exact doubled_half_index k _ hnext hmax
  · rw [hodd, doubled_half_index k _ hnext hmax]
    have hp : k - 1 - 1 = k - 2 := by omega
    simpa [hp, Nat.add_comm] using
      half_index_period (k - 1) (bitReverse (k - 2) row) (by omega) (by omega)

/-- Starting from either member of the source circle pair, doubling its
group index yields opposite signs of the second line domain's index. The
actual line coordinate is the x coordinate and ignores this sign. -/
theorem doubled_storage_pair (k row : Nat)
    (hk : 2 ≤ k) (hmax : k ≤ 30) :
    (2 : CircleIndex) * canonicalStorageIndex k (2 * row) =
      canonicalHalfIndex (k - 1) (bitReverse (k - 1) row) ∧
    (2 : CircleIndex) * canonicalStorageIndex k (2 * row + 1) =
      -canonicalHalfIndex (k - 1) (bitReverse (k - 1) row) := by
  have hpair := canonical_storage_pair (k - 1) row
  have hk' : k - 1 + 1 = k := by omega
  rw [hk'] at hpair
  constructor
  · rw [hpair.1]
    exact doubled_half_index k _ hk hmax
  · rw [hpair.2, mul_neg]
    exact congrArg Neg.neg (doubled_half_index k _ hk hmax)

end S31.Gadgets.PcsFri.CanonicalCircleFoldIndex
