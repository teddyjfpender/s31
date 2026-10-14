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
    (hk : 2 ≤ k) (hmax : k ≤ 30) :
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

/-- One native sparse circle projection discards the next raw bit while
retaining the conjugate bit. Its canonical group index is the square of the
source point's index. This is the index-level peer of the lifted Merkle
projection; it does not assert a native field-coordinate equality. -/
theorem one_sparse_projection_index (k raw : Nat)
    (hk : 2 ≤ k) (hmax : k ≤ 30) :
    canonicalStorageIndex (k - 1)
        (SparseCascadeQueries.projectedCircleRow raw 1) =
      (2 : CircleIndex) * canonicalStorageIndex k raw := by
  let q := raw / 4
  have hrem : raw % 4 < 4 := Nat.mod_lt _ (by omega)
  have hraw : raw = 4 * q + raw % 4 := by
    dsimp [q]
    omega
  have hproj : SparseCascadeQueries.projectedCircleRow raw 1 =
      2 * q + raw % 2 := by
    simp [SparseCascadeQueries.projectedCircleRow,
      SparseCascadeQueries.pairBase, q]
  have hfold := doubled_first_line_pair k q hk hmax
  have hpairSource0 := canonical_storage_pair (k - 1) (2 * q)
  have hpairSource1 := canonical_storage_pair (k - 1) (2 * q + 1)
  have hpairTarget := canonical_storage_pair (k - 2) q
  have hs : k - 1 + 1 = k := by omega
  have ht : k - 2 + 1 = k - 1 := by omega
  rw [hs] at hpairSource0 hpairSource1
  rw [ht] at hpairTarget
  interval_cases hcase : raw % 4
  · have hr : raw = 2 * (2 * q) := by omega
    have hp : SparseCascadeQueries.projectedCircleRow raw 1 = 2 * q := by
      rw [hproj]
      omega
    rw [hp, hr, hpairSource0.1, hpairTarget.1]
    exact hfold.1.symm
  · have hr : raw = 2 * (2 * q) + 1 := by omega
    have hp : SparseCascadeQueries.projectedCircleRow raw 1 = 2 * q + 1 := by
      rw [hproj]
      omega
    rw [hp, hr, hpairSource0.2, hpairTarget.2, mul_neg]
    exact congrArg Neg.neg hfold.1.symm
  · have hr : raw = 2 * (2 * q + 1) := by omega
    have hp : SparseCascadeQueries.projectedCircleRow raw 1 = 2 * q := by
      rw [hproj]
      omega
    rw [hp, hr, hpairSource1.1, hpairTarget.1]
    exact hfold.2.symm
  · have hr : raw = 2 * (2 * q + 1) + 1 := by omega
    have hp : SparseCascadeQueries.projectedCircleRow raw 1 = 2 * q + 1 := by
      rw [hproj]
      omega
    rw [hp, hr, hpairSource1.2, hpairTarget.2, mul_neg]
    exact congrArg Neg.neg hfold.2.symm

theorem sparse_projection_next (raw i : Nat) :
    SparseCascadeQueries.projectedCircleRow raw (i + 1) =
      SparseCascadeQueries.projectedCircleRow
        (SparseCascadeQueries.projectedCircleRow raw i) 1 := by
  simp only [SparseCascadeQueries.projectedCircleRow,
    SparseCascadeQueries.pairBase]
  have hmod : (2 * (raw / 2 ^ (i + 1)) + raw % 2) % 2 = raw % 2 := by
    omega
  have hdiv : (2 * (raw / 2 ^ (i + 1)) + raw % 2) / 4 =
      (raw / 2 ^ (i + 1)) / 2 := by
    omega
  have hfour : 2 ^ (1 + 1) = 4 := by norm_num
  rw [hmod, hfour, hdiv, Nat.div_div_eq_div_mul]
  have hp : 2 ^ (i + 1) * 2 = 2 ^ (i + 1 + 1) := by
    simp [pow_succ, Nat.mul_assoc]
  rw [hp]

/-- At every smaller canonical circle height, the production sparse query
projection corresponds to repeated circle-group squaring. This is an exact
index identity for all valid log sizes, independent of sampled row values.
Native index-to-point arithmetic and Merkle authentication remain separate. -/
theorem sparse_projection_index (k raw : Nat) (hmax : k ≤ 30) :
    ∀ i, i < k →
      canonicalStorageIndex (k - i)
        (SparseCascadeQueries.projectedCircleRow raw i) =
        ((2 ^ i : Nat) : CircleIndex) * canonicalStorageIndex k raw := by
  intro i
  induction i with
  | zero =>
      intro _
      simpa using congrArg (canonicalStorageIndex k)
        (SparseCascadeQueries.projected_circle_row_zero raw)
  | succ i ih =>
      intro hi
      have hi' : i < k := by omega
      have hki : 2 ≤ k - i := by omega
      have hmax' : k - i ≤ 30 := by omega
      have hsize : k - (i + 1) = k - i - 1 := by omega
      calc
        canonicalStorageIndex (k - (i + 1))
            (SparseCascadeQueries.projectedCircleRow raw (i + 1)) =
          canonicalStorageIndex (k - i - 1)
            (SparseCascadeQueries.projectedCircleRow
              (SparseCascadeQueries.projectedCircleRow raw i) 1) := by
                rw [hsize, sparse_projection_next]
        _ = (2 : CircleIndex) *
            canonicalStorageIndex (k - i)
              (SparseCascadeQueries.projectedCircleRow raw i) :=
                one_sparse_projection_index (k - i) _ hki hmax'
        _ = (2 : CircleIndex) *
            (((2 ^ i : Nat) : CircleIndex) * canonicalStorageIndex k raw) := by
                rw [ih hi']
        _ = ((2 ^ (i + 1) : Nat) : CircleIndex) *
            canonicalStorageIndex k raw := by
              simp [pow_succ, mul_assoc, mul_comm]

end S31.Gadgets.PcsFri.CanonicalCircleFoldIndex
