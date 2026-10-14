import S31.Gadgets.PcsFri.CircleBasisDot
import S31.Gadgets.PcsFri.CircleBasisM31Embedding
import Mathlib.Data.List.GetD

/-!
# Power-of-two circle basis fill

The native low basis and high-block basis are built in increasing index order.
This module proves an arbitrary-length fill invariant from a predecessor
schedule that clears one active bit. The premise that the native bitwise
instructions realize the schedule is kept explicit; a source-bound Zig test
checks it exhaustively for the selected k=10 and k=16 sizes.
-/

namespace S31.Gadgets.PcsFri.CircleBasisPrefixRecurrence

open CircleBasisDot

variable {E : Type*} [Field E]

/-- Model one write per index, reading only a previous cell. -/
def fillPrefix (previous bit : Nat → Nat) (factor : Nat → E) : Nat → List E
  | 0 => []
  | n + 1 =>
      let cells := fillPrefix previous bit factor n
      cells ++ [if n = 0 then 1 else cells.getD (previous n) 0 * factor (bit n)]

theorem fillPrefix_length (previous bit : Nat → Nat) (factor : Nat → E)
    (n : Nat) : (fillPrefix previous bit factor n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fillPrefix, ih]

theorem basisWeight_zero (factor : Nat → E) (k : Nat) :
    basisWeight factor k 0 = 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [basisWeight, ih]

/-- The exact prefix invariant for any coefficient count. The schedule
premises make clear what must be established about native bit-clearing and
trailing-zero operations before treating this as Zig loop correctness. -/
theorem fillPrefix_eq_basisWeight
    (factor : Nat → E) (k : Nat) (previous bit : Nat → Nat)
    (hprevious : ∀ j, 0 < j → j < 2 ^ k → previous j < j)
    (hstep : ∀ j, 0 < j → j < 2 ^ k →
      basisWeight factor k j =
        basisWeight factor k (previous j) * factor (bit j))
    (n : Nat) (hn : n ≤ 2 ^ k) (j : Nat) (hj : j < n) :
    (fillPrefix previous bit factor n).getD j 0 = basisWeight factor k j := by
  induction n generalizing j with
  | zero => omega
  | succ n ih =>
      by_cases hjold : j < n
      · rw [fillPrefix, List.getD_append _ _ _ _ (by
          simpa [fillPrefix_length] using hjold)]
        exact ih (by omega) j hjold
      · have hjeq : j = n := by omega
        subst j
        have hlast :
            (fillPrefix previous bit factor (n + 1)).getD n 0 =
              if n = 0 then 1 else
                (fillPrefix previous bit factor n).getD (previous n) 0 *
                  factor (bit n) := by
          rw [fillPrefix, List.getD_append_right _ _ 0 n (by
            simp [fillPrefix_length])]
          simp [fillPrefix_length]
        rw [hlast]
        by_cases hnzero : n = 0
        · subst n
          simp [basisWeight_zero]
        · simp only [hnzero, ↓reduceIte]
          have hnpos : 0 < n := Nat.pos_of_ne_zero hnzero
          rw [ih (by omega) (previous n) (hprevious n hnpos (by omega))]
          exact (hstep n hnpos (by omega)).symm

private theorem weight_low (factor : Nat → E) (k j : Nat)
    (hj : j < 2 ^ k) :
    basisWeight factor (k + 1) j = basisWeight factor k j := by
  simp [basisWeight, Nat.mod_eq_of_lt hj, hj]

private theorem weight_high (factor : Nat → E) (k j : Nat)
    (hj : j < 2 ^ k) :
    basisWeight factor (k + 1) (j + 2 ^ k) =
      basisWeight factor k j * factor k := by
  have hnlt : ¬ j + 2 ^ k < 2 ^ k := by omega
  simp [basisWeight, Nat.add_mod_right, Nat.mod_eq_of_lt hj, hnlt]

/-- Exact cell factorization for the native 256-cell low basis and its high
block basis. Stated for any split so the source log 10 and 16 cases share one
proof. The native packed multiplication that materializes the product is a
separate implementation obligation. -/
theorem basisWeight_block
    (factor : Nat → E) (low high offset block : Nat)
    (hoffset : offset < 2 ^ low) (hblock : block < 2 ^ high) :
    basisWeight factor (low + high) (offset + block * 2 ^ low) =
      basisWeight factor low offset *
        basisWeight (fun r => factor (low + r)) high block := by
  induction high generalizing block with
  | zero =>
      have : block = 0 := by omega
      subst block
      simp [basisWeight]
  | succ high ih =>
      let shifted : Nat → E := fun r => factor (low + r)
      have hpow : 2 ^ (low + high) = 2 ^ high * 2 ^ low := by
        rw [pow_add]; ring
      by_cases hsmall : block < 2 ^ high
      · have hindex : offset + block * 2 ^ low < 2 ^ (low + high) := by
          rw [hpow]
          calc
            offset + block * 2 ^ low < 2 ^ low + block * 2 ^ low :=
              Nat.add_lt_add_right hoffset _
            _ = (block + 1) * 2 ^ low := by ring
            _ ≤ 2 ^ high * 2 ^ low :=
              Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hsmall)
        calc
          basisWeight factor (low + (high + 1))
              (offset + block * 2 ^ low) =
            basisWeight factor (low + high)
              (offset + block * 2 ^ low) := by
                rw [show low + (high + 1) = (low + high) + 1 by omega]
                exact weight_low factor (low + high) _ hindex
          _ = basisWeight factor low offset *
              basisWeight shifted high block := ih block hsmall
          _ = basisWeight factor low offset *
              basisWeight shifted (high + 1) block := by
                rw [weight_low shifted high block hsmall]
      · let b := block - 2 ^ high
        have hb : b < 2 ^ high := by omega
        have hblock_eq : block = b + 2 ^ high := by omega
        have hinner : offset + b * 2 ^ low < 2 ^ (low + high) := by
          rw [hpow]
          calc
            offset + b * 2 ^ low < 2 ^ low + b * 2 ^ low :=
              Nat.add_lt_add_right hoffset _
            _ = (b + 1) * 2 ^ low := by ring
            _ ≤ 2 ^ high * 2 ^ low :=
              Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hb)
        have hindex : offset + block * 2 ^ low =
            (offset + b * 2 ^ low) + 2 ^ (low + high) := by
          rw [hblock_eq, hpow]
          ring
        calc
          basisWeight factor (low + (high + 1))
              (offset + block * 2 ^ low) =
            basisWeight factor (low + high)
              (offset + b * 2 ^ low) * factor (low + high) := by
                rw [show low + (high + 1) = (low + high) + 1 by omega,
                  hindex]
                exact weight_high factor (low + high) _ hinner
          _ = basisWeight factor low offset *
              basisWeight shifted high b * shifted high := by
                rw [ih b hb]
          _ = basisWeight factor low offset *
              basisWeight shifted (high + 1) block := by
                rw [hblock_eq, show b + 2 ^ high = b + 2 ^ high by rfl,
                  weight_high shifted high b hb]
                ring

/-- Clearing a single active bit has the expected multiplicative effect on
the circle basis. The quotient `q` contains all bits above `r`; the low
`r+1` bits of the predecessor are zero. -/
theorem basisWeight_single_bit_step
    (factor : Nat → E) (k r q : Nat) (hr : r < k)
    (hq : q < 2 ^ (k - (r + 1))) :
    basisWeight factor k (q * 2 ^ (r + 1) + 2 ^ r) =
      basisWeight factor k (q * 2 ^ (r + 1)) * factor r := by
  let high := k - (r + 1)
  have hk : r + 1 + high = k := by dsimp [high]; omega
  have hradius : 2 ^ r < 2 ^ (r + 1) := by
    rw [pow_succ]
    have hp : 0 < 2 ^ r := pow_pos (by norm_num) _
    omega
  have htop : basisWeight factor (r + 1) (2 ^ r) = factor r := by
    simp [basisWeight, basisWeight_zero]
  have hbottom : basisWeight factor (r + 1) 0 = 1 :=
    basisWeight_zero factor (r + 1)
  have hplus := basisWeight_block factor (r + 1) high (2 ^ r) q
    hradius (by simpa [high] using hq)
  have hminus := basisWeight_block factor (r + 1) high 0 q
    (pow_pos (by norm_num) _) (by simpa [high] using hq)
  rw [hk, htop] at hplus
  rw [hk, hbottom, one_mul, zero_add] at hminus
  rw [Nat.add_comm] at hplus
  rw [hplus, hminus]
  ring

/-- A certificate for the exact bit-clearing schedule: each positive index
is an odd multiple of `2^bit`, and its predecessor clears that bit. Native
`index & (index-1)` and `ctz(index)` are checked against these equations at
the selected finite sizes by the Zig fixture. -/
structure BitSchedule (k : Nat) where
  previous : Nat → Nat
  bit : Nat → Nat
  quotient : Nat → Nat
  bit_lt : ∀ j, 0 < j → j < 2 ^ k → bit j < k
  quotient_lt : ∀ j, 0 < j → j < 2 ^ k →
    quotient j < 2 ^ (k - (bit j + 1))
  previous_eq : ∀ j, 0 < j → j < 2 ^ k →
    previous j = quotient j * 2 ^ (bit j + 1)
  index_eq : ∀ j, 0 < j → j < 2 ^ k →
    j = previous j + 2 ^ (bit j)

theorem BitSchedule.previous_lt (schedule : BitSchedule k)
    (j : Nat) (hj : 0 < j) (hbound : j < 2 ^ k) :
    schedule.previous j < j := by
  have hbit := schedule.index_eq j hj hbound
  have hpositive : 0 < 2 ^ (schedule.bit j) := pow_pos (by norm_num) _
  omega

theorem BitSchedule.weight_step (schedule : BitSchedule k)
    (factor : Nat → E) (j : Nat) (hj : 0 < j) (hbound : j < 2 ^ k) :
    basisWeight factor k j =
      basisWeight factor k (schedule.previous j) *
        factor (schedule.bit j) := by
  calc
    basisWeight factor k j =
        basisWeight factor k
          (schedule.previous j + 2 ^ schedule.bit j) := by
            rw [← schedule.index_eq j hj hbound]
    _ = basisWeight factor k
          (schedule.quotient j * 2 ^ (schedule.bit j + 1) +
            2 ^ schedule.bit j) := by
              rw [schedule.previous_eq j hj hbound]
    _ = basisWeight factor k
          (schedule.quotient j * 2 ^ (schedule.bit j + 1)) *
            factor (schedule.bit j) :=
          basisWeight_single_bit_step factor k (schedule.bit j)
            (schedule.quotient j)
            (schedule.bit_lt j hj hbound)
            (schedule.quotient_lt j hj hbound)
    _ = basisWeight factor k (schedule.previous j) *
          factor (schedule.bit j) := by
            rw [schedule.previous_eq j hj hbound]

theorem certifiedPrefix_eq_basisWeight
    (factor : Nat → E) (k : Nat) (schedule : BitSchedule k)
    (n : Nat) (hn : n ≤ 2 ^ k) (j : Nat) (hj : j < n) :
    (fillPrefix schedule.previous schedule.bit factor n).getD j 0 =
      basisWeight factor k j := by
  exact fillPrefix_eq_basisWeight factor k schedule.previous schedule.bit
    (schedule.previous_lt) (schedule.weight_step factor) n hn j hj

theorem blockIndex_lt (low high offset block : Nat)
    (hoffset : offset < 2 ^ low) (hblock : block < 2 ^ high) :
    offset + block * 2 ^ low < 2 ^ (low + high) := by
  rw [pow_add, Nat.mul_comm (2 ^ low) (2 ^ high)]
  calc
    offset + block * 2 ^ low < 2 ^ low + block * 2 ^ low :=
      Nat.add_lt_add_right hoffset _
    _ = (block + 1) * 2 ^ low := by ring
    _ ≤ 2 ^ high * 2 ^ low :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hblock)

theorem filled_block_lengths (factor : Nat → E)
    (low high : Nat) (previousLow bitLow previousHigh bitHigh : Nat → Nat) :
    (fillPrefix previousLow bitLow factor (2 ^ low)).length *
        (fillPrefix previousHigh bitHigh (fun r => factor (low + r))
          (2 ^ high)).length = 2 ^ (low + high) := by
  simp [fillPrefix_length, pow_add]

/-- A full cell at any power-of-two size is the product of one low cell and
one high block cell, if both strictly earlier-cell schedules implement the
specified subset-product recurrence. This is the mathematical target for
the native packed high-block multiplication. -/
theorem filled_block_cell_eq_basisWeight
    (factor : Nat → E) (low high offset block : Nat)
    (previousLow bitLow previousHigh bitHigh : Nat → Nat)
    (hoffset : offset < 2 ^ low) (hblock : block < 2 ^ high)
    (hpreviousLow : ∀ j, 0 < j → j < 2 ^ low → previousLow j < j)
    (hstepLow : ∀ j, 0 < j → j < 2 ^ low →
      basisWeight factor low j =
        basisWeight factor low (previousLow j) * factor (bitLow j))
    (hpreviousHigh : ∀ j, 0 < j → j < 2 ^ high → previousHigh j < j)
    (hstepHigh : ∀ j, 0 < j → j < 2 ^ high →
      basisWeight (fun r => factor (low + r)) high j =
        basisWeight (fun r => factor (low + r)) high (previousHigh j) *
          factor (low + bitHigh j)) :
    (fillPrefix previousLow bitLow factor (2 ^ low)).getD offset 0 *
      (fillPrefix previousHigh bitHigh (fun r => factor (low + r))
        (2 ^ high)).getD block 0 =
      basisWeight factor (low + high) (offset + block * 2 ^ low) := by
  rw [fillPrefix_eq_basisWeight factor low previousLow bitLow
      hpreviousLow hstepLow (2 ^ low) le_rfl offset hoffset,
    fillPrefix_eq_basisWeight (fun r => factor (low + r)) high
      previousHigh bitHigh hpreviousHigh hstepHigh
      (2 ^ high) le_rfl block hblock]
  exact (basisWeight_block factor low high offset block hoffset hblock).symm

/-- Column-major block traversal of a full coefficient word. The two lists
are the exact low and high basis arrays; `getD` is harmless only after the
array-length and in-range hypotheses below are discharged. -/
def filledBlockDot
    {F : Type*} [Field F] [Algebra F E]
    (low high : Nat) (coefficient : Nat → F)
    (lowCells highCells : List E) : E :=
  ∑ block ∈ Finset.range (2 ^ high),
    ∑ offset ∈ Finset.range (2 ^ low),
      (algebraMap F E) (coefficient (offset + block * 2 ^ low)) *
        (lowCells.getD offset 0 * highCells.getD block 0)

theorem filledBlockDot_eq_basisDot
    {F : Type*} [Field F] [Algebra F E]
    (factor : Nat → E) (low high : Nat) (coefficient : Nat → F)
    (lowCells highCells : List E)
    (_hlowLength : lowCells.length = 2 ^ low)
    (_hhighLength : highCells.length = 2 ^ high)
    (hlow : ∀ offset < 2 ^ low,
      lowCells.getD offset 0 = basisWeight factor low offset)
    (hhigh : ∀ block < 2 ^ high,
      highCells.getD block 0 =
        basisWeight (fun r => factor (low + r)) high block) :
    filledBlockDot low high coefficient lowCells highCells =
      basisDot factor (low + high) coefficient := by
  calc
    filledBlockDot low high coefficient lowCells highCells =
        ∑ block ∈ Finset.range (2 ^ high),
          basisDot factor low
            (fun offset => coefficient (offset + block * 2 ^ low)) *
            basisWeight (fun r => factor (low + r)) high block := by
              unfold filledBlockDot
              apply Finset.sum_congr rfl
              intro block hb
              rw [basisDot, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro offset ho
              rw [hlow offset (Finset.mem_range.mp ho),
                hhigh block (Finset.mem_range.mp hb)]
              ring
    _ = basisDot factor (low + high) coefficient :=
      (basisDot_split factor low high coefficient).symm

/-- The full native-shaped fill/dot is the mathematical circle basis dot
for any low/high split and any coefficient word, conditional on each native
bit schedule realizing the stated predecessor and factor recurrence. -/
theorem filledPrefixDot_eq_basisDot
    {F : Type*} [Field F] [Algebra F E]
    (factor : Nat → E) (low high : Nat) (coefficient : Nat → F)
    (previousLow bitLow previousHigh bitHigh : Nat → Nat)
    (hpreviousLow : ∀ j, 0 < j → j < 2 ^ low → previousLow j < j)
    (hstepLow : ∀ j, 0 < j → j < 2 ^ low →
      basisWeight factor low j =
        basisWeight factor low (previousLow j) * factor (bitLow j))
    (hpreviousHigh : ∀ j, 0 < j → j < 2 ^ high → previousHigh j < j)
    (hstepHigh : ∀ j, 0 < j → j < 2 ^ high →
      basisWeight (fun r => factor (low + r)) high j =
        basisWeight (fun r => factor (low + r)) high (previousHigh j) *
          factor (low + bitHigh j)) :
    filledBlockDot low high coefficient
      (fillPrefix previousLow bitLow factor (2 ^ low))
      (fillPrefix previousHigh bitHigh (fun r => factor (low + r))
        (2 ^ high)) = basisDot factor (low + high) coefficient := by
  apply filledBlockDot_eq_basisDot factor low high coefficient
  · exact fillPrefix_length previousLow bitLow factor (2 ^ low)
  · exact fillPrefix_length previousHigh bitHigh
      (fun r => factor (low + r)) (2 ^ high)
  · intro offset hoffset
    exact fillPrefix_eq_basisWeight factor low previousLow bitLow
      hpreviousLow hstepLow (2 ^ low) le_rfl offset hoffset
  · intro block hblock
    exact fillPrefix_eq_basisWeight (fun r => factor (low + r)) high
      previousHigh bitHigh hpreviousHigh hstepHigh
      (2 ^ high) le_rfl block hblock

/-- The end-to-end mathematical refinement needs only two valid bit
schedule certificates. Their implementation by native `ctz`/bit-clearing is
checked separately at the concrete finite widths. -/
theorem filledCertifiedDot_eq_basisDot
    {F : Type*} [Field F] [Algebra F E]
    (factor : Nat → E) (low high : Nat) (coefficient : Nat → F)
    (lowSchedule : BitSchedule low) (highSchedule : BitSchedule high) :
    filledBlockDot low high coefficient
      (fillPrefix lowSchedule.previous lowSchedule.bit factor (2 ^ low))
      (fillPrefix highSchedule.previous highSchedule.bit
        (fun r => factor (low + r)) (2 ^ high)) =
      basisDot factor (low + high) coefficient := by
  exact filledPrefixDot_eq_basisDot factor low high coefficient
    lowSchedule.previous lowSchedule.bit highSchedule.previous highSchedule.bit
    lowSchedule.previous_lt (lowSchedule.weight_step factor)
    highSchedule.previous_lt
    (highSchedule.weight_step (fun r => factor (low + r)))

/-- A length-indexed M31 coefficient word gives an exact Laurent value after
the independently certified low/high basis fill. This is conditional on the
actual native FFT array and factor word corresponding to these inputs. -/
theorem certifiedM31Word_eq_laurent
    (z : CircleBasisM31Embedding.QM31ˣ) (low high : Nat)
    (coefficients : Fin (2 ^ (low + high)) → CircleBasisM31Embedding.M31)
    (lowSchedule : BitSchedule low) (highSchedule : BitSchedule high) :
    let word := List.ofFn coefficients
    let factors := CircleRecursiveBasisDegree.nativeFactorValue
      (CircleLaurentDegree.fourierX z.val z⁻¹.val)
      (CircleLaurentDegree.fourierY
        ((algebraMap CircleBasisM31Embedding.CM31
          CircleBasisM31Embedding.QM31) ConcreteCircleMinpoly.imaginary)
        z.val z⁻¹.val)
    filledBlockDot low high
      (fun j => CircleBasisM31Embedding.m31ToCM31 (word.getD j 0))
      (fillPrefix lowSchedule.previous lowSchedule.bit factors (2 ^ low))
      (fillPrefix highSchedule.previous highSchedule.bit
        (fun r => factors (low + r)) (2 ^ high)) =
      LaurentPolynomial.eval₂
        (algebraMap CircleBasisM31Embedding.CM31 CircleBasisM31Embedding.QM31)
        z (CircleRecursiveBasisDegree.coefficientWord
          ConcreteCircleMinpoly.imaginary (low + high)
          (word.map CircleBasisM31Embedding.m31ToCM31)) := by
  dsimp
  calc
    _ = CircleBasisDot.basisDot
      (CircleRecursiveBasisDegree.nativeFactorValue
        (CircleLaurentDegree.fourierX z.val z⁻¹.val)
        (CircleLaurentDegree.fourierY
          ((algebraMap CircleBasisM31Embedding.CM31
            CircleBasisM31Embedding.QM31) ConcreteCircleMinpoly.imaginary)
          z.val z⁻¹.val))
      (low + high)
      (fun j => CircleBasisM31Embedding.m31ToCM31
        ((List.ofFn coefficients).getD j 0)) :=
          filledCertifiedDot_eq_basisDot _ low high _ lowSchedule highSchedule
    _ = _ := CircleBasisM31Embedding.embedded_m31_basisDot_eq_laurent
      z (low + high) (List.ofFn coefficients)

end S31.Gadgets.PcsFri.CircleBasisPrefixRecurrence
