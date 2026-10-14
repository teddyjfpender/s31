import S31.Gadgets.PcsFri.M31MaskedQuery
import Mathlib.Tactic

/-!
The deterministic eight-word query-batch schedule of the pinned native
Blake2sM31 channel and `drawQueries` loop. This models the already-hashed
raw u32 limbs as an array of eight-lane blocks; it does not assert that
BLAKE2s outputs are independent or that a good set is fixed before drawing.
The Zig loop and selected channel profile require source/native refinement.
-/

namespace S31.Gadgets.PcsFri.NativeQueryBatch

open S31.Gadgets.PcsFri.M31MaskedQuery

/-- Number of eight-word hash blocks consumed to produce `n` raw queries. -/
def blockCount (n : Nat) : Nat := (n + 7) / 8

theorem block_slot_lt (n : Nat) (j : Fin n) :
    j.val / 8 < blockCount n := by
  dsimp [blockCount]
  omega

theorem blockCount_zero : blockCount 0 = 0 := by decide
theorem blockCount_seventy : blockCount 70 = 9 := by decide

/-- The query at raw slot `j` consumes lane `j mod 8` of block `j / 8`.
The bound is derived for every slot, including the final partial block. -/
def rawWord (n : Nat)
    (blocks : Fin (blockCount n) → Fin 8 → Fin rawSize)
    (j : Fin n) : Fin rawSize :=
  blocks ⟨j.val / 8, block_slot_lt n j⟩
    ⟨j.val % 8, by omega⟩

/-- Every ordered raw-word tuple can be placed into the native batch layout;
unused lanes in its last block are filled with zero. This is a deterministic
surjectivity result, not an assertion about the hash output distribution. -/
def blocksOfRaw (n : Nat) (raw : Fin n → Fin rawSize) :
    Fin (blockCount n) → Fin 8 → Fin rawSize :=
  fun block lane =>
    if h : block.val * 8 + lane.val < n then
      raw ⟨block.val * 8 + lane.val, h⟩
    else
      ⟨0, by decide⟩

theorem rawWord_blocksOfRaw (n : Nat) (raw : Fin n → Fin rawSize)
    (j : Fin n) : rawWord n (blocksOfRaw n raw) j = raw j := by
  have hindex : j.val / 8 * 8 + j.val % 8 = j.val := by omega
  simp [rawWord, blocksOfRaw, hindex]

/-- The modeled ordered, repeated raw query slots before Merkle sorting. -/
def queryAt (k n : Nat)
    (blocks : Fin (blockCount n) → Fin 8 → Fin rawSize)
    (j : Fin n) : Fin (size k) :=
  sampleIndex k (rawWord n blocks j).val

/-- For every possible 32-bit lane, the selected block/lane output is the
native M31 reduction followed by Zig's low-bit mask. `k≤31` is the native
u32-shift precondition; the arithmetic equality also covers `k=0`. -/
theorem queryAt_eq_reduced_mask (k n : Nat)
    (blocks : Fin (blockCount n) → Fin 8 → Fin rawSize)
    (j : Fin n) :
    (queryAt k n blocks j).val =
      M31WordReduction.reducedWord (rawWord n blocks j).val &&&
        (size k - 1) := by
  have hword := (rawWord n blocks j).isLt
  have h := native_reduced_index_eq k (rawWord n blocks j).val hword
  have hmask :
      M31WordReduction.reducedWord (rawWord n blocks j).val &&&
          (size k - 1) =
        M31WordReduction.reducedWord (rawWord n blocks j).val % size k := by
    simp [size, Nat.and_two_pow_sub_one_eq_mod]
  unfold queryAt sampleIndex
  exact h.symm.trans hmask.symm

/-- `70` raw queries use blocks 0 through 8; the final requested word is
lane 5 of block 8. The remaining two words of that block are discarded. -/
theorem seventy_last_raw_word
    (blocks : Fin (blockCount 70) → Fin 8 → Fin rawSize) :
    rawWord 70 blocks ⟨69, by decide⟩ =
      blocks ⟨8, by decide⟩ ⟨5, by decide⟩ := by
  rfl

/-- The block schedule's all-good event is exactly the existing ordered
raw-word event. Duplicate positions are kept as separate slots here. -/
theorem all_good_iff_raw_product_event (k n : Nat)
    (blocks : Fin (blockCount n) → Fin 8 → Fin rawSize)
    (good : Finset (Fin (size k))) :
    (fun j : Fin n => rawWord n blocks j) ∈
        QuerySampling.goodSequences n (goodRawFin k good) ↔
      ∀ j : Fin n, queryAt k n blocks j ∈ good := by
  simpa only [queryAt] using
    (raw_good_sequence_iff k n good
      (fun j : Fin n => rawWord n blocks j))

end S31.Gadgets.PcsFri.NativeQueryBatch
