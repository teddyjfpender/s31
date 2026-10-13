import S31.Gadgets.PcsFri.MultiproofCommittedColumns
import Mathlib.Tactic

/-!
Parametric index bridge for the compact row-tiled CPU Merkle committer.
The two branches match `tiled_commit.zig`: a column wider than the tile
contributes a contiguous coset block, while a smaller column contributes its
pair of values for the tile. The theorems quantify over all valid heights,
tile numbers, offsets, columns and abstract leaf/parent hashes. Native Zig
source/binary refinement and coefficient FFT semantics are separate premises.
-/

namespace S31.Gadgets.PcsFri.MultiproofCompactTiles

open S31.Gadgets.PcsFri.MerkleOpening
open S31.Gadgets.PcsFri.MultiproofCommittedColumns

theorem projection_tile (height columnLog tileLog tile offset : Nat)
    (column_le : columnLog ≤ height)
    (tile_le : tileLog ≤ height)
    (block_valid : height - columnLog + 1 ≤ tileLog) :
    projectedPosition height columnLog (tile * 2 ^ tileLog + offset) =
      tile * 2 ^ (tileLog - (height - columnLog)) +
        projectedPosition tileLog (tileLog - (height - columnLog)) offset := by
  let d := height - columnLog + 1
  let j := tileLog - (height - columnLog)
  have dj : 1 ≤ j := by dsimp [j]; omega
  have jm : j ≤ tileLog := by dsimp [j]; omega
  have hd : 1 ≤ d := by dsimp [d]; omega
  have sum : tileLog = d + (j - 1) := by dsimp [d, j]; omega
  have small_shift : tileLog - j + 1 = d := by omega
  have powtile : 2 ^ tileLog = 2 ^ d * 2 ^ (j - 1) := by
    rw [sum, pow_add]
  have powblock : 2 ^ j = 2 * 2 ^ (j - 1) := by
    calc
      2 ^ j = 2 ^ ((j - 1) + 1) := by congr 1; omega
      _ = 2 * 2 ^ (j - 1) := by rw [pow_succ]; ring
  have div_tile : (tile * 2 ^ tileLog + offset) / 2 ^ d =
      tile * 2 ^ (j - 1) + offset / 2 ^ d := by
    rw [powtile]
    have hmul : tile * (2 ^ d * 2 ^ (j - 1)) = 2 ^ d * (tile * 2 ^ (j - 1)) := by ring
    rw [hmul]
    exact Nat.mul_add_div (by positivity) (tile * 2 ^ (j - 1)) offset
  have mod_tile : (tile * 2 ^ tileLog + offset) % 2 = offset % 2 := by
    have ht : 2 ∣ tile * 2 ^ tileLog := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : tileLog ≠ 0)
      refine ⟨tile * 2 ^ n, ?_⟩
      simp [pow_succ]
      ring
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd ht]
    simp
  rw [projectedPosition, if_neg (Nat.not_lt.mpr column_le)]
  rw [projectedPosition, if_neg (by omega)]
  change 2 * ((tile * 2 ^ tileLog + offset) / 2 ^ d) +
    (tile * 2 ^ tileLog + offset) % 2 =
    tile * 2 ^ j + (2 * (offset / 2 ^ (tileLog - j + 1)) + offset % 2)
  rw [div_tile, mod_tile, small_shift, powblock]
  ring

theorem projection_tile_small (height columnLog tileLog tile offset : Nat)
    (column_le : columnLog ≤ height)
    (tile_positive : 0 < tileLog)
    (small : columnLog + tileLog ≤ height)
    (offset_lt : offset < 2 ^ tileLog) :
    projectedPosition height columnLog (tile * 2 ^ tileLog + offset) =
      2 * (tile / 2 ^ (height - tileLog - columnLog + 1)) + offset % 2 := by
  let d := height - columnLog + 1
  let k := height - tileLog - columnLog + 1
  have hk : 0 < k := by dsimp [k]; omega
  have sum : d = tileLog + k := by dsimp [d, k]; omega
  have powd : 2 ^ d = 2 ^ tileLog * 2 ^ k := by rw [sum, pow_add]
  have qdiv : (tile * 2 ^ tileLog + offset) / 2 ^ tileLog = tile := by
    have hmul : tile * 2 ^ tileLog = 2 ^ tileLog * tile := by ring
    rw [hmul]
    rw [Nat.mul_add_div (by positivity)]
    have : offset / 2 ^ tileLog = 0 := Nat.div_eq_zero_iff.mpr (Or.inr offset_lt)
    simp [this]
  have div_tile : (tile * 2 ^ tileLog + offset) / 2 ^ d = tile / 2 ^ k := by
    rw [powd, ← Nat.div_div_eq_div_mul, qdiv]
  have mod_tile : (tile * 2 ^ tileLog + offset) % 2 = offset % 2 := by
    have ht : 2 ∣ tile * 2 ^ tileLog := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : tileLog ≠ 0)
      refine ⟨tile * 2 ^ n, ?_⟩
      simp [pow_succ]
      ring
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd ht]
    simp
  rw [projectedPosition, if_neg (Nat.not_lt.mpr column_le)]
  change 2 * ((tile * 2 ^ tileLog + offset) / 2 ^ d) +
    (tile * 2 ^ tileLog + offset) % 2 = 2 * (tile / 2 ^ k) + offset % 2
  rw [div_tile, mod_tile]

/-- Index read by one tiled leaf at offset `offset` within tile `tile`.
The first branch is `tile * 2^blockLog + projectedPosition tileLog blockLog
offset`, where `blockLog = tileLog - (height-columnLog)`; the second is the
small column's two-value pair offset. -/
def tiledPosition (height columnLog tileLog tile offset : Nat) : Nat :=
  if height - columnLog + 1 ≤ tileLog then
    tile * 2 ^ (tileLog - (height - columnLog)) +
      projectedPosition tileLog (tileLog - (height - columnLog)) offset
  else
    2 * (tile / 2 ^ (height - tileLog - columnLog + 1)) + offset % 2

/-- Both tile branches read exactly the word read by the complete lifted
tree. `offset < 2^tileLog` names a valid position within one tile. -/
theorem tiledPosition_eq_projected (height columnLog tileLog tile offset : Nat)
    (column_le : columnLog ≤ height)
    (tile_positive : 0 < tileLog)
    (tile_le : tileLog ≤ height)
    (offset_lt : offset < 2 ^ tileLog) :
    tiledPosition height columnLog tileLog tile offset =
      projectedPosition height columnLog (tile * 2 ^ tileLog + offset) := by
  by_cases large : height - columnLog + 1 ≤ tileLog
  · simp only [tiledPosition, if_pos large]
    exact (projection_tile height columnLog tileLog tile offset column_le tile_le large).symm
  · have small : columnLog + tileLog ≤ height := by omega
    simp only [tiledPosition, if_neg large]
    exact (projection_tile_small height columnLog tileLog tile offset
      column_le tile_positive small offset_lt).symm

variable {V H : Type*}

/-- Values in one compact tile leaf, with columns already sorted by height
and original index, as in the prover. -/
def tiledRow (height tileLog tile offset : Nat) (columns : List (Column V)) : List V :=
  columns.map fun column =>
    column.value (tiledPosition height column.logSize tileLog tile offset)

theorem tiledRow_eq_projectedRow (height tileLog tile offset : Nat)
    (columns : List (Column V))
    (tile_positive : 0 < tileLog) (tile_le : tileLog ≤ height)
    (offset_lt : offset < 2 ^ tileLog)
    (valid : ∀ column ∈ columns, column.logSize ≤ height) :
    tiledRow height tileLog tile offset columns =
      projectedRow height (tile * 2 ^ tileLog + offset) columns := by
  induction columns with
  | nil => rfl
  | cons column rest ih =>
      have head : column.logSize ≤ height := valid column (by simp)
      have tail : ∀ c ∈ rest, c.logSize ≤ height := by
        intro c member
        exact valid c (by simp [member])
      change column.value (tiledPosition height column.logSize tileLog tile offset) ::
          tiledRow height tileLog tile offset rest =
        column.value (projectedPosition height column.logSize
          (tile * 2 ^ tileLog + offset)) ::
          projectedRow height (tile * 2 ^ tileLog + offset) rest
      rw [tiledPosition_eq_projected height column.logSize tileLog tile offset
        head tile_positive tile_le offset_lt, ih tail]

/-- The compact tree's abstract leaf and parent recurrence, using tiled
projection at the leaf. `layer = 0` is the full leaf layer. -/
def tiledLayerHash (leafHash : List V → H) (parentHash : H × H → H)
    (height tileLog : Nat) (columns : List (Column V)) : Nat → Nat → H
  | 0, position => leafHash (tiledRow height tileLog
      (position / 2 ^ tileLog) (position % 2 ^ tileLog) columns)
  | layer + 1, position => parentHash
      (tiledLayerHash leafHash parentHash height tileLog columns layer (2 * position),
       tiledLayerHash leafHash parentHash height tileLog columns layer (2 * position + 1))

/-- For every layer and position, the tiled recurrence is the ideal
complete-tree recurrence. This theorem is independent of hash injectivity. -/
theorem tiledLayerHash_eq_layerHash (leafHash : List V → H)
    (parentHash : H × H → H) (height tileLog : Nat)
    (columns : List (Column V))
    (tile_positive : 0 < tileLog) (tile_le : tileLog ≤ height)
    (valid : ∀ column ∈ columns, column.logSize ≤ height)
    (layer position : Nat) :
    tiledLayerHash leafHash parentHash height tileLog columns layer position =
      layerHash leafHash parentHash height columns layer position := by
  induction layer generalizing position with
  | zero =>
      change leafHash (tiledRow height tileLog
        (position / 2 ^ tileLog) (position % 2 ^ tileLog) columns) =
        leafHash (projectedRow height position columns)
      rw [tiledRow_eq_projectedRow height tileLog
        (position / 2 ^ tileLog) (position % 2 ^ tileLog) columns
        tile_positive tile_le (Nat.mod_lt _ (by positivity)) valid]
      have decomposition : position / 2 ^ tileLog * 2 ^ tileLog +
          position % 2 ^ tileLog = position := by
        simpa [Nat.mul_comm] using (Nat.div_add_mod position (2 ^ tileLog))
      rw [decomposition]
  | succ layer ih =>
      simp only [tiledLayerHash, layerHash]
      rw [ih (2 * position), ih (2 * position + 1)]

theorem tiledRoot_eq_committedRoot (leafHash : List V → H)
    (parentHash : H × H → H) (height tileLog : Nat)
    (columns : List (Column V))
    (tile_positive : 0 < tileLog) (tile_le : tileLog ≤ height)
    (valid : ∀ column ∈ columns, column.logSize ≤ height) :
    tiledLayerHash leafHash parentHash height tileLog columns height 0 =
      committedRoot leafHash parentHash height columns := by
  exact tiledLayerHash_eq_layerHash leafHash parentHash height tileLog
    columns tile_positive tile_le valid height 0

end S31.Gadgets.PcsFri.MultiproofCompactTiles
