import Mathlib.Tactic
import S31.Gadgets.PcsFri.SparseP05AcceptedH3Data
import S31.Gadgets.PcsFri.SparseP05ConditionalBatchCap

/-!
Finite, source-bound coverage checks for the accepted sparse Gate P05 H3
candidate roster. The generated `columns` data records the 61 source columns
and each column's slice of the 73 accepted OOD claims. Its Python generator
checks the full canonical QM31 claim map digest and the accepted key/proof
identity before emitting this reduced Lean data.

The results below show that candidate original tracks cover every source
column exactly once, candidate own-quotient tracks cover every explicit OOD
claim exactly once, and twelve two-sample columns need a separate legacy
periodicity relation word. These are roster facts, not degree tests or a
native-to-paper FRI/BCS reduction.
-/

namespace S31.PcsFri.SparseP05AcceptedH3Roster

open SparseP05AcceptedH3Data

def sourceRefs : List (Nat × Nat) :=
  columns.map fun c => (c.root, c.index)

def expectedSourceRefs : List (Nat × Nat) :=
  ((List.range 12).map fun i => (0, i)) ++
  ((List.range 17).map fun i => (1, i)) ++
  ((List.range 24).map fun i => (2, i)) ++
  ((List.range 8).map fun i => (3, i))

theorem every_source_column_once : sourceRefs = expectedSourceRefs := by decide

def explicitClaimRefs : List Nat :=
  columns.flatMap fun c =>
    (List.range c.claimCount).map fun offset => c.firstClaim + offset

theorem every_explicit_claim_once : explicitClaimRefs = List.range 73 := by decide

/-- Any later degree-correction theorem established for all listed own
quotient tracks reaches every accepted OOD claim, without a missing index. -/
theorem transfer_to_all_accepted_claims (P : Nat → Prop)
    (htracks : ∀ i ∈ explicitClaimRefs, P i) :
    ∀ i, i < 73 → P i := by
  intro i hi
  apply htracks
  rw [every_explicit_claim_once]
  exact List.mem_range.mpr hi

theorem transfer_to_all_source_columns (P : Nat × Nat → Prop)
    (htracks : ∀ ref ∈ sourceRefs, P ref) :
    ∀ ref ∈ expectedSourceRefs, P ref := by
  intro ref href
  apply htracks
  rw [every_source_column_once]
  exact href

def atHeight (h : Nat) : List Column :=
  columns.filter (fun c => c.extendedLog == h)

def originalCount (h : Nat) : Nat := (atHeight h).length
def explicitClaimCount (h : Nat) : Nat := ((atHeight h).map Column.claimCount).sum
def twoSampleCount (h : Nat) : Nat :=
  ((atHeight h).filter (fun c => c.claimCount == 2)).length

def directWidth (h : Nat) : Nat := originalCount h + explicitClaimCount h
def widthIfPeriodicitySeparate (h : Nat) : Nat := directWidth h + twoSampleCount h

theorem accepted_h3_dimensions :
    (originalCount 17, explicitClaimCount 17, twoSampleCount 17) = (14, 18, 4) ∧
    (originalCount 11, explicitClaimCount 11, twoSampleCount 11) = (28, 32, 4) ∧
    (originalCount 5, explicitClaimCount 5, twoSampleCount 5) = (19, 23, 4) := by
  decide

def candidateDirectSizes : List Nat := [directWidth 17, directWidth 11, directWidth 5]
def candidateWithPeriodicitySizes : List Nat :=
  [widthIfPeriodicitySeparate 17, widthIfPeriodicitySeparate 11,
   widthIfPeriodicitySeparate 5]

theorem candidate_direct_sizes : candidateDirectSizes = [32, 60, 42] := by decide
theorem candidate_with_periodicity_sizes :
    candidateWithPeriodicitySizes = [36, 64, 46] := by decide

/-- Conditional only: the paper's per-domain batch functions must first be
proved to equal these direct candidate tracks, with no extra functions or
compression. No such mapping is asserted for the current native protocol. -/
theorem conditional_direct_common_M (paperDomainBatchSizes : List Nat)
    (hmap : paperDomainBatchSizes = candidateDirectSizes) :
    paperDomainBatchSizes.foldl Nat.max 0 = 60 := by
  rw [hmap, candidate_direct_sizes]
  decide

/-- Conditional only: every legacy periodicity relation word is itself a
separate paper-domain function. Its polynomial status is not established. -/
theorem conditional_periodicity_common_M (paperDomainBatchSizes : List Nat)
    (hmap : paperDomainBatchSizes = candidateWithPeriodicitySizes) :
    paperDomainBatchSizes.foldl Nat.max 0 = 64 := by
  rw [hmap, candidate_with_periodicity_sizes]
  decide

/-- These hypothetical mapped widths fit the *isolated ungrinded* sparse
batching factor. The imported cap assumes D₀=N B², R=1, T=2⁶⁴, and zero
certified batch grinding credit. Other paper error terms remain open. -/
theorem conditional_direct_isolated_batch_fits (paperDomainBatchSizes : List Nat)
    (hmap : paperDomainBatchSizes = candidateDirectSizes) :
    SparseP05ConditionalBatchCap.isolatedFits
      (paperDomainBatchSizes.foldl Nat.max 0) := by
  rw [conditional_direct_common_M paperDomainBatchSizes hmap]
  exact (SparseP05ConditionalBatchCap.isolated_fits_iff_cap (M := 60) (by omega)).2
    (by omega)

theorem conditional_periodicity_isolated_batch_fits (paperDomainBatchSizes : List Nat)
    (hmap : paperDomainBatchSizes = candidateWithPeriodicitySizes) :
    SparseP05ConditionalBatchCap.isolatedFits
      (paperDomainBatchSizes.foldl Nat.max 0) := by
  rw [conditional_periodicity_common_M paperDomainBatchSizes hmap]
  exact (SparseP05ConditionalBatchCap.isolated_fits_iff_cap (M := 64) (by omega)).2
    (by omega)

end S31.PcsFri.SparseP05AcceptedH3Roster
