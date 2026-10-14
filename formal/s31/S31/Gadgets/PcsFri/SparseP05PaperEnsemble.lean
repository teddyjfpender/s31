import Mathlib.Tactic
import S31.Gadgets.PcsFri.SparseP05AcceptedH3Roster

/-!
Finite occupancy arithmetic for the accepted sparse Gate H3 roster. The
source-bound Python classifier proves which accepted claims use the base or
shifted OOD point. This file proves the resulting function counts and the
Protocol-3 max-width arithmetic under explicit mapping premises. No theorem
here identifies an actual native batch with a paper batch or proves degree.
-/

namespace S31.PcsFri.SparseP05PaperEnsemble

open SparseP05AcceptedH3Roster

/-- One claim per source column uses the base OOD point in the accepted map.
The point assignment itself is checked by the source-bound Python classifier. -/
def baseSingleQWidth (h : Nat) : Nat := 2 * originalCount h

/-- Only two-sample columns have a second, shifted OOD claim. -/
def shiftedSingleQWidth (h : Nat) : Nat := 2 * twoSampleCount h

/-- A literal pair `(original, own quotient)` per accepted claim duplicates
the original of each two-sample column. This requires a multi-Q extension. -/
def jointRepeatedWidth (h : Nat) : Nat := 2 * explicitClaimCount h

/-- The earlier candidate shares each original across all its claims. Its
soundness requires a separate multi-Q/deduplication reduction. -/
def jointDeduplicatedWidth (h : Nat) : Nat := directWidth h

def baseSingleQSizes : List Nat :=
  [baseSingleQWidth 17, baseSingleQWidth 11, baseSingleQWidth 5]
def shiftedSingleQSizes : List Nat :=
  [shiftedSingleQWidth 17, shiftedSingleQWidth 11, shiftedSingleQWidth 5]
def jointRepeatedSizes : List Nat :=
  [jointRepeatedWidth 17, jointRepeatedWidth 11, jointRepeatedWidth 5]
def jointDeduplicatedSizes : List Nat :=
  [jointDeduplicatedWidth 17, jointDeduplicatedWidth 11, jointDeduplicatedWidth 5]

theorem accepted_occupancies :
    baseSingleQSizes = [28, 56, 38] ∧
    shiftedSingleQSizes = [8, 8, 8] ∧
    jointRepeatedSizes = [36, 64, 46] ∧
    jointDeduplicatedSizes = [32, 60, 42] := by
  decide

/-- These are distinct Protocol-3 instances if a separate single-Q proof is
used for each point. Their error bounds cannot be merged by taking `max`. -/
theorem conditional_separate_single_Q_common_widths
    (paperBase paperShifted : List Nat)
    (hbase : paperBase = baseSingleQSizes)
    (hshifted : paperShifted = shiftedSingleQSizes) :
    paperBase.foldl Nat.max 0 = 56 ∧
    paperShifted.foldl Nat.max 0 = 8 := by
  rw [hbase, hshifted]
  decide

/-- Conditional common padded width of one proposed *joint* per-claim batch.
This premise is not discharged by native P05 or the paper's single-Q Protocol 4. -/
theorem conditional_joint_repeated_common_width (paperBatchSizes : List Nat)
    (hmap : paperBatchSizes = jointRepeatedSizes) :
    paperBatchSizes.foldl Nat.max 0 = 64 := by
  rw [hmap]
  decide

/-- A shared-original joint ensemble would have a different conditional width
and requires an additional multi-point degree-correction argument. -/
theorem conditional_joint_deduplicated_common_width (paperBatchSizes : List Nat)
    (hmap : paperBatchSizes = jointDeduplicatedSizes) :
    paperBatchSizes.foldl Nat.max 0 = 60 := by
  rw [hmap]
  decide

/-- Four periodicity relation words per height are counted separately from
the 73 explicit OOD quotients; treating them as functions is another premise. -/
theorem conditional_periodicity_occupancies :
    [jointRepeatedWidth 17 + twoSampleCount 17,
     jointRepeatedWidth 11 + twoSampleCount 11,
     jointRepeatedWidth 5 + twoSampleCount 5] = [40, 68, 50] ∧
    [jointDeduplicatedWidth 17 + twoSampleCount 17,
     jointDeduplicatedWidth 11 + twoSampleCount 11,
     jointDeduplicatedWidth 5 + twoSampleCount 5] = [36, 64, 46] := by
  decide

end S31.PcsFri.SparseP05PaperEnsemble
