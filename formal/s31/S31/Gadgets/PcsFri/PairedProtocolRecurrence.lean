import S31.Gadgets.PcsFri.DeepQuotientAlgebra
import S31.Gadgets.PcsFri.FoldAlgebra
import Mathlib.Tactic

/-!
The algebraic portion of the CAS05 accepted-row to S-two Protocol 3 bridge.

At each height the native source batch orders each original and *its own*
two-point quotient as `f₀, q₀, f₁, q₁, ...`, under powers of one challenge.
Native inverse butterflies omit `1/2`; at height `i`, divide both the carried
line pair and inserted circle batch by `2^i` before applying the published
normalized recurrence. Theorems here quantify over every height and every
finite column roster. They are conditional field algebra. Authentication,
the circle-coordinate quotient law, degree/correlated agreement, transcript
sampling, and Protocol 3's proximity theorem remain separate obligations.
-/

namespace S31.Gadgets.PcsFri.PairedProtocolRecurrence

variable {F : Type*} [Field F]

/-- The direct interpolation of the claimed OOD value and its conjugate at
the row's y-coordinate. This is the independent expression in CAS05's
accepted-relation checker. -/
def conjugateInterpolant (sampleY conjugateY sampleValue conjugateValue rowY : F) : F :=
  sampleValue + (conjugateValue - sampleValue) *
    ((rowY - sampleY) / (conjugateY - sampleY))

/-- The native cross-multiplied line residual equals the direct interpolation
residual used by the accepted-relation checker. The two OOD y-coordinates
must differ. -/
theorem line_residual_eq_interpolation
    (sampleY conjugateY sampleValue conjugateValue rowY rowValue : F)
    (hspan : conjugateY - sampleY ≠ 0) :
    DeepQuotientAlgebra.lineResidual
      (DeepQuotientAlgebra.conjugateLineCoeffs sampleY conjugateY
        sampleValue conjugateValue 1) rowY rowValue =
      (conjugateY - sampleY) *
        (rowValue - conjugateInterpolant sampleY conjugateY
          sampleValue conjugateValue rowY) := by
  unfold DeepQuotientAlgebra.lineResidual
    DeepQuotientAlgebra.conjugateLineCoeffs conjugateInterpolant
  field_simp [hspan]
  ring

/-- Per-column quotient value: original minus its own interpolated OOD
claim, divided by that row's circle vanishing denominator. This is a row
identity, not a polynomial degree theorem. -/
theorem own_quotient_eq_interpolation
    (sampleY conjugateY sampleValue conjugateValue rowY rowValue denominator : F)
    (hspan : conjugateY - sampleY ≠ 0) :
    DeepQuotientAlgebra.lineResidual
        (DeepQuotientAlgebra.conjugateLineCoeffs sampleY conjugateY
          sampleValue conjugateValue 1) rowY rowValue / denominator =
      ((conjugateY - sampleY) *
        (rowValue - conjugateInterpolant sampleY conjugateY
          sampleValue conjugateValue rowY)) / denominator := by
  rw [line_residual_eq_interpolation _ _ _ _ _ _ hspan]

theorem own_quotient_cross_mul
    (sampleY conjugateY sampleValue conjugateValue rowY rowValue denominator : F)
    (hspan : conjugateY - sampleY ≠ 0) (hden : denominator ≠ 0) :
    (DeepQuotientAlgebra.lineResidual
        (DeepQuotientAlgebra.conjugateLineCoeffs sampleY conjugateY
          sampleValue conjugateValue 1) rowY rowValue / denominator) * denominator =
      (conjugateY - sampleY) *
        (rowValue - conjugateInterpolant sampleY conjugateY
          sampleValue conjugateValue rowY) := by
  rw [own_quotient_eq_interpolation _ _ _ _ _ _ _ hspan]
  field_simp [hden]

/-- The native two-word-at-a-time accumulator, with the running challenge
power incremented after *each* original or own-quotient word. -/
def batchLoop (challenge power : F) : List (F × F) → F
  | [] => 0
  | (original, quotient) :: rest =>
      power * original + (power * challenge) * quotient +
        batchLoop challenge (power * challenge * challenge) rest

/-- Protocol 3 Eq. 66's explicit challenge powers for this finite roster. -/
def batchPowers (challenge : F) (column : Nat) : List (F × F) → F
  | [] => 0
  | (original, quotient) :: rest =>
      challenge ^ (2 * column) * original +
        challenge ^ (2 * column + 1) * quotient +
        batchPowers challenge (column + 1) rest

/-- No challenge reset occurs between columns; each quotient receives the
immediately following power. -/
theorem batchLoop_eq_powers (challenge : F) (column : Nat)
    (columns : List (F × F)) :
    batchLoop challenge (challenge ^ (2 * column)) columns =
      batchPowers challenge column columns := by
  induction columns generalizing column with
  | nil => rfl
  | cons head tail ih =>
      rcases head with ⟨original, quotient⟩
      have hnext :
          challenge ^ (2 * column) * challenge * challenge =
            challenge ^ (2 * (column + 1)) := by
        rw [show 2 * (column + 1) = 2 * column + 1 + 1 by omega]
        simp only [pow_succ]
      simp only [batchLoop, batchPowers]
      rw [hnext, ih (column + 1)]
      rw [show 2 * column + 1 = (2 * column) + 1 by omega, pow_succ]

theorem native_batch_eq_protocol3 (challenge : F) (columns : List (F × F)) :
    batchLoop challenge 1 columns = batchPowers challenge 0 columns := by
  simpa using batchLoop_eq_powers challenge 0 columns

/-- Native one-step unnormalized inverse butterfly. -/
def pair (left right coord challenge : F) : F :=
  FoldAlgebra.pairFold challenge coord⁻¹ left right

/-- The normalized inverse butterfly in the paper, Eq. 70. -/
def normalizedPair (left right coord challenge : F) : F :=
  (1 / 2 : F) * pair left right coord challenge

theorem pair_scale (scale left right coord challenge : F) :
    pair (scale * left) (scale * right) coord challenge =
      scale * pair left right coord challenge := by
  unfold pair FoldAlgebra.pairFold
  ring

theorem native_pair_eq_two_normalized (left right coord challenge : F)
    (htwo : (2 : F) ≠ 0) :
    pair left right coord challenge =
      2 * normalizedPair left right coord challenge := by
  unfold normalizedPair
  field_simp [htwo]

/-- The source pair at a given height and the preceding line pair. The
previous pair is ignored at height zero. -/
structure Round (F : Type*) where
  previousLeft : F
  previousRight : F
  insertedLeft : F
  insertedRight : F
  lineCoord : F
  circleCoord : F
  challenge : F

/-- This is the native row recurrence checked by CAS05. -/
def nativeForward (height : Nat) (r : Round F) : F :=
  let inserted := pair r.insertedLeft r.insertedRight r.circleCoord r.challenge
  if height = 0 then inserted else
    pair r.previousLeft r.previousRight r.lineCoord r.challenge +
      r.challenge ^ 2 * inserted

/-- Published Eq. 68 with both height-i oracle pairs rescaled by `2^-i`.
The previous pair is ignored at height zero. -/
def protocol3Forward (height : Nat) (r : Round F) : F :=
  let scale := (2 : F) ^ height
  let inserted := normalizedPair (r.insertedLeft / scale)
    (r.insertedRight / scale) r.circleCoord r.challenge
  if height = 0 then inserted else
    normalizedPair (r.previousLeft / scale) (r.previousRight / scale)
      r.lineCoord r.challenge + r.challenge ^ 2 * inserted

/-- Exact row refinement for every cascade height; no fixed three- or
four-height fixture is used. -/
theorem nativeForward_eq_scaled_protocol3 (height : Nat) (r : Round F)
    (htwo : (2 : F) ≠ 0) :
    nativeForward height r =
      (2 : F) ^ (height + 1) * protocol3Forward height r := by
  have hscale : (2 : F) ^ height ≠ 0 := pow_ne_zero _ htwo
  have hpair (left right coord : F) :
      pair left right coord r.challenge =
        (2 : F) ^ (height + 1) *
          normalizedPair (left / (2 : F) ^ height)
            (right / (2 : F) ^ height) coord r.challenge := by
    simp only [normalizedPair, pair, FoldAlgebra.pairFold]
    rw [pow_succ]
    field_simp [hscale, htwo]
  unfold nativeForward protocol3Forward
  split_ifs with h
  · simpa using hpair r.insertedLeft r.insertedRight r.circleCoord
  · rw [hpair r.previousLeft r.previousRight r.lineCoord,
        hpair r.insertedLeft r.insertedRight r.circleCoord]
    ring

/-- For any finite accepted query set and any schedule of heights, all
verified native forwarded values become the corresponding normalized
Protocol 3 values. Authentication is an external premise of this theorem. -/
theorem accepted_rows_refine_protocol3
    (queries : List Nat) (heightCount : Nat)
    (roundAt : Nat → Nat → Round F) (forwarded : Nat → Nat → F)
    (htwo : (2 : F) ≠ 0)
    (haccepted : ∀ q ∈ queries, ∀ i < heightCount,
      forwarded q i = nativeForward i (roundAt q i)) :
    ∀ q ∈ queries, ∀ i < heightCount,
      forwarded q i = (2 : F) ^ (i + 1) *
        protocol3Forward i (roundAt q i) := by
  intro q hq i hi
  rw [haccepted q hq i hi, nativeForward_eq_scaled_protocol3 i _ htwo]

/-- One sampled CAS05 slot after source and line authentication has provided
row words. Each list member is that column's `(original, own quotient)` pair.
The scalar row values are already field elements; no commitment or degree
claim is hidden in this structure. -/
structure AcceptedSlot (F : Type*) where
  evenColumns : List (F × F)
  oddColumns : List (F × F)
  previousLeft : F
  previousRight : F
  lineCoord : F
  circleCoord : F
  challenge : F
  batchChallenge : F
  forwarded : F

def nativeRoundOf (slot : AcceptedSlot F) : Round F :=
  { previousLeft := slot.previousLeft
    previousRight := slot.previousRight
    insertedLeft := batchLoop slot.batchChallenge 1 slot.evenColumns
    insertedRight := batchLoop slot.batchChallenge 1 slot.oddColumns
    lineCoord := slot.lineCoord
    circleCoord := slot.circleCoord
    challenge := slot.challenge }

def paperRoundOf (slot : AcceptedSlot F) : Round F :=
  { previousLeft := slot.previousLeft
    previousRight := slot.previousRight
    insertedLeft := batchPowers slot.batchChallenge 0 slot.evenColumns
    insertedRight := batchPowers slot.batchChallenge 0 slot.oddColumns
    lineCoord := slot.lineCoord
    circleCoord := slot.circleCoord
    challenge := slot.challenge }

/-- The exact original-plus-own-quotient batch and normalized fold join. A
native accepted-slot equation implies the published sampled-row equation,
after the explicit height-dependent scale. -/
theorem accepted_slot_refines_protocol3 (height : Nat) (slot : AcceptedSlot F)
    (htwo : (2 : F) ≠ 0)
    (haccepted : slot.forwarded = nativeForward height (nativeRoundOf slot)) :
    slot.forwarded = (2 : F) ^ (height + 1) *
      protocol3Forward height (paperRoundOf slot) := by
  have hround : nativeRoundOf slot = paperRoundOf slot := by
    cases slot
    simp [nativeRoundOf, paperRoundOf, native_batch_eq_protocol3]
  rw [haccepted, hround, nativeForward_eq_scaled_protocol3 height _ htwo]

theorem accepted_slots_refine_protocol3
    (queries : List Nat) (heightCount : Nat)
    (slotAt : Nat → Nat → AcceptedSlot F) (htwo : (2 : F) ≠ 0)
    (haccepted : ∀ q ∈ queries, ∀ i < heightCount,
      (slotAt q i).forwarded = nativeForward i (nativeRoundOf (slotAt q i))) :
    ∀ q ∈ queries, ∀ i < heightCount,
      (slotAt q i).forwarded = (2 : F) ^ (i + 1) *
        protocol3Forward i (paperRoundOf (slotAt q i)) := by
  intro q hq i hi
  exact accepted_slot_refines_protocol3 i (slotAt q i) htwo
    (haccepted q hq i hi)

end S31.Gadgets.PcsFri.PairedProtocolRecurrence
