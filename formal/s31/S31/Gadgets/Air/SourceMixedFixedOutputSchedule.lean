import S31.Gadgets.Air.SourceMixedFixedScheduleBridge

/-!
Finite public-output row schedule for the source-pinned N1/N8 mixed chain.
The fixed export supplies each mask, optional inverse multiplication, and
public copy row. Values of the unit and inverse-unit constants remain main
column/producer obligations rather than consequences of the fixed columns.
-/

namespace S31.Gadgets.Air.SourceMixedFixedOutputSchedule

open S31.Gadgets.Packed
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedPublicClosure
open S31.Gadgets.Air.SourceMixedScheduledPublicPath
open S31.Gadgets.Air.SourceMixedFixedScheduleBridge
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.UnpackRows
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.GeneratedMixedFixedRows

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Production address of the packed basis selector for a lane. -/
def unitAddress (lane : Fin 4) : Nat :=
  ([1, 15, 2, 16] : List Nat)[lane.val]!

/-- Inverse basis constants are allocated after the final packed result. -/
def inverseAddress (count : Nat) (lane : Fin 4) : Nat :=
  22 + 10 * count + ([0, 5, 8, 11] : List Nat)[lane.val]!

def maskAddress (count : Nat) (product : Bool) (lane : Fin 4) : Nat :=
  22 + 10 * count +
    ([3, 4, 7, 10, 13, 14, 16, 18] : List Nat)[(outputSlot product lane).val]!

def scalarAddress (count : Nat) (product : Bool) (lane : Fin 4) : Nat :=
  22 + 10 * count +
    ([3, 6, 9, 12, 13, 15, 17, 19] : List Nat)[(outputSlot product lane).val]!

private def maskCell (count : Nat) (product : Bool) (lane : Fin 4) :
    ColumnCell :=
  { traceRow := 500 - 4 * count + (outputSlot product lane).val,
    addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1,
    in0 := packedOutputAddress count product, in1 := unitAddress lane,
    out := maskAddress count product lane, mults := 1 }

private def inverseCell (count : Nat) (product : Bool) (lane : Fin 4) :
    ColumnCell :=
  { traceRow := 472 - 4 * count +
      (if product then 3 else 0) + lane.val - 1,
    addFlag := 0, subFlag := 0, mulFlag := 1, pointwiseMulFlag := 0,
    in0 := maskAddress count product lane,
    in1 := inverseAddress count lane,
    out := scalarAddress count product lane, mults := 1 }

private def copyCell (count : Nat) (product : Bool) (lane : Fin 4) :
    ColumnCell :=
  { traceRow := 3 * (count + 1) + 1 + (outputSlot product lane).val,
    addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0,
    in0 := scalarAddress count product lane, in1 := 0,
    out := 3 + (outputSlot product lane).val, mults := 1 }

private theorem mask_flags (count : Nat) (product : Bool) (lane : Fin 4) :
    cellFlags (maskCell count product lane) = encode .pointwiseMul := by
  rfl

private theorem inverse_flags (count : Nat) (product : Bool) (lane : Fin 4) :
    cellFlags (inverseCell count product lane) = encode .mul := by
  rfl

private theorem copy_flags (count : Nat) (product : Bool) (lane : Fin 4) :
    cellFlags (copyCell count product lane) = encode .add := by
  rfl

private theorem scalar_eq_mask_lane_zero (count : Nat) (product : Bool)
    (lane : Fin 4) (hzero : lane.val = 0) :
    scalarAddress count product lane = maskAddress count product lane := by
  have hlane : lane = 0 := Fin.ext (by simpa using hzero)
  subst lane
  cases product <;> simp [scalarAddress, maskAddress, outputSlot]

private theorem n1_mask_members : ∀ product lane,
    maskCell 1 product lane ∈ N1.selectedCells := by decide
private theorem n1_inverse_members : ∀ product lane,
    lane.val ≠ 0 → inverseCell 1 product lane ∈ N1.selectedCells := by decide
private theorem n1_copy_members : ∀ product lane,
    copyCell 1 product lane ∈ N1.selectedCells := by decide

private theorem n8_mask_members : ∀ product lane,
    maskCell 8 product lane ∈ N8.selectedCells := by decide
private theorem n8_inverse_members : ∀ product lane,
    lane.val ≠ 0 → inverseCell 8 product lane ∈ N8.selectedCells := by decide
private theorem n8_copy_members : ∀ product lane,
    copyCell 8 product lane ∈ N8.selectedCells := by decide

/-- Every N1 public word has a fixed mask, optional inverse-basis multiply,
and final public copy row. Only constant values are supplied separately. -/
theorem n1_outputs_scheduled (boundary : Boundary 1) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (hunit : ∀ lane, ValueAt boundary (unitAddress lane) (unit lane))
    (hinverse : ∀ lane, lane.val ≠ 0 →
      ValueAt boundary (inverseAddress 1 lane) (unitInverse lane)) :
    ∀ product lane, ScheduledOutputPath boundary 1 product lane := by
  intro product lane
  refine ⟨unitAddress lane, maskAddress 1 product lane,
    inverseAddress 1 lane, scalarAddress 1 product lane,
    hunit lane, ?_, ?_, ?_⟩
  · exact n1_selected_scheduled boundary trace hfixed hrows
      (maskCell 1 product lane) (n1_mask_members product lane)
      .pointwiseMul (mask_flags 1 product lane) (by simp [maskCell])
  · by_cases hzero : lane.val = 0
    · simpa [hzero] using scalar_eq_mask_lane_zero 1 product lane hzero
    · simp only [hzero, ↓reduceIte]
      exact ⟨hinverse lane hzero,
        n1_selected_scheduled boundary trace hfixed hrows
          (inverseCell 1 product lane)
          (n1_inverse_members product lane hzero)
          .mul (inverse_flags 1 product lane) (by simp [inverseCell])⟩
  · exact n1_selected_scheduled boundary trace hfixed hrows
      (copyCell 1 product lane) (n1_copy_members product lane)
      .add (copy_flags 1 product lane) (by simp [copyCell])

/-- The same complete eight-word output row schedule for N8. -/
theorem n8_outputs_scheduled (boundary : Boundary 8) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (hunit : ∀ lane, ValueAt boundary (unitAddress lane) (unit lane))
    (hinverse : ∀ lane, lane.val ≠ 0 →
      ValueAt boundary (inverseAddress 8 lane) (unitInverse lane)) :
    ∀ product lane, ScheduledOutputPath boundary 8 product lane := by
  intro product lane
  refine ⟨unitAddress lane, maskAddress 8 product lane,
    inverseAddress 8 lane, scalarAddress 8 product lane,
    hunit lane, ?_, ?_, ?_⟩
  · exact n8_selected_scheduled boundary trace hfixed hrows
      (maskCell 8 product lane) (n8_mask_members product lane)
      .pointwiseMul (mask_flags 8 product lane) (by simp [maskCell])
  · by_cases hzero : lane.val = 0
    · simpa [hzero] using scalar_eq_mask_lane_zero 8 product lane hzero
    · simp only [hzero, ↓reduceIte]
      exact ⟨hinverse lane hzero,
        n8_selected_scheduled boundary trace hfixed hrows
          (inverseCell 8 product lane)
          (n8_inverse_members product lane hzero)
          .mul (inverse_flags 8 product lane) (by simp [inverseCell])⟩
  · exact n8_selected_scheduled boundary trace hfixed hrows
      (copyCell 8 product lane) (n8_copy_members product lane)
      .add (copy_flags 8 product lane) (by simp [copyCell])

end S31.Gadgets.Air.SourceMixedFixedOutputSchedule
