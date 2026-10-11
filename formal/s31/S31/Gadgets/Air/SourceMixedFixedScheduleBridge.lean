import S31.Gadgets.Air.SourceMixedScheduledPublicPath
import S31.Gadgets.Functional.Correspondence.GeneratedMixedFixedRows

/-!
For the source-pinned `mixed_general_N` chain, the generated N1/N8 fixture
checks selected fixed rows against the production compiler's 512-row export.
This module transports their opcode, address, and positive multiplicity data
to `ScheduledRow` when one decoded trace is identified with the source-owned
canonical row list. It does not infer main-column values, the producer scan,
or trace authentication from fixed columns.
-/

namespace S31.Gadgets.Air.SourceMixedFixedScheduleBridge

open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAuthenticatedTrace
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.GeneratedMixedFixedRows

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A selected fixed cell becomes a scheduled source row once the decoded
row list is identified with the compiler's canonical row list. This equality
is a separate committed-trace correspondence obligation. -/
theorem scheduled_of_fixed_match {N : Nat} (boundary : Boundary N)
    (trace : Trace 9)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (cell : ColumnCell) (op : Qm31Ops.Op)
    (hfixed : fixedMatches trace cell)
    (hflags : cellFlags cell = encode op)
    (hpositive : 0 < cell.mults) :
    ScheduledRow boundary cell.in0 cell.in1 cell.out op := by
  obtain ⟨i, _, hflag, h0, h1, hout, hmult⟩ := hfixed
  have hmem : row trace i ∈ nativeRows trace :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  rw [hrows] at hmem
  obtain ⟨canonical, hcanonical, hrow⟩ := List.mem_map.mp hmem
  rw [← hrow] at hflag h0 h1 hout hmult
  refine ⟨canonical, hcanonical, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [CanonicalRow.toGate] using h0
  · simpa [CanonicalRow.toGate] using h1
  · simpa [CanonicalRow.toGate] using hout
  · calc
      canonical.flags = cellFlags cell := by
        simpa [CanonicalRow.toGate] using hflag
      _ = encode op := hflags
  · have h : canonical.multiplicity = cell.mults := by
      simpa [CanonicalRow.toGate] using hmult
    omega

/-- Every positive-multiplicity selected N1 row, including pack, unpack,
public copy, and scalar endpoint rows, is source-scheduled. -/
theorem n1_selected_scheduled (boundary : Boundary 1) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (cell : ColumnCell) (hcell : cell ∈ N1.selectedCells)
    (op : Qm31Ops.Op) (hflags : cellFlags cell = encode op)
    (hpositive : 0 < cell.mults) :
    ScheduledRow boundary cell.in0 cell.in1 cell.out op :=
  scheduled_of_fixed_match boundary trace hrows cell op
    (N1.selected_fixed_matches trace hfixed cell hcell) hflags hpositive

/-- Every positive-multiplicity selected N8 row is source-scheduled. Dead
interior pack rows retain their fixed shape but do not yield Gate outputs. -/
theorem n8_selected_scheduled (boundary : Boundary 8) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (cell : ColumnCell) (hcell : cell ∈ N8.selectedCells)
    (op : Qm31Ops.Op) (hflags : cellFlags cell = encode op)
    (hpositive : 0 < cell.mults) :
    ScheduledRow boundary cell.in0 cell.in1 cell.out op :=
  scheduled_of_fixed_match boundary trace hrows cell op
    (N8.selected_fixed_matches trace hfixed cell hcell) hflags hpositive

/-- The all-row output-address range required by the native roster follows
from an exact fixed-column export and decoded-to-source row identity. This
also covers inactive rows, which the logical producer roster later skips. -/
theorem row_address_range_of_fixed {N : Nat} (boundary : Boundary N)
    (trace : Trace 9) (fixed : Fin 512 → Fin 8 → S31.Gadgets.Packed.F)
    (hfixed : ∀ i : Fin 512, trace.fixed i ⟨6, by decide⟩ =
      fixed i ⟨6, by decide⟩)
    (hbound : ∀ i : Fin 512, (fixed i ⟨6, by decide⟩).val < 512)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate) :
    ∀ row ∈ boundary.jointGateSource.gateRows, row.outAddress < 512 := by
  intro target ht
  have hnative : target ∈ nativeRows trace := by
    rw [hrows]
    simpa [Boundary.jointGateSource, GateSource.gateRows] using ht
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hnative
  subst target
  change (trace.fixed i ⟨6, by decide⟩).val < 512
  rw [hfixed i]
  exact hbound i

/-- The complete exported N1 output-address column stays within the native
512-variable roster bound, including rows whose output multiplicity is zero. -/
theorem n1_row_address_range (boundary : Boundary 1) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate) :
    ∀ row ∈ boundary.jointGateSource.gateRows, row.outAddress < 512 := by
  apply row_address_range_of_fixed boundary trace N1.fixedAt
  · intro i; exact hfixed i ⟨6, by decide⟩
  · have hall : ∀ i : Fin 512,
        (N1.fixedAt i ⟨6, by decide⟩).val < 512 := by decide
    exact hall
  · exact hrows

/-- The complete exported N8 output-address column is likewise bounded. -/
theorem n8_row_address_range (boundary : Boundary 8) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate) :
    ∀ row ∈ boundary.jointGateSource.gateRows, row.outAddress < 512 := by
  apply row_address_range_of_fixed boundary trace N8.fixedAt
  · intro i; exact hfixed i ⟨6, by decide⟩
  · have hall : ∀ i : Fin 512,
        (N8.fixedAt i ⟨6, by decide⟩).val < 512 := by decide
    exact hall
  · exact hrows

private def n1TailAdd : ColumnCell :=
  { traceRow := 6, addFlag := 1, subFlag := 0, mulFlag := 0,
    pointwiseMulFlag := 0, in0 := 22, in1 := 32, out := 33, mults := 4 }

private def n1TailMul : ColumnCell :=
  { traceRow := 495, addFlag := 0, subFlag := 0, mulFlag := 0,
    pointwiseMulFlag := 1, in0 := 22, in1 := 32, out := 34, mults := 4 }

private def n8TailAdd : ColumnCell :=
  { traceRow := 27, addFlag := 1, subFlag := 0, mulFlag := 0,
    pointwiseMulFlag := 0, in0 := 22, in1 := 102, out := 103, mults := 4 }

private def n8TailMul : ColumnCell :=
  { traceRow := 467, addFlag := 0, subFlag := 0, mulFlag := 0,
    pointwiseMulFlag := 1, in0 := 22, in1 := 102, out := 104, mults := 4 }

/-- The N1 packed public tail has the exact source-owned add and pointwise
multiply rows in the decoded trace. -/
theorem n1_tail_scheduled (boundary : Boundary 1) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate) :
    ScheduledRow boundary 22 32 33 .add ∧
      ScheduledRow boundary 22 32 34 .pointwiseMul := by
  constructor
  · exact n1_selected_scheduled boundary trace hfixed hrows n1TailAdd
      (by decide) .add (by decide) (by decide)
  · exact n1_selected_scheduled boundary trace hfixed hrows n1TailMul
      (by decide) .pointwiseMul (by decide) (by decide)

/-- The N8 packed public tail has the exact source-owned add and pointwise
multiply rows in the decoded trace. -/
theorem n8_tail_scheduled (boundary : Boundary 8) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate) :
    ScheduledRow boundary 22 102 103 .add ∧
      ScheduledRow boundary 22 102 104 .pointwiseMul := by
  constructor
  · exact n8_selected_scheduled boundary trace hfixed hrows n8TailAdd
      (by decide) .add (by decide) (by decide)
  · exact n8_selected_scheduled boundary trace hfixed hrows n8TailMul
      (by decide) .pointwiseMul (by decide) (by decide)

end S31.Gadgets.Air.SourceMixedFixedScheduleBridge
