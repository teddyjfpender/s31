import S31.Gadgets.Functional.Correspondence.AliasProjectedExportBridge
import S31.Gadgets.Functional.TextSquare4ProducerRoster

/-!
This module deliberately projects the pinned native square4 export onto all
512 output-address/multiplicity pairs and 27 selected full fixed-column cells.
It constructs a decoded trace for arbitrary main-column values and proves
the corresponding partial fixed-cell equality. The complete eight-column
roster is checked separately in `PinnedFullFixedRoster`.
-/

namespace S31.Functional.Correspondence.PinnedFullOutputRoster

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateProducerRoster
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness

set_option maxRecDepth 8192

private def nativeOutputRows : List (Nat × Nat) :=
  S31.Functional.TextSquare4Native.paddedArithmeticOutputRows

theorem native_output_rows_length : nativeOutputRows.length = 512 := by
  decide

def outputAt (index : Fin 512) : Nat × Nat :=
  nativeOutputRows[index.val]!

set_option maxRecDepth 8192 in
theorem all_output_pairs_pinned :
    List.ofFn outputAt = nativeOutputRows := by
  decide

theorem outputAt_bounded : ∀ index : Fin 512,
    (outputAt index).1 < 2147483647 ∧
      (outputAt index).2 < 2147483647 := by
  decide

def pinnedFixed (index : Fin 512) (column : Fin 8) : F :=
  if column.val = 6 then ((outputAt index).1 : F)
  else if column.val = 7 then ((outputAt index).2 : F)
  else fixedAt squareCells index.val column

def trace (main : Fin 512 → Fin 12 → F) : Trace 9 where
  fixed := pinnedFixed
  main := main
  interaction _ _ := 0
  prev := Equiv.refl _
  airPair _ := 0
  airLast _ := 0
  claimed := 0
  externalUses := []
  externalYields := []

/-- For any main-column values, every one of the 512 decoded row output
addresses and multiplicities equals the native compiler's pinned export. -/
theorem trace_output_pairs_pinned (main : Fin 512 → Fin 12 → F) :
    (nativeRows (trace main)).map
      (fun r => (r.outAddress, r.multiplicity)) = nativeOutputRows := by
  rw [nativeRows, List.map_ofFn]
  have hfunction :
      (fun i : Fin 512 =>
        ((row (trace main) i).outAddress,
         (row (trace main) i).multiplicity)) = outputAt := by
    funext i
    change ((outputAt i).1 % 2147483647,
      (outputAt i).2 % 2147483647) = outputAt i
    exact Prod.ext
      (Nat.mod_eq_of_lt (outputAt_bounded i).1)
      (Nat.mod_eq_of_lt (outputAt_bounded i).2)
  exact (congrArg List.ofFn hfunction).trans all_output_pairs_pinned

/-- Check that every one of the 27 projected alias-square cells agrees with
the pinned full output/multiplicity rows at its physical trace index. -/
theorem selected_output_pairs_match :
    ∀ cell ∈ squareCells,
      nativeOutputRows[cell.traceRow]! =
        (cell.out, cell.mults) := by
  decide

/-- The 27 source and public-boundary cells retain all eight selected
fixed-column values while output address and multiplicity also follow the
full native 512-row export. This constructed trace uses synthetic values for
the other six fixed columns on unselected rows. -/
theorem selected_cells_fixed (main : Fin 512 → Fin 12 → F) :
    ∀ cell ∈ squareCells, fixedMatches (trace main) cell := by
  intro cell hcell
  have hbase := zeroTrace_fixed squareCells square_roster_nodup
    square_roster_bounded square_roster_addresses [] cell hcell
  obtain ⟨i, hi, hflags, hin0, hin1, _, _⟩ := hbase
  have hpair : outputAt i = (cell.out, cell.mults) := by
    have hidx : i = ⟨cell.traceRow, square_roster_bounded cell hcell⟩ :=
      Fin.ext hi
    subst i
    simpa only [outputAt] using selected_output_pairs_match cell hcell
  refine ⟨i, hi, ?_, ?_, ?_, ?_, ?_⟩
  · exact hflags
  · exact hin0
  · exact hin1
  · simp [row, trace, pinnedFixed, hpair,
      Nat.mod_eq_of_lt (square_roster_addresses cell hcell).2.2.1]
  · simp [row, trace, pinnedFixed, hpair,
      Nat.mod_eq_of_lt (square_roster_addresses cell hcell).2.2.2]

/-- A decoded trace whose complete 512-row output-address/multiplicity
columns equal the pinned native export has unique arithmetic producer values,
regardless of its main-column contents. External events may duplicate those
same produced tuples; they must not introduce a conflicting value. This
statement directly supplies `PhysicalTraceContext.unique` once the native
feeder events are shown to be covered by the arithmetic producers. -/
theorem unique_of_pinned_output_roster (t : Trace 9)
    (hfixed : (nativeRows t).map
      (fun r => (r.outAddress, r.multiplicity)) = nativeOutputRows)
    (hcovered : ∀ event ∈ t.externalYields,
      event ∈ allYields (nativeRows t) []) :
    uniqueProduced (allYields (nativeRows t) t.externalYields) := by
  have hactive :
      (activeRows (nativeRows t)).map Row.outAddress =
      S31.Functional.TextSquare4Native.activeArithmeticProducerAddresses := by
    exact S31.Functional.TextSquare4ProducerRoster.fixed_output_rows_imply_active_roster
      (row t) hfixed
  have hnodup :
      ((activeRows (nativeRows t)).map Row.outAddress ++
        ([] : List Nat)).Nodup := by
    simpa [hactive,
      S31.Functional.TextSquare4ProducerRoster.source_has_no_external_producers]
      using S31.Functional.TextSquare4ProducerRoster.source_roster_nodup
  have hbase : uniqueProduced (allYields (nativeRows t) []) :=
    unique_yields_of_nodup_roster (nativeRows t) [] [] hnodup (by simp)
  intro address left right hleft hright
  apply hbase address left right
  · rcases List.mem_append.mp hleft with hrow | hext
    · exact List.mem_append_left _ hrow
    · exact hcovered _ hext
  · rcases List.mem_append.mp hright with hrow | hext
    · exact List.mem_append_left _ hrow
    · exact hcovered _ hext

/-- The concrete pinned trace has no external feeder events, so complete
output/multiplicity equality alone discharges producer uniqueness for any
main-column assignment. -/
theorem all_512_producers_unique (main : Fin 512 → Fin 12 → F) :
    uniqueProduced (allYields (nativeRows (trace main)) []) :=
  unique_of_pinned_output_roster (trace main)
    (trace_output_pairs_pinned main) (by simp [trace])

def alternateTrace (main : Fin 512 → Fin 12 → F) : Trace 9 :=
  { trace main with
    fixed := fun index column =>
      if index.val = 11 ∧ column.val = 0 then 0
      else pinnedFixed index column }

private theorem selected_row_ne_eleven :
    ∀ cell ∈ squareCells, cell.traceRow ≠ 11 := by
  decide

/-- Changing an unprojected selector leaves both the complete exported
output/multiplicity roster and the 27 selected eight-column cells intact. -/
theorem alternate_preserves_exported_projection
    (main : Fin 512 → Fin 12 → F) :
    (nativeRows (alternateTrace main)).map
      (fun r => (r.outAddress, r.multiplicity)) = nativeOutputRows ∧
    (∀ cell ∈ squareCells, fixedMatches (alternateTrace main) cell) := by
  constructor
  · have heq :
        (nativeRows (alternateTrace main)).map
          (fun r => (r.outAddress, r.multiplicity)) =
        (nativeRows (trace main)).map
          (fun r => (r.outAddress, r.multiplicity)) := by
      simp only [nativeRows, List.map_ofFn]
      congr 1
      funext i
      simp [row, alternateTrace, trace]
    exact heq.trans (trace_output_pairs_pinned main)
  · intro cell hcell
    obtain ⟨i, hi, hflags, hin0, hin1, hout, hmult⟩ :=
      selected_cells_fixed main cell hcell
    have hne : i.val ≠ 11 := by
      rw [hi]
      exact selected_row_ne_eleven cell hcell
    refine ⟨i, hi, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [row, alternateTrace, hne] using hflags
    · simpa [row, alternateTrace, hne] using hin0
    · simpa [row, alternateTrace, hne] using hin1
    · simpa [row, alternateTrace, hne] using hout
    · simpa [row, alternateTrace, hne] using hmult

/-- The two-column projection plus selected cells alone does not determine
all eight fixed columns: two decoded traces can agree on that projection and
disagree on row 11's add selector. This says nothing about the full native
roster, which is checked in `PinnedFullFixedRoster`, or AIR satisfiability
of the alternate trace. -/
theorem exported_projection_does_not_determine_all_fixed
    (main : Fin 512 → Fin 12 → F) :
    (nativeRows (trace main)).map
      (fun r => (r.outAddress, r.multiplicity)) = nativeOutputRows ∧
    (nativeRows (alternateTrace main)).map
      (fun r => (r.outAddress, r.multiplicity)) = nativeOutputRows ∧
    (∀ cell ∈ squareCells, fixedMatches (trace main) cell) ∧
    (∀ cell ∈ squareCells, fixedMatches (alternateTrace main) cell) ∧
    (trace main).fixed ⟨11, by decide⟩ ⟨0, by decide⟩ ≠
      (alternateTrace main).fixed ⟨11, by decide⟩ ⟨0, by decide⟩ := by
  refine ⟨trace_output_pairs_pinned main,
    (alternate_preserves_exported_projection main).1,
    selected_cells_fixed main,
    (alternate_preserves_exported_projection main).2, ?_⟩
  change pinnedFixed ⟨11, by decide⟩ ⟨0, by decide⟩ ≠ (0 : F)
  decide

end S31.Functional.Correspondence.PinnedFullOutputRoster
