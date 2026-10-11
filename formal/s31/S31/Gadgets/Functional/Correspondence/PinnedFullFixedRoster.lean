import S31.Gadgets.Functional.Correspondence.PinnedFullOutputRoster

/-!
All eight preprocessed `qm31_ops` columns for every one of the 512 physical
AIR rows are emitted by the native square4 topology exporter. The row order
here is the semantic order used by the direct-Gate decoder:
add, sub, mul, pointwise-mul, input0 address, input1 address, output address,
output multiplicity. These are source-bound generated data, not authenticated
commitment openings or main/interaction witness values.
-/

namespace S31.Functional.Correspondence.PinnedFullFixedRoster

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness
open S31.Functional.Correspondence.PinnedFullOutputRoster

set_option maxRecDepth 8192

def fixedRows : List (List Nat) :=
  S31.Functional.TextSquare4Native.paddedArithmeticFixedRows

theorem fixed_rows_length : fixedRows.length = 512 := by decide

theorem fixed_row_width : ∀ index : Fin 512,
    (fixedRows[index.val]!).length = 8 := by decide

theorem fixed_cells_canonical : ∀ index : Fin 512, ∀ column : Fin 8,
    (fixedRows[index.val]!)[column.val]! < 2147483647 := by decide

def fixedAt (index : Fin 512) (column : Fin 8) : F :=
  (fixedRows[index.val]!)[column.val]!

/-- The field-canonical decoded value of every pinned fixed cell is exactly
the Nat emitted by the native exporter. This quantifies over all 4096 cells,
not a selected subset. -/
theorem fixedAt_exact (index : Fin 512) (column : Fin 8) :
    (fixedAt index column).val =
      (fixedRows[index.val]!)[column.val]! := by
  change ((fixedRows[index.val]!)[column.val]! % 2147483647) =
    (fixedRows[index.val]!)[column.val]!
  exact Nat.mod_eq_of_lt (fixed_cells_canonical index column)

def trace (main : Fin 512 → Fin 12 → F) : Trace 9 where
  fixed := fixedAt
  main := main
  interaction _ _ := 0
  prev := Equiv.refl _
  airPair _ := 0
  airLast _ := 0
  claimed := 0
  externalUses := []
  externalYields := []

/-- Every decoded fixed cell of the constructed 512-row trace equals its
native-exported value, regardless of all 6144 main-column cells. -/
theorem trace_fixed_exact (main : Fin 512 → Fin 12 → F)
    (index : Fin 512) (column : Fin 8) :
    ((trace main).fixed index column).val =
      (fixedRows[index.val]!)[column.val]! :=
  fixedAt_exact index column

/-- The new eight-column export and the older two-column export agree on
every physical row. This is an internal consistency check between native
exporter products, not a commitment-opening theorem. -/
theorem full_rows_agree_with_output_pairs :
    (List.range 512).map (fun index =>
      ((fixedRows[index]!)[6]!, (fixedRows[index]!)[7]!)) =
    S31.Functional.TextSquare4Native.paddedArithmeticOutputRows := by
  decide

/-- The native direct-gate export contains the full eight-column tuple for
every one of the 27 source and public-boundary cells. The equality checks
the row position as well as selectors, addresses, and multiplicity. -/
theorem selected_fixed_rows_match :
    ∀ cell ∈ squareCells,
      fixedRows[cell.traceRow]! =
        [cell.addFlag, cell.subFlag, cell.mulFlag, cell.pointwiseMulFlag,
          cell.in0, cell.in1, cell.out, cell.mults] := by
  decide

/-- Any decoded trace carrying exactly the pinned fixed columns matches
every selected source and public-boundary cell. Main, interaction and
commitment values remain unconstrained by this theorem. -/
theorem selected_cells_fixed_of_fixed_roster (t : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8, t.fixed i c = fixedAt i c) :
    ∀ cell ∈ squareCells, fixedMatches t cell := by
  intro cell hcell
  let i : Fin 512 := ⟨cell.traceRow, square_roster_bounded cell hcell⟩
  have hrow := selected_fixed_rows_match cell hcell
  have hval (c : Fin 8) : (t.fixed i c).val =
      ([cell.addFlag, cell.subFlag, cell.mulFlag, cell.pointwiseMulFlag,
        cell.in0, cell.in1, cell.out, cell.mults][c.val]!) := by
    rw [hfixed, fixedAt_exact]
    simp [i, hrow]
  refine ⟨i, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [row, hfixed, fixedAt, i, hrow,
      S31.Functional.SSANativePolynomialRows.cellFlags]
  · simpa [row] using hval ⟨4, by decide⟩
  · simpa [row] using hval ⟨5, by decide⟩
  · simpa [row] using hval ⟨6, by decide⟩
  · simpa [row] using hval ⟨7, by decide⟩

theorem selected_cells_fixed (main : Fin 512 → Fin 12 → F) :
    ∀ cell ∈ squareCells, fixedMatches (trace main) cell :=
  selected_cells_fixed_of_fixed_roster (trace main) (by intro i c; rfl)

end S31.Functional.Correspondence.PinnedFullFixedRoster
