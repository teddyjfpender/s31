import S31.Gadgets.Functional.SSAAirColumnCells

/-!
The bounded direct-gate source-row projection consumes every checked SSA
instruction exactly once. This closes two bookkeeping gaps in the Lean model:
`expectedCells` uses `List.zip`, and the native exporter groups source adds and
pointwise products in different partitions. The theorems below establish that
the zip cannot silently truncate an instruction and that the projected trace
positions cannot alias when the source has at most sixteen instructions.

These are structural facts about the modeled schedule. They do not establish
that Zig emitted the schedule, that the exported columns are committed, or
that PCS openings authenticate the projected rows.
-/

namespace S31.Functional.SSAProjectedRowCompleteness

open S31.Functional.SSACertificate
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells

private def step (totalAddRows : Nat)
    (state : Nat × Nat × List NativeSourceRow)
    (instruction : Instruction) : Nat × Nat × List NativeSourceRow :=
  let (priorAdds, priorMuls, rows) := state
  let row : NativeSourceRow :=
    { circuitRow := 5 + instruction.id,
      traceRow := if instruction.multiply then
          totalAddRows + 28 + priorMuls else 3 + priorAdds,
      multiply := instruction.multiply,
      in0 := address instruction.lhs,
      in1 := address instruction.rhs,
      out := address instruction.id }
  (priorAdds + if instruction.multiply then 0 else 1,
   priorMuls + if instruction.multiply then 1 else 0,
   rows ++ [row])

private theorem expected_rows_eq_fold (certificate : Certificate)
    (totalAddRows : Nat) :
    expectedRows certificate totalAddRows =
      ((certificate.instructions.foldl (step totalAddRows) (0, 0, [])).2.2) := by
  rfl

private theorem step_length (totalAddRows : Nat)
    (state : Nat × Nat × List NativeSourceRow)
    (instruction : Instruction) :
    (step totalAddRows state instruction).2.2.length = state.2.2.length + 1 := by
  rcases state with ⟨adds, muls, rows⟩
  simp [step]

private theorem fold_length (totalAddRows : Nat)
    (instructions : List Instruction)
    (state : Nat × Nat × List NativeSourceRow) :
    (instructions.foldl (step totalAddRows) state).2.2.length =
      state.2.2.length + instructions.length := by
  induction instructions generalizing state with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih, step_length]
      omega

/-- The modeled direct-gate emitter appends one source row per certificate
instruction, including dead instructions and repeated-operand instructions. -/
theorem expected_rows_length (certificate : Certificate)
    (totalAddRows : Nat) :
    (expectedRows certificate totalAddRows).length =
      certificate.instructions.length := by
  rw [expected_rows_eq_fold, fold_length]
  simp

/-- The subsequent `zip` with source instructions cannot discard a source
instruction because both lists have the same length. -/
theorem expected_cells_length (certificate : Certificate)
    (totalAddRows : Nat) :
    (expectedCells certificate totalAddRows).length =
      certificate.instructions.length := by
  simp [expectedCells, expected_rows_length]

private def placed (totalAddRows adds muls : Nat)
    (rows : List NativeSourceRow) : Prop :=
  (rows.map NativeSourceRow.traceRow).Nodup ∧
    ∀ row ∈ rows,
      row.traceRow < 3 + adds ∨
        (totalAddRows + 28 ≤ row.traceRow ∧
          row.traceRow < totalAddRows + 28 + muls)

private theorem step_placed (totalAddRows adds muls : Nat)
    (rows : List NativeSourceRow) (instruction : Instruction)
    (hplaced : placed totalAddRows adds muls rows)
    (hadds : adds ≤ 16) :
    placed totalAddRows
      (step totalAddRows (adds, muls, rows) instruction).1
      (step totalAddRows (adds, muls, rows) instruction).2.1
      (step totalAddRows (adds, muls, rows) instruction).2.2 := by
  obtain ⟨hnodup, hrange⟩ := hplaced
  cases hmul : instruction.multiply with
  | false =>
      have hfresh : 3 + adds ∉ rows.map NativeSourceRow.traceRow := by
        intro hmember
        obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmember
        rcases hrange old hold with hlow | ⟨hhigh, _⟩
        · omega
        · omega
      constructor
      · simpa [step, hmul, List.map_append, List.nodup_append,
          hnodup, hfresh] using
            (show ∀ a ∈ rows, a.traceRow ≠ 3 + adds from by
              intro a ha heq
              exact hfresh (List.mem_map.mpr ⟨a, ha, heq⟩))
      · intro row hmember
        simp only [step, hmul, List.mem_append, List.mem_singleton] at hmember ⊢
        rcases hmember with hold | hnew
        · rcases hrange row hold with hlow | hhigh
          · exact Or.inl (by omega)
          · exact Or.inr hhigh
        · subst row
          simp
  | true =>
      have hfresh : totalAddRows + 28 + muls ∉
          rows.map NativeSourceRow.traceRow := by
        intro hmember
        obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmember
        rcases hrange old hold with hlow | ⟨_, hhigh⟩
        · omega
        · omega
      constructor
      · simpa [step, hmul, List.map_append, List.nodup_append,
          hnodup, hfresh] using
            (show ∀ a ∈ rows,
                a.traceRow ≠ totalAddRows + 28 + muls from by
              intro a ha heq
              exact hfresh (List.mem_map.mpr ⟨a, ha, heq⟩))
      · intro row hmember
        simp only [step, hmul, List.mem_append, List.mem_singleton] at hmember ⊢
        rcases hmember with hold | hnew
        · rcases hrange row hold with hlow | ⟨hstart, hend⟩
          · exact Or.inl hlow
          · exact Or.inr ⟨hstart, by omega⟩
        · subst row
          simp

private theorem fold_placed (totalAddRows : Nat)
    (instructions : List Instruction)
    (state : Nat × Nat × List NativeSourceRow)
    (hplaced : placed totalAddRows state.1 state.2.1 state.2.2)
    (hcapacity : state.1 + instructions.length ≤ 16) :
    placed totalAddRows
      (instructions.foldl (step totalAddRows) state).1
      (instructions.foldl (step totalAddRows) state).2.1
      (instructions.foldl (step totalAddRows) state).2.2 := by
  induction instructions generalizing state with
  | nil => simpa using hplaced
  | cons instruction rest ih =>
      rcases state with ⟨adds, muls, rows⟩
      simp only [List.length_cons] at hcapacity
      have hnext : placed totalAddRows
          (step totalAddRows (adds, muls, rows) instruction).1
          (step totalAddRows (adds, muls, rows) instruction).2.1
          (step totalAddRows (adds, muls, rows) instruction).2.2 :=
        step_placed totalAddRows adds muls rows instruction hplaced (by omega)
      have hnextCapacity :
          (step totalAddRows (adds, muls, rows) instruction).1 +
            rest.length ≤ 16 := by
        cases hmul : instruction.multiply <;> simp [step, hmul] <;> omega
      simpa only [List.foldl_cons] using
        ih (step totalAddRows (adds, muls, rows) instruction)
          hnext hnextCapacity

private theorem fold_add_count (totalAddRows : Nat)
    (instructions : List Instruction)
    (state : Nat × Nat × List NativeSourceRow) :
    (instructions.foldl (step totalAddRows) state).1 =
      state.1 + (instructions.filter (fun i => !i.multiply)).length := by
  induction instructions generalizing state with
  | nil => simp
  | cons instruction rest ih =>
      rcases state with ⟨adds, muls, rows⟩
      cases hmul : instruction.multiply <;>
        simp [List.foldl_cons, hmul, ih, step]
      omega

private theorem fold_product_count (totalAddRows : Nat)
    (instructions : List Instruction)
    (state : Nat × Nat × List NativeSourceRow) :
    (instructions.foldl (step totalAddRows) state).2.1 =
      state.2.1 + (instructions.filter (fun i => i.multiply)).length := by
  induction instructions generalizing state with
  | nil => simp
  | cons instruction rest ih =>
      rcases state with ⟨adds, muls, rows⟩
      cases hmul : instruction.multiply <;>
        simp [List.foldl_cons, hmul, ih, step]
      omega

/-- The bounded source schedule places every source arithmetic instruction
at a different trace index, independent of instruction order or deadness.
The source grammar and package checker enforce the sixteen-instruction cap. -/
theorem expected_rows_trace_nodup (certificate : Certificate)
    (totalAddRows : Nat)
    (hcapacity : certificate.instructions.length ≤ 16) :
    ((expectedRows certificate totalAddRows).map
      NativeSourceRow.traceRow).Nodup := by
  rw [expected_rows_eq_fold]
  exact (fold_placed totalAddRows certificate.instructions
    (0, 0, []) (by simp [placed]) (by simpa using hcapacity)).1

/-- Under the native bounded-profile row equation, the complete source-row
projection lies before the eight trailing fixed pointwise rows. The source
rows therefore have valid indices in the 512-row trace. This models the
partition arithmetic checked independently by `check_source_fixed_rows`; it
does not authenticate that the native columns satisfy the equation. -/
theorem expected_rows_within_native_trace (certificate : Certificate)
    (totalAddRows : Nat)
    (hcapacity : certificate.instructions.length ≤ 16)
    (hpartition : totalAddRows + 28 +
      (certificate.instructions.filter (fun i => i.multiply)).length + 8 = 512) :
    ∀ row ∈ expectedRows certificate totalAddRows, row.traceRow < 504 := by
  intro row hmember
  rw [expected_rows_eq_fold] at hmember
  have hplaced := fold_placed totalAddRows certificate.instructions
    (0, 0, []) (by simp [placed]) (by simpa using hcapacity)
  rcases hplaced.2 row hmember with hadd | ⟨_, hproduct⟩
  · rw [fold_add_count] at hadd
    have hfilter : (certificate.instructions.filter
        (fun i => !i.multiply)).length ≤ certificate.instructions.length :=
      List.length_filter_le _ _
    omega
  · rw [fold_product_count] at hproduct
    simp at hproduct
    omega

private theorem zip_cell_trace_rows (certificate : Certificate)
    (instructions : List Instruction) (rows : List NativeSourceRow)
    (hlength : instructions.length = rows.length) :
    ((instructions.zip rows).map
      (fun pair => (expectedCell certificate pair.1 pair.2).traceRow)) =
        rows.map NativeSourceRow.traceRow := by
  induction instructions generalizing rows with
  | nil =>
      cases rows with
      | nil => rfl
      | cons row rest => simp at hlength
  | cons instruction rest ih =>
      cases rows with
      | nil => simp at hlength
      | cons row tail =>
          have htail : rest.length = tail.length := by simpa using hlength
          simp only [List.zip_cons_cons, List.map_cons, expectedCell]
          congr 1
          simpa only [expectedCell] using ih tail htail

/-- The actual `expectedCells` list has the same ordered row indices as the
independently constructed native-source row list. -/
theorem expected_cells_trace_rows (certificate : Certificate)
    (totalAddRows : Nat) :
    ((expectedCells certificate totalAddRows).map ColumnCell.traceRow) =
      (expectedRows certificate totalAddRows).map
        NativeSourceRow.traceRow := by
  simp only [expectedCells, List.map_map]
  exact zip_cell_trace_rows certificate certificate.instructions
    (expectedRows certificate totalAddRows)
    (expected_rows_length certificate totalAddRows).symm

/-- Every projected fixed cell lies at a valid native trace index under the
same 512-row partition equation used for `expectedRows`. -/
theorem expected_cells_within_native_trace (certificate : Certificate)
    (totalAddRows : Nat)
    (hcapacity : certificate.instructions.length ≤ 16)
    (hpartition : totalAddRows + 28 +
      (certificate.instructions.filter (fun i => i.multiply)).length + 8 = 512) :
    ∀ cell ∈ expectedCells certificate totalAddRows,
      cell.traceRow < 504 := by
  intro cell hcell
  have htrace : cell.traceRow ∈
      (expectedCells certificate totalAddRows).map ColumnCell.traceRow :=
    List.mem_map.mpr ⟨cell, hcell, rfl⟩
  rw [expected_cells_trace_rows] at htrace
  obtain ⟨row, hrow, heq⟩ := List.mem_map.mp htrace
  rw [← heq]
  exact expected_rows_within_native_trace certificate totalAddRows
    hcapacity hpartition row hrow

/-- No two projected AIR cells can silently refer to the same physical row.
Together with `expected_cells_length`, this gives a total one-to-one source
instruction projection under the checked bounded grammar. -/
theorem expected_cells_trace_nodup (certificate : Certificate)
    (totalAddRows : Nat)
    (hcapacity : certificate.instructions.length ≤ 16) :
    ((expectedCells certificate totalAddRows).map ColumnCell.traceRow).Nodup := by
  rw [expected_cells_trace_rows]
  exact expected_rows_trace_nodup certificate totalAddRows hcapacity

/-- Equality with the observed fixed-cell projection now entails cardinality
and nonaliasing. The sixteen-instruction premise is explicit because this
module does not yet prove the parser's fuel bound as a theorem. -/
theorem observed_source_cells_complete (certificate : Certificate)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (hcapacity : certificate.instructions.length ≤ 16)
    (hcells : observedCells = expectedCells certificate totalAddRows) :
    observedCells.length = certificate.instructions.length ∧
      (observedCells.map ColumnCell.traceRow).Nodup := by
  subst observedCells
  exact ⟨expected_cells_length certificate totalAddRows,
    expected_cells_trace_nodup certificate totalAddRows hcapacity⟩

/-- A resealed projection with two source operations at one physical trace
index cannot equal the checked source-row schedule. -/
theorem repeated_observed_trace_row_rejected (certificate : Certificate)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (hcapacity : certificate.instructions.length ≤ 16)
    (hduplicate : ¬ (observedCells.map ColumnCell.traceRow).Nodup) :
    observedCells ≠ expectedCells certificate totalAddRows := by
  intro heq
  rw [heq] at hduplicate
  exact hduplicate (expected_cells_trace_nodup certificate totalAddRows hcapacity)

private def twoStepCertificate : Certificate :=
  { instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := false },
       { id := 2, lhs := 1, rhs := 1, multiply := true }],
    output := 2 }

/-- A handwritten add-then-square example: source instruction 1 is in add
row 3, while source instruction 2 is in pointwise row 503 of the 512-row
profile with 475 total add rows. The remaining eight pointwise rows occupy
504 through 511. -/
example :
    (expectedCells twoStepCertificate 475).map ColumnCell.traceRow =
      [3, 503] := by decide

example : 475 + 28 +
    (twoStepCertificate.instructions.filter (fun i => i.multiply)).length +
      8 = 512 := by decide

end S31.Functional.SSAProjectedRowCompleteness
