import S31.Gadgets.Functional.SSADeadRowGateJoin
import S31.Gadgets.Air.DirectGateEvaluatorCells

/-!
A parameterized bridge from a decoded direct-Gate trace to the bounded SSA
source, input, and output row predicates. A single trace supplies all physical
row values. The source plan associates each checked instruction with a
projected fixed cell; the exact fixed projection and installed nine
arithmetic roots are premises about that trace, not independently chosen
logical wires.

The theorem is valid for any trace log size and any byte-admitted certificate.
The bounded parser's required first arithmetic instruction proves the source
input is read. It does not establish that verifier
acceptance authenticates the trace, that
challenge-compressed LogUp implies exact Gate balance, or PCS/FRI/Fiat--Shamir
soundness. Those premises stay explicit in the final source-to-claim theorem.
-/

namespace S31.Functional.SSAGeneralDecodedTraceBridge

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.DirectGateEvaluatorCells
open S31.Gadgets.Air.DirectGatePolynomial
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAInstalledBytecodeGateJoin
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSADeadRowGateJoin

def nativeRows {logSize : Nat} (trace : Trace logSize) : List Row :=
  List.ofFn (row trace)

def fixedMatches {logSize : Nat} (trace : Trace logSize)
    (cell : ColumnCell) : Prop :=
  ∃ i : Fin (2 ^ logSize), i.val = cell.traceRow ∧
    (row trace i).flags = cellFlags cell ∧
    (row trace i).in0Address = cell.in0 ∧
    (row trace i).in1Address = cell.in1 ∧
    (row trace i).outAddress = cell.out ∧
    (row trace i).multiplicity = cell.mults

def allArithmeticRootsZero {logSize : Nat} (trace : Trace logSize) : Prop :=
  ∀ i : Fin (2 ^ logSize),
    ∀ root ∈ bytecodeArithmetic (fromTrace trace i), root = 0

/-- Every source instruction has a matching projected arithmetic cell,
including a zero-use result. This predicate does not assert uniqueness. -/
def SourcePlan (certificate : Certificate) (sourceCells : List ColumnCell) :
    Prop :=
  ∀ instruction ∈ certificate.instructions,
    ∃ cell ∈ sourceCells,
      cell.addFlag = (if instruction.multiply then 0 else 1) ∧
      cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
      cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
      cell.in0 = address instruction.lhs ∧
      cell.in1 = address instruction.rhs ∧
      cell.out = address instruction.id ∧
      cell.mults = sourceUses certificate instruction.id

private def rowShape (instruction : Instruction)
    (native : NativeSourceRow) : Prop :=
  native.circuitRow = 5 + instruction.id ∧
    native.multiply = instruction.multiply ∧
    native.in0 = address instruction.lhs ∧
    native.in1 = address instruction.rhs ∧
    native.out = address instruction.id

private def emittedRow (instruction : Instruction)
    (totalAddRows priorAdds priorMuls : Nat) : NativeSourceRow :=
  { circuitRow := 5 + instruction.id,
    traceRow := if instruction.multiply then
        totalAddRows + 28 + priorMuls else 3 + priorAdds,
    multiply := instruction.multiply,
    in0 := address instruction.lhs,
    in1 := address instruction.rhs,
    out := address instruction.id }

private def emitStep (totalAddRows : Nat)
    (state : Nat × Nat × List NativeSourceRow)
    (instruction : Instruction) : Nat × Nat × List NativeSourceRow :=
  let (priorAdds, priorMuls, rows) := state
  (priorAdds + if instruction.multiply then 0 else 1,
   priorMuls + if instruction.multiply then 1 else 0,
   rows ++ [emittedRow instruction totalAddRows priorAdds priorMuls])

private theorem fold_rows_shape (totalAddRows : Nat)
    (remaining prior : List Instruction) (priorAdds priorMuls : Nat)
    (rows : List NativeSourceRow)
    (hprior : List.Forall₂ rowShape prior rows) :
    List.Forall₂ rowShape (prior ++ remaining)
      ((remaining.foldl (emitStep totalAddRows)
        (priorAdds, priorMuls, rows)).2.2) := by
  induction remaining generalizing prior priorAdds priorMuls rows with
  | nil => simpa using hprior
  | cons instruction rest ih =>
      let newRow := emittedRow instruction totalAddRows priorAdds priorMuls
      have hnew : rowShape instruction newRow := by
        simp [rowShape, newRow, emittedRow]
      have hnext : List.Forall₂ rowShape (prior ++ [instruction])
          (rows ++ [newRow]) :=
        List.rel_append hprior (List.Forall₂.cons hnew List.Forall₂.nil)
      simpa [List.foldl_cons, emitStep, newRow, List.append_assoc] using
        (ih (prior ++ [instruction]) _ _ (rows ++ [newRow]) hnext)

/-- Within the modeled `expectedRows` schedule, each position has the
instruction's operand and output addresses, even for a zero-use result.
This lemma does not compare the schedule with native emitted rows. -/
private theorem expected_rows_shape (certificate : Certificate)
    (totalAddRows : Nat) :
    List.Forall₂ rowShape certificate.instructions
      (expectedRows certificate totalAddRows) := by
  have h := fold_rows_shape totalAddRows certificate.instructions [] 0 0 []
    List.Forall₂.nil
  have heq : expectedRows certificate totalAddRows =
      ((certificate.instructions.foldl (emitStep totalAddRows)
        (0, 0, [])).2.2) := by
    rfl
  simpa [heq] using h

private theorem forall₂_rows_plan (instructions : List Instruction)
    (rows : List NativeSourceRow)
    (hshape : List.Forall₂ rowShape instructions rows) :
    ∀ instruction ∈ instructions,
      ∃ native, (instruction, native) ∈ instructions.zip rows ∧
        rowShape instruction native := by
  induction hshape with
  | nil => simp
  | @cons instruction native rest rows hrow _ ih =>
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        exact ⟨native, by simp, hrow⟩
      · obtain ⟨other, hpair, hother⟩ := ih item htail
        exact ⟨other, by simp [hpair], hother⟩

private theorem forall₂_rows_all_pairs (instructions : List Instruction)
    (rows : List NativeSourceRow)
    (hshape : List.Forall₂ rowShape instructions rows) :
    ∀ pair ∈ instructions.zip rows, rowShape pair.1 pair.2 := by
  induction hshape with
  | nil => simp
  | @cons instruction native rest rows hrow _ ih =>
      intro pair hpair
      rcases List.mem_cons.mp hpair with heq | htail
      · subst pair
        exact hrow
      · exact ih pair htail

/-- The modeled source rows retain each instruction's opcode, circuit wire
position, and operand/output addresses. This is an assertion about the
`expectedRows` constructor, not about the native trace emitter. -/
theorem expected_rows_opcode_and_addresses (certificate : Certificate)
    (totalAddRows : Nat) :
    ∀ pair ∈ certificate.instructions.zip (expectedRows certificate totalAddRows),
      pair.2.circuitRow = 5 + pair.1.id ∧
      pair.2.multiply = pair.1.multiply ∧
      pair.2.in0 = address pair.1.lhs ∧
      pair.2.in1 = address pair.1.rhs ∧
      pair.2.out = address pair.1.id := by
  exact forall₂_rows_all_pairs certificate.instructions
    (expectedRows certificate totalAddRows)
    (expected_rows_shape certificate totalAddRows)

private theorem forall₂_opcode_sequence (instructions : List Instruction)
    (rows : List NativeSourceRow)
    (hshape : List.Forall₂ rowShape instructions rows) :
    rows.map NativeSourceRow.multiply =
      instructions.map Instruction.multiply := by
  induction hshape with
  | nil => rfl
  | @cons instruction native rest rows hrow _ ih =>
      simp [hrow.2.1, ih]

/-- The full modeled row opcode sequence has exactly the source's ordered
add/pointwise-multiply partition. No arithmetic selector is inferred from a
native commitment by this theorem. -/
theorem expected_rows_opcode_sequence (certificate : Certificate)
    (totalAddRows : Nat) :
    (expectedRows certificate totalAddRows).map NativeSourceRow.multiply =
      certificate.instructions.map Instruction.multiply :=
  forall₂_opcode_sequence certificate.instructions
    (expectedRows certificate totalAddRows)
    (expected_rows_shape certificate totalAddRows)

private theorem forall₂_cell_opcode_flags (certificate : Certificate)
    (instructions : List Instruction) (rows : List NativeSourceRow)
    (hshape : List.Forall₂ rowShape instructions rows) :
    ((instructions.zip rows).map
      (fun pair =>
        let cell := expectedCell certificate pair.1 pair.2
        (cell.addFlag, cell.pointwiseMulFlag))) =
      instructions.map (fun instruction =>
        (if instruction.multiply then 0 else 1,
         if instruction.multiply then 1 else 0)) := by
  induction hshape with
  | nil => rfl
  | @cons instruction native rest rows _ _ ih =>
      simp only [List.zip_cons_cons, List.map_cons]
      congr 1

/-- The projected source AIR cells have exactly one add or pointwise-multiply
selector per source instruction, in source order. The remaining arithmetic
selectors are zero by `expectedCell`'s definition. -/
theorem expected_cells_opcode_flags (certificate : Certificate)
    (totalAddRows : Nat) :
    (expectedCells certificate totalAddRows).map
      (fun cell => (cell.addFlag, cell.pointwiseMulFlag)) =
      certificate.instructions.map (fun instruction =>
        (if instruction.multiply then 0 else 1,
         if instruction.multiply then 1 else 0)) := by
  simpa [expectedCells, List.map_map] using
    (forall₂_cell_opcode_flags certificate certificate.instructions
      (expectedRows certificate totalAddRows)
      (expected_rows_shape certificate totalAddRows))

private def rowsWithin (totalAddRows priorAdds priorMuls : Nat)
    (rows : List NativeSourceRow) : Prop :=
  ∀ row ∈ rows,
    if row.multiply then
      totalAddRows + 28 ≤ row.traceRow ∧
        row.traceRow < totalAddRows + 28 + priorMuls
    else
      3 ≤ row.traceRow ∧ row.traceRow < 3 + priorAdds

private theorem fold_rows_unique (totalAddRows : Nat)
    (remaining : List Instruction) (priorAdds priorMuls : Nat)
    (rows : List NativeSourceRow)
    (hnodup : (rows.map NativeSourceRow.traceRow).Nodup)
    (hwithin : rowsWithin totalAddRows priorAdds priorMuls rows)
    (hgap : 3 + priorAdds + remaining.length ≤ totalAddRows + 28) :
    (((remaining.foldl (emitStep totalAddRows)
      (priorAdds, priorMuls, rows)).2.2).map NativeSourceRow.traceRow).Nodup := by
  induction remaining generalizing priorAdds priorMuls rows with
  | nil => simpa using hnodup
  | cons instruction rest ih =>
      let next := emittedRow instruction totalAddRows priorAdds priorMuls
      simp only [List.length_cons] at hgap
      have hnot : next.traceRow ∉ rows.map NativeSourceRow.traceRow := by
        intro hmember
        obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmember
        have hrange := hwithin old hold
        cases hi : instruction.multiply <;> cases ho : old.multiply <;>
          simp [next, emittedRow, hi, ho] at heq hrange <;> omega
      have hnodup' :
          ((rows ++ [next]).map NativeSourceRow.traceRow).Nodup := by
        simpa [List.map_append] using
          (List.nodup_concat (rows.map NativeSourceRow.traceRow)
            next.traceRow).2 ⟨hnot, hnodup⟩
      have hwithin' : rowsWithin totalAddRows
          (priorAdds + if instruction.multiply then 0 else 1)
          (priorMuls + if instruction.multiply then 1 else 0)
          (rows ++ [next]) := by
        intro row hmember
        rcases List.mem_append.mp hmember with hold | hnew
        · have hrange := hwithin row hold
          cases instruction.multiply <;> cases ho : row.multiply <;>
            simp [ho] at hrange ⊢ <;> omega
        · have heq : row = next := by simpa using hnew
          subst row
          cases hi : instruction.multiply <;>
            simp [next, emittedRow, hi]
      have hgap' :
          3 + (priorAdds + if instruction.multiply then 0 else 1) +
            rest.length ≤ totalAddRows + 28 := by
        cases hi : instruction.multiply <;> simp [hi] at * <;> omega
      simpa [List.foldl_cons, emitStep, next] using
        (ih _ _ (rows ++ [next]) hnodup' hwithin' hgap')

/-- Source rows in the modeled grouped AIR schedule occupy distinct trace
positions. The explicit gap premise keeps the source-add partition below the
pointwise-multiply partition. It is satisfied by the native bounded profile's
row count, but equality of that count with the committed trace is separate. -/
theorem expected_rows_trace_rows_nodup (certificate : Certificate)
    (totalAddRows : Nat)
    (hgap : 3 + certificate.instructions.length ≤ totalAddRows + 28) :
    ((expectedRows certificate totalAddRows).map
      NativeSourceRow.traceRow).Nodup := by
  have h := fold_rows_unique totalAddRows certificate.instructions 0 0 []
    (by simp) (by simp [rowsWithin]) (by simpa using hgap)
  simpa [expectedRows, emitStep] using h

/-- A separately established 16-instruction budget is sufficient for unique
source trace positions at any natural `totalAddRows` in this modeled layout. -/
theorem expected_rows_trace_rows_nodup_of_budget (certificate : Certificate)
    (totalAddRows : Nat) (hbudget : certificate.instructions.length ≤ 16) :
    ((expectedRows certificate totalAddRows).map
      NativeSourceRow.traceRow).Nodup := by
  apply expected_rows_trace_rows_nodup
  omega

/-- The projected AIR source cells inherit the modeled schedule's unique
trace positions. This says nothing about omitted non-source cells. -/
theorem expected_cells_trace_rows_nodup (certificate : Certificate)
    (totalAddRows : Nat)
    (hgap : 3 + certificate.instructions.length ≤ totalAddRows + 28) :
    ((expectedCells certificate totalAddRows).map ColumnCell.traceRow).Nodup := by
  have hlen := (expected_rows_shape certificate totalAddRows).length_eq
  have hproj :
      (expectedCells certificate totalAddRows).map ColumnCell.traceRow =
        (expectedRows certificate totalAddRows).map
          NativeSourceRow.traceRow := by
    calc
      _ = ((certificate.instructions.zip
          (expectedRows certificate totalAddRows)).map Prod.snd).map
            NativeSourceRow.traceRow := by
              simp [expectedCells, expectedCell, List.map_map]
      _ = _ := by rw [List.map_snd_zip hlen.ge]
  rw [hproj]
  exact expected_rows_trace_rows_nodup certificate totalAddRows hgap

/-- The modeled deterministic `expectedRows` schedule supplies a matching
projected cell for each instruction. It does not prove uniqueness, native
trace-row placement, or native opcode correspondence; those latter fields
are connected only under the separate `fixedMatches` premise. -/
theorem source_plan_expected (certificate : Certificate)
    (totalAddRows : Nat) :
    SourcePlan certificate (expectedCells certificate totalAddRows) := by
  intro instruction hmember
  obtain ⟨native, hpair, hshape⟩ := forall₂_rows_plan
    certificate.instructions (expectedRows certificate totalAddRows)
    (expected_rows_shape certificate totalAddRows) instruction hmember
  refine ⟨expectedCell certificate instruction native, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(instruction, native), hpair, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hshape.2.2.1
  · exact hshape.2.2.2.1
  · exact hshape.2.2.2.2
  · rfl

/-- Output masks, inverse-basis products, and public copies each yield once
by construction, independently of the source program's instruction count. -/
theorem expected_output_cells_positive (certificate : Certificate)
    (totalAddRows : Nat) :
    ∀ cell ∈ expectedOutputCells certificate totalAddRows,
      0 < cell.mults := by
  intro cell hcell
  simp [expectedOutputCells, expectedMaskCells, expectedMaskCell,
    expectedInverseCell, expectedCopyCell] at hcell
  rcases hcell with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
    subst cell <;> simp

/-- The input pack's final row has exactly the source input's use count;
other public-input rows have fixed positive multiplicity. -/
theorem expected_input_cells_positive (certificate : Certificate)
    (totalAddRows : Nat) (huse : 0 < sourceInputUses certificate) :
    ∀ cell ∈ expectedInputCells certificate totalAddRows,
      0 < cell.mults := by
  intro cell hcell
  simp [expectedInputCells, expectedPackAddCell, expectedPackMulCell,
    expectedInputCopyCell, expectedInputSelfCell] at hcell
  rcases hcell with ⟨index, _, h⟩ | ⟨_, _, h⟩ |
      ⟨_, _, h⟩ | ⟨_, _, h⟩
  · subst cell
    by_cases hi : index = 2 <;> simp [hi, huse]
  all_goals subst cell; simp

private theorem input_read_fold_ge (instructions : List Instruction)
    (start : Nat) :
    start ≤ instructions.foldl
      (fun count instruction =>
        count + (if instruction.lhs == 0 then 1 else 0) +
          (if instruction.rhs == 0 then 1 else 0)) start := by
  induction instructions generalizing start with
  | nil => simp
  | cons instruction rest ih =>
      simp only [List.foldl_cons]
      have hstep : start ≤
          start + (if instruction.lhs == 0 then 1 else 0) +
            (if instruction.rhs == 0 then 1 else 0) := by omega
      exact hstep.trans (ih _)

private theorem first_checked_step_reads_input (instruction : Instruction)
    (next : List Term)
    (hstep : checkStep [.input] instruction = some next) :
    instruction.lhs = 0 ∧ instruction.rhs = 0 := by
  have hleft : [Term.input][instruction.lhs]? ≠ none := by
    intro hnone
    simp [checkStep, hnone] at hstep
  have hright : [Term.input][instruction.rhs]? ≠ none := by
    intro hnone
    simp [checkStep, hnone] at hstep
  constructor
  · simpa using hleft
  · simpa using hright

/-- A nonempty checked SSA execution has a first step, and its only initial
wire is input zero. Consequently the source input has a positive arithmetic
use count. -/
theorem source_input_used_of_checked_nonempty (certificate : Certificate)
    (meaning : Term)
    (hterm : termFor certificate = some meaning)
    (hnonempty : certificate.instructions ≠ []) :
    0 < sourceInputUses certificate := by
  cases hins : certificate.instructions with
  | nil => exact False.elim (hnonempty hins)
  | cons instruction rest =>
      have hfirst : ∃ next, checkStep [.input] instruction = some next := by
        unfold termFor at hterm
        simp only [hins, List.foldlM_cons] at hterm
        cases hstep : checkStep [.input] instruction with
        | none => simp [hstep] at hterm
        | some next => exact ⟨next, rfl⟩
      obtain ⟨next, hstep⟩ := hfirst
      have hzero := (first_checked_step_reads_input instruction next hstep).1
      simp only [sourceInputUses, hins, List.foldl_cons]
      have hpositive : 0 <
          (0 + (if instruction.lhs == 0 then 1 else 0) +
            (if instruction.rhs == 0 then 1 else 0)) := by
        simp [hzero]
      exact lt_of_lt_of_le hpositive (input_read_fold_ge rest _)

private theorem parsed_nonempty (bytes : List Nat) (parsed : Parsed)
    (hparse : parseBytes bytes = some parsed) :
    parsed.certificate.instructions ≠ [] := by
  simp [parseBytes, Option.bind] at hparse
  repeat (split at hparse <;> simp_all)
  have hnonempty := hparse.2.2.1
  have hparsed := hparse.2.2.2.2.2
  intro hnil
  exact hnonempty ((congrArg (fun p : Parsed => p.certificate.instructions)
    hparsed).trans hnil)

/-- Successful exact source/normalized-byte admission forces a first checked
instruction. The first instruction can only read the sole initial input wire,
so the public input pack's final producer multiplicity is positive. -/
theorem checked_relation_source_input_used
    (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate) :
    0 < sourceInputUses certificate := by
  unfold checkRelation at hrelation
  cases hsource : parseBytes sourceBytes with
  | none => simp [hsource] at hrelation
  | some parsed =>
      cases hencoded : encodeNormalized parsed with
      | none => simp [hsource, hencoded] at hrelation
      | some expected =>
          by_cases hmatch : expected = normalizedBytes
          · have hcertificate : parsed.certificate = certificate := by
              simpa [hsource, hencoded, hmatch] using hrelation
            subst certificate
            exact source_input_used_of_checked_nonempty
              parsed.certificate parsed.meaning parsed.checked
              (parsed_nonempty sourceBytes parsed hsource)
          · simp [hsource, hencoded, hmatch] at hrelation

private theorem native_rows_lookup {logSize : Nat} (trace : Trace logSize)
    (i : Fin (2 ^ logSize)) :
    (nativeRows trace)[i.val]? = some (row trace i) := by
  simp only [nativeRows, List.getElem?_ofFn, dif_pos i.isLt]

private theorem projected_roots_zero {logSize : Nat}
    (trace : Trace logSize) (cell : ColumnCell)
    (i : Fin (2 ^ logSize))
    (hflags : (row trace i).flags = cellFlags cell)
    (hroots : allArithmeticRootsZero trace) :
    ∀ root ∈ bytecodeArithmetic
      (physicalBytecodeCells cell (row trace i)), root = 0 := by
  have heq : bytecodeArithmetic
      (physicalBytecodeCells cell (row trace i)) =
      bytecodeArithmetic (fromTrace trace i) := by
    calc
      bytecodeArithmetic (physicalBytecodeCells cell (row trace i))
          = residuals (cellFlags cell) (row trace i).in0
              (row trace i).in1 (row trace i).output :=
            physical_bytecode_arithmetic_eq cell (row trace i)
      _ = S31.Gadgets.Air.NativeQm31Air.residuals (row trace i).flags
            (row trace i).in0 (row trace i).in1 (row trace i).output := by
            rw [hflags]
            exact (S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq
              (cellFlags cell) (row trace i).in0 (row trace i).in1
              (row trace i).output).symm
      _ = arithmetic (fromTrace trace i) :=
            (arithmetic_from_trace trace i).symm
      _ = bytecodeArithmetic (fromTrace trace i) := by
            exact (bytecode_arithmetic_eq (fromTrace trace i)).symm
  simpa only [heq] using hroots i

private theorem physical_boundary_rows {logSize : Nat}
    (trace : Trace logSize) (cells : List ColumnCell)
    (hfixed : ∀ cell ∈ cells, fixedMatches trace cell)
    (hpositive : ∀ cell ∈ cells, 0 < cell.mults)
    (hroots : allArithmeticRootsZero trace) :
    physicalGateBytecodeRows cells (nativeRows trace) := by
  intro cell hcell
  obtain ⟨i, hi, hflags, hin0, hin1, hout, hmult⟩ :=
    hfixed cell hcell
  refine ⟨row trace i, ?_, hflags, hin0, hin1, hout, hmult, ?_, ?_⟩
  · simpa only [← hi] using native_rows_lookup trace i
  · simpa only [hmult] using hpositive cell hcell
  · exact projected_roots_zero trace cell i hflags hroots

/-- One decoded trace discharges the three physical-row families for any
certificate whose projected source plan and boundary multiplicities are
checked. Dead source rows still carry exact fixed cells and zero roots. -/
theorem decoded_rows {logSize : Nat} (trace : Trace logSize)
    (certificate : Certificate)
    (sourceCells inputCells outputCells : List ColumnCell)
    (hplan : SourcePlan certificate sourceCells)
    (hpositiveInput : ∀ cell ∈ inputCells, 0 < cell.mults)
    (hpositiveOutput : ∀ cell ∈ outputCells, 0 < cell.mults)
    (hfixed : ∀ cell ∈ sourceCells ++ inputCells ++ outputCells,
      fixedMatches trace cell)
    (hroots : allArithmeticRootsZero trace) :
    sourceGateBytecodeRowsAllowDead certificate sourceCells
      (nativeRows trace) ∧
    physicalGateBytecodeRows inputCells (nativeRows trace) ∧
    physicalGateBytecodeRows outputCells (nativeRows trace) := by
  constructor
  · intro instruction hmember
    obtain ⟨cell, hcell, hadd, hsub, hmul, hpm,
      hin0, hin1, hout, huses⟩ := hplan instruction hmember
    obtain ⟨i, hi, hflags, haddr0, haddr1, haddrOut, hmult⟩ :=
      hfixed cell (by simp [hcell])
    refine ⟨cell, hcell, row trace i, ?_, hadd, hsub, hmul, hpm,
      hin0, hin1, hout, hflags, haddr0, haddr1, haddrOut,
      hmult, ?_, ?_⟩
    · simpa only [← hi] using native_rows_lookup trace i
    · intro hused
      simpa only [hmult, huses] using hused
    · exact projected_roots_zero trace cell i hflags hroots
  constructor
  · exact physical_boundary_rows trace inputCells
      (by intro cell hcell; exact hfixed cell (by simp [hcell]))
      hpositiveInput hroots
  · exact physical_boundary_rows trace outputCells
      (by intro cell hcell; exact hfixed cell (by simp [hcell]))
      hpositiveOutput hroots

/-- Generic source-to-public semantics from one decoded trace. Successful
bounded source/normalized-byte admission proves the public input's use count
positive, and row constructors prove the remaining public multiplicities.
Ideal Gate and constant/public-event
premises remain separate from native verifier acceptance. -/
theorem decoded_public_io_sound {logSize : Nat} (trace : Trace logSize)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat)
    (sourceCells inputCells outputCells : List ColumnCell)
    (input claimed : Lanes)
    (externalUses externalYields : List S31.Gadgets.Air.GateLookup.Event)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hsourceCells : sourceCells = expectedCells certificate totalAddRows)
    (hinputCells : inputCells = expectedInputCells certificate totalAddRows)
    (houtputCells : outputCells = expectedOutputCells certificate totalAddRows)
    (hfixed : ∀ cell ∈ sourceCells ++ inputCells ++ outputCells,
      fixedMatches trace cell)
    (hroots : allArithmeticRootsZero trace)
    (hbalance : balanced (nativeRows trace) externalUses externalYields)
    (hunique : uniqueProduced (allYields (nativeRows trace) externalYields))
    (hzero : (0, base 0) ∈ allYields (nativeRows trace) externalYields)
    (hbasis1 : (15, unit ⟨1, by decide⟩) ∈
      allYields (nativeRows trace) externalYields)
    (hbasis2 : (2, unit ⟨2, by decide⟩) ∈
      allYields (nativeRows trace) externalYields)
    (hbasis3 : (16, unit ⟨3, by decide⟩) ∈
      allYields (nativeRows trace) externalYields)
    (hmaskBasis : ∀ i : Fin 4,
      (maskBasisAddress i.val, unit i) ∈
        allYields (nativeRows trace) externalYields)
    (hinverseBasis : ∀ i : Fin 3,
      ((expectedInverseCell certificate totalAddRows i.val).in1,
        unitInverse ⟨i.val + 1, by omega⟩) ∈
          allYields (nativeRows trace) externalYields)
    (hpublicInputPins : ∀ i : Fin 4,
      (3 + i.val, base (Field.toZMod (input i))) ∈ externalYields)
    (hpublicOutputPins : ∀ i : Fin 4,
      (7 + i.val, base (Field.toZMod (claimed i))) ∈ externalYields) :
    denotation sourceBytes input = some claimed := by
  have hinputUse := checked_relation_source_input_used sourceBytes
    normalizedBytes certificate hrelation
  obtain ⟨hsource, hinput, houtput⟩ :=
    decoded_rows trace certificate sourceCells inputCells outputCells
      (by rw [hsourceCells]; exact source_plan_expected certificate totalAddRows)
      (by rw [hinputCells]; exact expected_input_cells_positive certificate totalAddRows hinputUse)
      (by rw [houtputCells]; exact expected_output_cells_positive certificate totalAddRows)
      hfixed hroots
  exact bytecode_exact_gate_public_io_allow_dead_sound
    sourceBytes normalizedBytes certificate totalAddRows
    sourceCells inputCells outputCells input claimed
    (nativeRows trace) externalUses externalYields
    hrelation hsourceCells hsource hinputCells hinput
    houtputCells houtput hbalance hunique
    hzero hbasis1 hbasis2 hbasis3 hmaskBasis hinverseBasis
    hpublicInputPins hpublicOutputPins

end S31.Functional.SSAGeneralDecodedTraceBridge
