import S31.Gadgets.Functional.SSADeadRowGateJoin
import S31.Gadgets.Air.DirectGateEvaluatorCells

/-!
A parameterized bridge from a decoded direct-Gate trace to the bounded SSA
source, input, and output row predicates. A single trace supplies all physical
row values. The source plan identifies the checked certificate's instructions
with projected fixed cells; the exact fixed projection and installed nine
arithmetic roots are premises about that trace, not independently chosen
logical wires.

The theorem is valid for any trace log size and any checked certificate whose
source input is read at least once. It does not establish that verifier
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

/-- The plan has exactly one certificate-derived arithmetic cell for every
source instruction; it also works for a zero-use result. -/
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

/-- The generated native source-row schedule preserves instruction operands
and output addresses at every position, even for a zero-use instruction. -/
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

/-- The compiler's deterministic source-row schedule itself supplies the
source-plan premise; callers need not posit an unrelated cell-to-instruction
matching. The package's observed-to-expected fixed-column equality remains
an explicit separate check. -/
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
  · exact hshape.1
  · exact hshape.2.1
  · exact hshape.2.2
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

/-- Generic source-to-public semantics from one decoded trace. The positive
`sourceInputUses` premise is exact for the input pack's last row; the bounded
source grammar admits one or more arithmetic instructions and forbids a
direct output alias of the input. Ideal Gate and constant/public-event
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
    (hinputUsed : 0 < sourceInputUses certificate)
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
  obtain ⟨hsource, hinput, houtput⟩ :=
    decoded_rows trace certificate sourceCells inputCells outputCells
      (by rw [hsourceCells]; exact source_plan_expected certificate totalAddRows)
      (by rw [hinputCells]; exact
        expected_input_cells_positive certificate totalAddRows hinputUsed)
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
