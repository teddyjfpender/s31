import S31.Gadgets.Functional.SSANativePolynomialRows
import S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic

/-!
The installed `qm31_ops` arithmetic bytecode meets the bounded source-row
argument at its exact eight fixed cells and twelve main cells. The source
bytes, normalized bytes, and exported fixed cells are checked separately by
`checkRelation` and `expectedCells`; this file replaces an abstract local AIR
residual premise with the nine roots of the selected installed bytecode.

`wire` is still an address-coherent logical value map. Authentication of that
map by Gate lookup, of these cells by PCS, and of all-row zero roots by the
native verifier remain separate obligations; this theorem assumes zero roots
only for cells projected from that logical map.
-/

namespace S31.Functional.SSAInstalledBytecodeRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.DirectGateEvaluatorCells
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Gadgets.Air.DirectGateNativeIndices
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSANativePolynomialRows

/-- The local fixed order is `[add, mul, pointwise, sub, in0, in1, out,
mults]`, the installed selected bytecode's read vector. Main cells are the
three four-limb values at the fixed Gate addresses. The interaction columns
are irrelevant to the first nine arithmetic roots. -/
def sourceBytecodeCells (cell : ColumnCell) (wire : Nat → Quad) : Cells :=
  { localFixed := fun i =>
      match i.val with
      | 0 => cell.addFlag
      | 1 => cell.mulFlag
      | 2 => cell.pointwiseMulFlag
      | 3 => cell.subFlag
      | 4 => cell.in0
      | 5 => cell.in1
      | 6 => cell.out
      | _ => cell.mults,
    main := fun i =>
      match i.val with
      | 0 => (wire cell.in0).a
      | 1 => (wire cell.in0).b
      | 2 => (wire cell.in0).c
      | 3 => (wire cell.in0).d
      | 4 => (wire cell.in1).a
      | 5 => (wire cell.in1).b
      | 6 => (wire cell.in1).c
      | 7 => (wire cell.in1).d
      | 8 => (wire cell.out).a
      | 9 => (wire cell.out).b
      | 10 => (wire cell.out).c
      | _ => (wire cell.out).d,
    interaction := fun _ => 0,
    previousInteraction := fun _ => 0 }

/-- A source-projected row is exactly the local arithmetic row consumed by
the installed program. Addresses and multiplicity do not enter these nine
roots; they enter the two separate LogUp roots. -/
theorem source_bytecode_arithmetic_eq (cell : ColumnCell) (wire : Nat → Quad) :
    bytecodeArithmetic (sourceBytecodeCells cell wire) =
      residuals (cellFlags cell) (wire cell.in0) (wire cell.in1)
        (wire cell.out) := by
  rw [bytecode_arithmetic_eq]
  simp [DirectGateEvaluatorCells.arithmetic,
    DirectGateEvaluatorCells.decodedRow,
    DirectGateEvaluatorCells.semanticFixed, sourceBytecodeCells,
    cellFlags, fixedReadOrder, airLocalToSemantic, semanticToAirLocal]

/-- Exact projected selectors and a zero output from the installed arithmetic
bytecode imply the source operation's local polynomial relation. -/
theorem source_bytecode_zero_implies_cell (cell : ColumnCell)
    (wire : Nat → Quad)
    (hzero : ∀ root ∈ bytecodeArithmetic (sourceBytecodeCells cell wire),
      root = 0) :
    cellAccepts cell wire := by
  rw [cellAccepts, accepts]
  simpa only [source_bytecode_arithmetic_eq] using hzero

/-- Source-to-normalized byte checking, exact exported source-cell checking,
public input pins, and installed bytecode arithmetic at those same cells
together determine the source result for every four-lane input. The logical
value map and row-zero condition remain authentication premises. -/
theorem checked_source_bytecode_output
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (wire : Nat → Quad) (input : Lanes)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedCells certificate totalAddRows)
    (hboundary : InputBoundary certificate totalAddRows wire input)
    (hrows : ∀ instruction ∈ certificate.instructions,
      ∃ cell ∈ observedCells,
        cell.addFlag = (if instruction.multiply then 0 else 1) ∧
        cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
        cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
        cell.in0 = address instruction.lhs ∧
        cell.in1 = address instruction.rhs ∧
        cell.out = address instruction.id ∧
        (∀ root ∈ bytecodeArithmetic (sourceBytecodeCells cell wire),
          root = 0)) :
    observedCells = expectedCells certificate totalAddRows ∧
      ∃ output : Lanes,
        denotation sourceBytes input = some output ∧
          wire (address certificate.output) = packM31 output := by
  apply checked_source_polynomial_output sourceBytes normalizedBytes
    certificate totalAddRows observedCells wire input hrelation hcells
    hboundary
  intro instruction hmember
  obtain ⟨cell, hcell, hflag0, hflag1, hflag2, hflag3,
    hin0, hin1, hout, hzero⟩ := hrows instruction hmember
  exact ⟨cell, hcell, hflag0, hflag1, hflag2, hflag3,
    hin0, hin1, hout, source_bytecode_zero_implies_cell cell wire hzero⟩

end S31.Functional.SSAInstalledBytecodeRows
