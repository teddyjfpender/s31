import S31.Gadgets.Functional.SSAInstalledBytecodeRows
import S31.Gadgets.Functional.GeneratedDirectGateMixedReturn

/-!
An exact source-byte example: `early_output` computes three mixed add/mul
lets but publishes its first square. The generated fixture checks the literal
source and normalized bytes and the three exported selector/address cells.
This module asks for zero *installed bytecode arithmetic roots* at precisely
those cells, rather than an abstract local-row acceptance predicate.

The zero roots and coherent wire values are premises until Gate lookup,
all-row AIR, and PCS authentication are connected to the native verifier.
-/

namespace S31.Functional.SSAInstalledBytecodeMixedReturn

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAInstalledBytecodeRows
open S31.Functional.GeneratedDirectGateMixedReturn

/-- The exact three source instructions each have one matching observed fixed
row. This is a closed structural check over the generated artifact. -/
theorem observed_source_coverage :
    ∀ instruction ∈ certificate.instructions,
      ∃ cell ∈ observedColumnCells,
        cell.addFlag = (if instruction.multiply then 0 else 1) ∧
        cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
        cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
        cell.in0 = address instruction.lhs ∧
        cell.in1 = address instruction.rhs ∧
        cell.out = address instruction.id := by decide

/-- An arbitrary coherent wire map satisfying the selected native arithmetic
bytecode on the exact source rows gives the result of the original 121 source
bytes. The public-input boundary and assumed zero roots over projected cells
are visible; the theorem does not assert that these are native opened cells
or bind the result wire to a verifier's public output claim. -/
theorem mixed_return_bytecode_output (wire : Nat → Quad) (input : Lanes)
    (hboundary : InputBoundary certificate observedAddRows wire input)
    (hzero : ∀ cell ∈ observedColumnCells,
      ∀ root ∈ bytecodeArithmetic (sourceBytecodeCells cell wire), root = 0) :
    ∃ output : Lanes,
      denotation sourceBytes input = some output ∧
        wire (address certificate.output) = packM31 output := by
  have hrows : ∀ instruction ∈ certificate.instructions,
      ∃ cell ∈ observedColumnCells,
        cell.addFlag = (if instruction.multiply then 0 else 1) ∧
        cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
        cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
        cell.in0 = address instruction.lhs ∧
        cell.in1 = address instruction.rhs ∧
        cell.out = address instruction.id ∧
        (∀ root ∈ bytecodeArithmetic (sourceBytecodeCells cell wire),
          root = 0) := by
    intro instruction hmember
    obtain ⟨cell, hcell, hflag0, hflag1, hflag2, hflag3,
      hin0, hin1, hout⟩ := observed_source_coverage instruction hmember
    exact ⟨cell, hcell, hflag0, hflag1, hflag2, hflag3,
      hin0, hin1, hout, hzero cell hcell⟩
  exact (checked_source_bytecode_output sourceBytes normalizedBytes certificate
    observedAddRows observedColumnCells wire input normalized_bytes_check
    observed_source_columns_match hboundary hrows).2

/-- If the first square selector is changed to addition, the same concrete
`x=3, square=9` row cannot satisfy the installed bytecode roots. -/
def changedFirstCell : ColumnCell :=
  { traceRow := 502, addFlag := 1, subFlag := 0, mulFlag := 0,
    pointwiseMulFlag := 0, in0 := 22, in1 := 22, out := 23, mults := 6 }

def changedFirstWire (address : Nat) : Quad :=
  if address == 22 then base 3 else if address == 23 then base 9 else base 0

theorem changed_selector_bytecode_rejected :
    ¬ (∀ root ∈ bytecodeArithmetic
      (sourceBytecodeCells changedFirstCell changedFirstWire), root = 0) := by
  intro hzero
  have hcell := source_bytecode_zero_implies_cell changedFirstCell
    changedFirstWire hzero
  apply changed_selector_rejected
  simpa [cellAccepts, cellFlags, changedFirstCell, changedFirstWire,
    encode] using hcell

end S31.Functional.SSAInstalledBytecodeMixedReturn
