import S31.Gadgets.Functional.SSAInstalledBytecodeRows
import S31.Gadgets.Functional.SSAGateLookupWireMap

/-!
Join the installed `qm31_ops` arithmetic bytecode, physical Gate rows, exact
Gate event balance, and the bounded source-byte semantics. The arithmetic
premise is evaluated on each physical row's twelve main cells. It is not a
zero-root premise on a freely chosen logical wire map. Exact Gate balance and
producer uniqueness turn those physical values into one coherent map.

The final public-claim theorem explicitly assumes that the claimed packed
value is yielded at the selected source address. Deriving that event from the
four public output words and the unpack/copy rows is still open. So are the
native verifier's authenticated opened cells, the LogUp-to-exact-balance
reduction, and PCS/FRI and Fiat--Shamir soundness.
-/

namespace S31.Functional.SSAInstalledBytecodeGateJoin

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.DirectGateEvaluatorCells
open S31.Gadgets.Air.DirectGateNativeIndices
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAInstalledBytecodeRows
open S31.Functional.SSAGateLookupWireMap

/-- Eight source-selected fixed cells and the twelve actual physical main
cells. The interaction columns are zero placeholders because the first nine
installed arithmetic roots do not read them. This is a projection model;
equality with authenticated native openings remains a separate premise. -/
def physicalBytecodeCells (cell : ColumnCell) (row : Row) : Cells :=
  { localFixed := (sourceBytecodeCells cell (fun _ => base 0)).localFixed,
    main := fun i =>
      match i.val with
      | 0 => row.in0.a
      | 1 => row.in0.b
      | 2 => row.in0.c
      | 3 => row.in0.d
      | 4 => row.in1.a
      | 5 => row.in1.b
      | 6 => row.in1.c
      | 7 => row.in1.d
      | 8 => row.output.a
      | 9 => row.output.b
      | 10 => row.output.c
      | _ => row.output.d,
    interaction := fun _ => 0,
    previousInteraction := fun _ => 0 }

/-- The installed nine roots evaluated on a physical row are precisely the
modeled operation residuals at that row's three packed values. -/
theorem physical_bytecode_arithmetic_eq (cell : ColumnCell) (row : Row) :
    bytecodeArithmetic (physicalBytecodeCells cell row) =
      residuals (cellFlags cell) row.in0 row.in1 row.output := by
  rw [bytecode_arithmetic_eq]
  simp [S31.Gadgets.Air.DirectGateEvaluatorCells.arithmetic,
    S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq,
    S31.Gadgets.Air.DirectGateEvaluatorCells.decodedRow,
    S31.Gadgets.Air.DirectGateEvaluatorCells.semanticFixed, physicalBytecodeCells,
    sourceBytecodeCells, cellFlags, fixedReadOrder,
    semanticToAirLocal]

/-- If exact Gate lookup has identified the three physical row values with
the logical address map, the installed roots at the physical row equal the
existing source-projected bytecode roots cell for cell. In particular this
works when both operands read the same address: the two equalities then
require the two physical reads to agree. -/
theorem physical_bytecode_roots_eq_source_roots
    (cell : ColumnCell) (row : Row) (wire : Nat → Quad)
    (hleft : wire cell.in0 = row.in0)
    (hright : wire cell.in1 = row.in1)
    (houtput : wire cell.out = row.output) :
    bytecodeArithmetic (physicalBytecodeCells cell row) =
      bytecodeArithmetic (sourceBytecodeCells cell wire) := by
  rw [physical_bytecode_arithmetic_eq, source_bytecode_arithmetic_eq,
    hleft, hright, houtput]

/-- A direct use of the earlier installed source-row lemma after a physical
Gate row's three values have been authenticated to the logical wire map. -/
theorem physical_bytecode_zero_implies_logical_cell
    (cell : ColumnCell) (row : Row) (wire : Nat → Quad)
    (hleft : wire cell.in0 = row.in0)
    (hright : wire cell.in1 = row.in1)
    (houtput : wire cell.out = row.output)
    (hzero : ∀ root ∈ bytecodeArithmetic (physicalBytecodeCells cell row),
      root = 0) :
    cellAccepts cell wire := by
  apply source_bytecode_zero_implies_cell cell wire
  simpa only [← physical_bytecode_roots_eq_source_roots cell row wire
    hleft hright houtput] using hzero

/-- Installed bytecode zero roots at physical row values give local Gate
arithmetic acceptance when the row selector is the exported fixed selector.
The Gate addresses and multiplicity are checked separately below. -/
theorem physical_bytecode_zero_accepts (cell : ColumnCell) (row : Row)
    (hflags : row.flags = cellFlags cell)
    (hzero : ∀ root ∈ bytecodeArithmetic (physicalBytecodeCells cell row),
      root = 0) :
    accepts row.flags row.in0 row.in1 row.output := by
  rw [hflags]
  simpa only [accepts, physical_bytecode_arithmetic_eq] using hzero

/-- Every checked SSA instruction selects an actual physical row by its
exported trace index. Its fixed selector/address/multiplicity fields match
the source cell, and its installed arithmetic roots vanish on the physical
main values. This is the exact local premise needed at the Gate join. -/
def sourceGateBytecodeRows (certificate : Certificate)
    (observedCells : List ColumnCell) (rows : List Row) : Prop :=
  ∀ instruction ∈ certificate.instructions,
    ∃ cell ∈ observedCells, ∃ row : Row,
      rows[cell.traceRow]? = some row ∧
      cell.addFlag = (if instruction.multiply then 0 else 1) ∧
      cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
      cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
      cell.in0 = address instruction.lhs ∧
      cell.in1 = address instruction.rhs ∧
      cell.out = address instruction.id ∧
      row.flags = cellFlags cell ∧
      row.in0Address = cell.in0 ∧
      row.in1Address = cell.in1 ∧
      row.outAddress = cell.out ∧
      row.multiplicity = cell.mults ∧
      0 < row.multiplicity ∧
      (∀ root ∈ bytecodeArithmetic (physicalBytecodeCells cell row), root = 0)

theorem source_gate_bytecode_rows_imply_gate_rows
    (certificate : Certificate) (observedCells : List ColumnCell)
    (rows : List Row)
    (hbytecode : sourceGateBytecodeRows certificate observedCells rows) :
    sourceGateRows certificate observedCells rows := by
  intro instruction hmember
  obtain ⟨cell, hcell, row, hindex, hflag0, hflag1, hflag2, hflag3,
    hin0, hin1, hout, hflags, haddr0, haddr1, haddrOut,
    hmult, hpositive, hzero⟩ := hbytecode instruction hmember
  exact ⟨cell, hcell, row, hindex, hflag0, hflag1, hflag2, hflag3,
    hin0, hin1, hout, hflags, haddr0, haddr1, haddrOut,
    hmult, hpositive,
    physical_bytecode_zero_accepts cell row hflags hzero⟩

/-- The composition reaches source semantics from installed physical-row
roots and ideal exact Gate balance. The packed input event is an explicit
public-boundary premise; no opening or lookup cryptography is inferred. -/
theorem checked_source_output_of_bytecode_and_exact_gate
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (input : Lanes) (rows : List Row)
    (externalUses externalYields : List Event)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedCells certificate totalAddRows)
    (hbytecode : sourceGateBytecodeRows certificate observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hinputYield : (address 0, packM31 input) ∈
      allYields rows externalYields) :
    observedCells = expectedCells certificate totalAddRows ∧
      ∃ output : Lanes,
        denotation sourceBytes input = some output ∧
          wireOfProduced (allYields rows externalYields)
            (address certificate.output) = packM31 output := by
  exact checked_source_output_of_exact_gate sourceBytes normalizedBytes
    certificate totalAddRows observedCells input rows externalUses
    externalYields hrelation hcells
    (source_gate_bytecode_rows_imply_gate_rows certificate observedCells
      rows hbytecode) hbalance hunique hinputYield

/-- A claimed packed value yielded at the selected source address must be
the four-lane source result. The claim event premise is deliberately visible:
binding the native four scalar public output pins through unpack/copy rows
to this event has not yet been proved. -/
theorem bytecode_exact_gate_selected_claim_sound
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (input claimed : Lanes) (rows : List Row)
    (externalUses externalYields : List Event)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedCells certificate totalAddRows)
    (hbytecode : sourceGateBytecodeRows certificate observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hinputYield : (address 0, packM31 input) ∈
      allYields rows externalYields)
    (hclaimYield : (address certificate.output, packM31 claimed) ∈
      allYields rows externalYields) :
    denotation sourceBytes input = some claimed := by
  obtain ⟨_, output, hsource, hselected⟩ :=
    checked_source_output_of_bytecode_and_exact_gate sourceBytes
      normalizedBytes certificate totalAddRows observedCells input rows
      externalUses externalYields hrelation hcells hbytecode hbalance
      hunique hinputYield
  have hclaimed := wire_of_produced_event
    (allYields rows externalYields) hunique
    (address certificate.output) (packM31 claimed) hclaimYield
  have hpacked : packM31 claimed = packM31 output :=
    hclaimed.symm.trans hselected
  have hvalue : claimed = output := by
    funext i
    apply S31.Field.toZMod_injective
    simpa only [coord_packM31] using
      congrArg (fun q => coord q i) hpacked
  simpa [hvalue] using hsource

end S31.Functional.SSAInstalledBytecodeGateJoin
