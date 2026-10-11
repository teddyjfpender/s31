import S31.Gadgets.Functional.SSADeadRowMixedReturn
import S31.Gadgets.Air.DirectGateEvaluatorCells

/-!
Decode the early-return package's projected source and public-boundary rows
from one 512-row direct-Gate trace. The first nine installed arithmetic roots
are checked on the trace's actual fixed and main cells, including the dead
source row. The trace and root-zero premises are deliberately explicit: this
module does not derive them from native verifier acceptance, PCS/FRI, or the
challenge-compressed Gate lookup.
-/

namespace S31.Functional.SSADecodedTraceBridge

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.DirectGateEvaluatorCells
open S31.Gadgets.Air.DirectGatePolynomial
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSACertificate
open S31.Functional.SSAInstalledBytecodeGateJoin
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSADeadRowGateJoin
open S31.Functional.SSADeadRowMixedReturn
open S31.Functional.GeneratedDirectGateMixedReturn

abbrev DirectTrace := Trace 9

def nativeRows (trace : DirectTrace) : List Row :=
  List.ofFn (row trace)

def projectedCells : List ColumnCell :=
  observedColumnCells ++ observedInputCells ++ observedOutputCells

/-- All eight fixed columns agree with one projected cell at its trace row.
The selector equality covers four field values; addresses and multiplicity
use the decoded canonical M31 representatives. -/
def fixedMatches (trace : DirectTrace) (cell : ColumnCell) : Prop :=
  ∃ i : Fin 512, i.val = cell.traceRow ∧
    (row trace i).flags = cellFlags cell ∧
    (row trace i).in0Address = cell.in0 ∧
    (row trace i).in1Address = cell.in1 ∧
    (row trace i).outAddress = cell.out ∧
    (row trace i).multiplicity = cell.mults

def allArithmeticRootsZero (trace : DirectTrace) : Prop :=
  ∀ i : Fin 512,
    ∀ root ∈ bytecodeArithmetic (fromTrace trace i), root = 0

private theorem native_rows_lookup (trace : DirectTrace) (i : Fin 512) :
    (nativeRows trace)[i.val]? = some (row trace i) := by
  have h : i.val < 2 ^ 9 := by simp
  simp only [nativeRows, List.getElem?_ofFn, dif_pos h]
  exact congrArg some (congrArg (row trace) (Fin.ext rfl))

/-- The physical row projection uses exactly the same first nine installed
roots as the decoded trace, with the selected bytecode's fixed-read
permutation handled by `fromTrace` and the generated polynomial identity. -/
private theorem projected_roots_zero (trace : DirectTrace)
    (cell : ColumnCell) (i : Fin 512)
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

private theorem source_plan :
    ∀ instruction ∈ certificate.instructions,
      ∃ cell ∈ observedColumnCells,
        cell.addFlag = (if instruction.multiply then 0 else 1) ∧
        cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
        cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
        cell.in0 = SSADirectGateBridge.address instruction.lhs ∧
        cell.in1 = SSADirectGateBridge.address instruction.rhs ∧
        cell.out = SSADirectGateBridge.address instruction.id ∧
        cell.mults = sourceUses certificate instruction.id := by
  decide

private theorem boundary_cells_positive :
    (∀ cell ∈ observedInputCells, 0 < cell.mults) ∧
      (∀ cell ∈ observedOutputCells, 0 < cell.mults) := by
  decide

private theorem physical_boundary_rows (trace : DirectTrace)
    (cells : List ColumnCell)
    (hsubset : ∀ cell ∈ cells, cell ∈ projectedCells)
    (hpositive : ∀ cell ∈ cells, 0 < cell.mults)
    (hfixed : ∀ cell ∈ projectedCells, fixedMatches trace cell)
    (hroots : allArithmeticRootsZero trace) :
    physicalGateBytecodeRows cells (nativeRows trace) := by
  intro cell hcell
  obtain ⟨i, hi, hflags, hin0, hin1, hout, hmult⟩ :=
    hfixed cell (hsubset cell hcell)
  refine ⟨row trace i, ?_, hflags, hin0, hin1, hout, hmult, ?_, ?_⟩
  · simpa only [← hi] using native_rows_lookup trace i
  · simpa only [hmult] using hpositive cell hcell
  · exact projected_roots_zero trace cell i hflags hroots

/-- One decoded native column array discharges all three physical-row
predicates used by the early-return source-to-public-claim theorem. The
positive multiplicities of public rows are checked from the generated cell
plan; a used source row's positivity follows from its `sourceUses` count. -/
theorem early_return_decoded_rows (trace : DirectTrace)
    (hfixed : ∀ cell ∈ projectedCells, fixedMatches trace cell)
    (hroots : allArithmeticRootsZero trace) :
    sourceGateBytecodeRowsAllowDead certificate observedColumnCells
      (nativeRows trace) ∧
    physicalGateBytecodeRows observedInputCells (nativeRows trace) ∧
    physicalGateBytecodeRows observedOutputCells (nativeRows trace) := by
  constructor
  · intro instruction hmember
    obtain ⟨cell, hcell, hadd, hsub, hmul, hpm,
      hin0, hin1, hout, huses⟩ := source_plan instruction hmember
    obtain ⟨i, hi, hflags, haddr0, haddr1, haddrOut, hmult⟩ :=
      hfixed cell (by simp [projectedCells, hcell])
    refine ⟨cell, hcell, row trace i, ?_, hadd, hsub, hmul, hpm,
      hin0, hin1, hout, hflags, haddr0, haddr1, haddrOut,
      hmult, ?_, ?_⟩
    · simpa only [← hi] using native_rows_lookup trace i
    · intro hused
      simpa only [hmult, huses] using hused
    · exact projected_roots_zero trace cell i hflags hroots
  constructor
  · exact physical_boundary_rows trace observedInputCells
      (by intro cell hcell; simp [projectedCells, hcell])
      boundary_cells_positive.1 hfixed hroots
  · exact physical_boundary_rows trace observedOutputCells
      (by intro cell hcell; simp [projectedCells, hcell])
      boundary_cells_positive.2 hfixed hroots

/-- The full early-return claim now takes decoded fixed/main columns and
their installed arithmetic roots instead of three independent physical-row
predicates. Gate closure, unique producers, constant/public events, and trace
authentication remain explicit premises. -/
theorem early_return_decoded_public_io_sound (trace : DirectTrace)
    (input claimed : Lanes)
    (externalUses externalYields : List S31.Gadgets.Air.GateLookup.Event)
    (hfixed : ∀ cell ∈ projectedCells, fixedMatches trace cell)
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
      (SSAOutputAirCells.maskBasisAddress i.val, unit i) ∈
        allYields (nativeRows trace) externalYields)
    (hinverseBasis : ∀ i : Fin 3,
      ((SSAOutputAirCells.expectedInverseCell certificate observedAddRows i.val).in1,
        unitInverse ⟨i.val + 1, by omega⟩) ∈
          allYields (nativeRows trace) externalYields)
    (hpublicInputPins : ∀ i : Fin 4,
      (3 + i.val, base (S31.Field.toZMod (input i))) ∈ externalYields)
    (hpublicOutputPins : ∀ i : Fin 4,
      (7 + i.val, base (S31.Field.toZMod (claimed i))) ∈ externalYields) :
    SSATextBytes.denotation sourceBytes input = some claimed := by
  obtain ⟨hsource, hinput, houtput⟩ :=
    early_return_decoded_rows trace hfixed hroots
  exact early_return_public_io_sound input claimed (nativeRows trace)
    externalUses externalYields hsource hinput houtput hbalance hunique
    hzero hbasis1 hbasis2 hbasis3 hmaskBasis hinverseBasis
    hpublicInputPins hpublicOutputPins

end S31.Functional.SSADecodedTraceBridge
