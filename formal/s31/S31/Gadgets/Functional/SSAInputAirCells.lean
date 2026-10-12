import S31.Gadgets.Functional.SSAOutputAirCells

/-!
Fourteen projected preprocessed cells on the public-input side of the
bounded 512-row direct-gate profile. Four scalar M31 words enter through
public ABI copy adds, four pointwise identity producers (`raw .* 1 = raw`), three basis
multiplications, and three pack adds. The last pack add produces native wire
22, which is SSA input wire zero. Its output multiplicity is the number of
operand reads of that SSA input in the checked source.

The package checker supplies total add rows and separately validates the
basis constant values, every other row, public ABI, and exported-column
hashes. This model does not authenticate a committed column, public input
value, Gate lookup, or native verifier behavior.
-/

namespace S31.Functional.SSAInputAirCells

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAOutputAirCells

def sourceInputUses (certificate : Certificate) : Nat :=
  certificate.instructions.foldl
    (fun count instruction =>
      count + (if instruction.lhs == 0 then 1 else 0) +
        (if instruction.rhs == 0 then 1 else 0)) 0

def expectedPackAddCell (certificate : Certificate) (index : Nat) : ColumnCell :=
  { traceRow := index,
    addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0,
    in0 := if index == 0 then 11 else 16 + 2 * index,
    in1 := 17 + 2 * index,
    out := 18 + 2 * index,
    mults := if index == 2 then sourceInputUses certificate else 1 }

def expectedPackMulCell (totalAddRows index : Nat) : ColumnCell :=
  { traceRow := totalAddRows + 1 + index,
    addFlag := 0, subFlag := 0, mulFlag := 1, pointwiseMulFlag := 0,
    in0 := maskBasisAddress (index + 1),
    in1 := 12 + index,
    out := 17 + 2 * index,
    mults := 1 }

def expectedInputCopyCell (certificate : Certificate) (lane : Nat) : ColumnCell :=
  { traceRow := 3 + sourceAddCount certificate + lane,
    addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0,
    in0 := 11 + lane,
    in1 := 0,
    out := 3 + lane,
    mults := 1 }

def expectedInputSelfCell (certificate : Certificate) (totalAddRows lane : Nat) :
    ColumnCell :=
  { traceRow := totalAddRows + 32 + sourceMulCount certificate + lane,
    addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1,
    in0 := 11 + lane,
    in1 := 1,
    out := 11 + lane,
    mults := 3 }

/-- The direct input packing creates the same native address that the
source-gate row model assigns to SSA wire zero. -/
theorem pack_result_is_ssa_input (certificate : Certificate) :
    (expectedPackAddCell certificate 2).out = address 0 := by
  rfl

theorem pack_input_multiplicity_is_ssa_uses (certificate : Certificate) :
    (expectedPackAddCell certificate 2).mults = sourceInputUses certificate := by
  rfl

def expectedInputCells (certificate : Certificate) (totalAddRows : Nat) :
    List ColumnCell :=
  (List.range 3).map (expectedPackAddCell certificate) ++
    (List.range 3).map (expectedPackMulCell totalAddRows) ++
    (List.range 4).map (expectedInputCopyCell certificate) ++
    (List.range 4).map (expectedInputSelfCell certificate totalAddRows)

/-- Exact source/normalized byte admission and exact projected input cells
share one checked SSA certificate. The package-to-Lean and native value joins
remain external premises. -/
theorem checked_input_cells_sound (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate) (input : Lanes)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedInputCells certificate totalAddRows) :
    observedCells = expectedInputCells certificate totalAddRows ∧
      executeNormalized certificate input = denotation sourceBytes input :=
  ⟨hcells, checked_relation_sound sourceBytes normalizedBytes certificate input hrelation⟩

end S31.Functional.SSAInputAirCells
