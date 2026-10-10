import S31.Gadgets.Functional.SSAAirColumnCells

/-!
The eleven projected preprocessed cells that carry a bounded direct-gate
program's selected QM31 result to its four public M31 words: four pointwise
basis masks, three ordinary multiplications by inverse basis constants, and
four public ABI copy adds. The checked SSA fixes the selected source address,
instruction count, and number of source add/multiply rows. The package
checker supplies the total add-row count and separately checks the basis
constant values, all other rows, exported-column hashes, and package key.

Equality with the exported cells does not prove that a commitment opens to
them, that Gate lookup authenticates values at these addresses, or that the
native verifier implements the modeled rows.
-/

namespace S31.Functional.SSAOutputAirCells

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells

def sourceMulCount (certificate : Certificate) : Nat :=
  certificate.instructions.foldl
    (fun count instruction => count + if instruction.multiply then 1 else 0) 0

def sourceAddCount (certificate : Certificate) : Nat :=
  certificate.instructions.foldl
    (fun count instruction => count + if instruction.multiply then 0 else 1) 0

def maskAddress (n lane : Nat) : Nat :=
  if lane == 0 then 23 + n else 21 + n + 3 * lane

def resultAddress (n lane : Nat) : Nat :=
  23 + n + 3 * lane

def maskBasisAddress (lane : Nat) : Nat :=
  match lane with
  | 0 => 1
  | 1 => 15
  | 2 => 2
  | _ => 16

def expectedMaskCell (certificate : Certificate) (totalAddRows lane : Nat) :
    ColumnCell :=
  { traceRow := totalAddRows + 28 + sourceMulCount certificate + lane,
    addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 1,
    in0 := address certificate.output,
    in1 := maskBasisAddress lane,
    out := maskAddress certificate.instructions.length lane,
    mults := 1 }

def expectedInverseCell (certificate : Certificate) (totalAddRows index : Nat) :
    ColumnCell :=
  let n := certificate.instructions.length
  let lane := index + 1
  { traceRow := totalAddRows + 4 + index,
    addFlag := 0, subFlag := 0, mulFlag := 1, pointwiseMulFlag := 0,
    in0 := maskAddress n lane,
    in1 := 25 + n + 3 * index,
    out := resultAddress n lane,
    mults := 1 }

def expectedCopyCell (certificate : Certificate) (lane : Nat) : ColumnCell :=
  { traceRow := 7 + sourceAddCount certificate + lane,
    addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0,
    in0 := resultAddress certificate.instructions.length lane,
    in1 := 0,
    out := 7 + lane,
    mults := 1 }

/-- Four mask rows read the same source-selected output address. -/
def expectedMaskCells (certificate : Certificate) (totalAddRows : Nat) :
    List ColumnCell :=
  (List.range 4).map (expectedMaskCell certificate totalAddRows)

theorem four_masks_read_selected_output (certificate : Certificate)
    (totalAddRows : Nat) :
    (expectedMaskCells certificate totalAddRows).map ColumnCell.in0 =
      List.replicate 4 (address certificate.output) := by
  rfl

/-- In native kind order: four pointwise masks, three ordinary inverse
multiplies, then four output copies. The rows themselves are grouped by
kind, so this list order is only for the certificate comparison. -/
def expectedOutputCells (certificate : Certificate) (totalAddRows : Nat) :
    List ColumnCell :=
  expectedMaskCells certificate totalAddRows ++
    (List.range 3).map (expectedInverseCell certificate totalAddRows) ++
    (List.range 4).map (expectedCopyCell certificate)

/-- Native direct-gate output slot zero is reserved. The next four addresses
are public input words and the last four are public result words. -/
def expectedPublicAddresses : List Nat :=
  [2, 3, 4, 5, 6, 7, 8, 9, 10]

theorem copy_rows_write_public_result_slots (certificate : Certificate) :
    (List.range 4).map (fun lane => (expectedCopyCell certificate lane).out) =
      expectedPublicAddresses.drop 5 := by
  rfl

/-- For any byte-admitted certificate and exact exported output-cell match,
the projected row roster and source semantics agree. Authenticity and value
lookup remain separate premises of the full prover theorem. -/
theorem checked_output_cells_sound (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate) (input : Lanes)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedOutputCells certificate totalAddRows) :
    observedCells = expectedOutputCells certificate totalAddRows ∧
      executeNormalized certificate input = denotation sourceBytes input :=
  ⟨hcells, checked_relation_sound sourceBytes normalizedBytes certificate input hrelation⟩

end S31.Functional.SSAOutputAirCells
