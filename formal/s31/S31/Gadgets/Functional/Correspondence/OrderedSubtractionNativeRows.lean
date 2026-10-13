import S31.Gadgets.Functional.Correspondence.OrderedSubtractionConcrete
import S31.Gadgets.Functional.SSAAirColumnCells

/-!
The direct-Gate physical source-row projection for the bounded straight-line
four-lane grammar with ordered subtraction. The native profile groups add,
sub, ordinary multiply, then pointwise multiply rows. Source operations are
allocated before constant derivation and padding in each group.

The projection fixes selected preprocessed selectors, addresses, row numbers,
and output use counts. It does not authenticate a commitment or the main
trace values at those rows.
-/

namespace S31.Functional.Correspondence.OrderedSubtractionNativeRows

open OrderedSubtractionBytes
open S31.Functional.SSAAirColumnCells

def countOp (instructions : List Instruction)
    (op : OrderedSubtractionBytes.Op) : Nat :=
  instructions.foldl (fun count instruction =>
    count + if instruction.op = op then 1 else 0) 0

def sourceUses (parsed : Parsed) (id : Nat) : Nat :=
  parsed.instructions.foldl (fun count instruction =>
    count + (if instruction.lhs = id then 1 else 0) +
      (if instruction.rhs = id then 1 else 0)) 0 +
    (if parsed.output = id then 4 else 0)

/-- Padding fills the add partition after source and constant gates. Every
source subtraction or pointwise multiplication replaces one padding add row.
The fixed constant derivation contributes one further subtraction. -/
def addRows (parsed : Parsed) : Nat :=
  476 - countOp parsed.instructions .sub - countOp parsed.instructions .mul

/-- The grouped profile retains 512 rows when the bounded source consumes
at most sixteen subtraction and pointwise-multiplication slots. Source add
operations use rows that would otherwise be padding adds. -/
theorem partition_count (parsed : Parsed)
    (hbudget : countOp parsed.instructions .sub +
      countOp parsed.instructions .mul ≤ 16) :
    addRows parsed + (1 + countOp parsed.instructions .sub) + 27 +
      (8 + countOp parsed.instructions .mul) = 512 := by
  unfold addRows
  omega

def sourceCell (parsed : Parsed) (earlier : List Instruction)
    (instruction : Instruction) : ColumnCell :=
  { traceRow := match instruction.op with
      | .add => 3 + countOp earlier .add
      | .sub => addRows parsed + countOp earlier .sub
      | .mul => 504 - countOp parsed.instructions .mul + countOp earlier .mul,
    addFlag := if instruction.op = .add then 1 else 0,
    subFlag := if instruction.op = .sub then 1 else 0,
    mulFlag := 0,
    pointwiseMulFlag := if instruction.op = .mul then 1 else 0,
    in0 := 22 + instruction.lhs,
    in1 := 22 + instruction.rhs,
    out := 22 + instruction.id,
    mults := sourceUses parsed instruction.id }

def expectedCellsAux (parsed : Parsed) (earlier : List Instruction) :
    List Instruction → List ColumnCell
  | [] => []
  | instruction :: rest =>
      sourceCell parsed earlier instruction ::
        expectedCellsAux parsed (earlier ++ [instruction]) rest

def expectedCells (parsed : Parsed) : List ColumnCell :=
  expectedCellsAux parsed [] parsed.instructions

end S31.Functional.Correspondence.OrderedSubtractionNativeRows
