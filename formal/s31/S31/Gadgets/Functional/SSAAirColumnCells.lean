import S31.Gadgets.Functional.SSANormalizedBytes
import S31.Gadgets.Functional.SSADirectGateBridge

/-!
The eight preprocessed QM31 operation-column cells at each source gate's
grouped AIR row in the bounded 512-row direct-gate profile. The expected
selector, addresses, and output multiplicity are derived from the checked
SSA. The generated instance supplies observed cells read from the native
gate-topology export and checks them by kernel reduction.

This is a correspondence check on an exported artifact. It does not prove
that the supplied total add-row count is authentic, that source-independent
rows have the required values, or
that a commitment opens to these cells, that Gate lookup authenticates the
operand values, or that the verifier implements this row relation.
-/

namespace S31.Functional.SSAAirColumnCells

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge

structure ColumnCell where
  traceRow : Nat
  addFlag : Nat
  subFlag : Nat
  mulFlag : Nat
  pointwiseMulFlag : Nat
  in0 : Nat
  in1 : Nat
  out : Nat
  mults : Nat
deriving DecidableEq, Repr

/-- Each later operand read adds one use of this output. The selected public
result is additionally read by all four fixed unpack masks. Other gates are
required to be source-independent by the separate native topology checker. -/
def sourceUses (certificate : Certificate) (id : Nat) : Nat :=
  certificate.instructions.foldl
    (fun count instruction =>
      count + (if instruction.lhs == id then 1 else 0) +
        (if instruction.rhs == id then 1 else 0)) 0 +
    (if certificate.output == id then 4 else 0)

def expectedCell (certificate : Certificate) (instruction : Instruction)
    (row : NativeSourceRow) : ColumnCell :=
  { traceRow := row.traceRow,
    addFlag := if instruction.multiply then 0 else 1,
    subFlag := 0,
    mulFlag := 0,
    pointwiseMulFlag := if instruction.multiply then 1 else 0,
    in0 := row.in0,
    in1 := row.in1,
    out := row.out,
    mults := sourceUses certificate instruction.id }

/-- One projected AIR cell for each certificate instruction, in source
order; `expectedRows` fixes its grouped trace row and native addresses.
`totalAddRows` is supplied by the package checker; this definition does not
validate unrelated rows or derive the count from the committed columns. -/
def expectedCells (certificate : Certificate) (totalAddRows : Nat) :
    List ColumnCell :=
  (certificate.instructions.zip (expectedRows certificate totalAddRows)).map
    (fun pair => expectedCell certificate pair.1 pair.2)

/-- The two executable byte checks and the exact projected-column equality
can be composed without assuming that the Python-emitted certificate has the
source meaning. Authenticity of the native committed columns is still an
explicit external premise. -/
theorem checked_air_cells_sound (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate) (input : Lanes)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedCells certificate totalAddRows) :
    observedCells = expectedCells certificate totalAddRows ∧
      executeNormalized certificate input = denotation sourceBytes input :=
  ⟨hcells, checked_relation_sound sourceBytes normalizedBytes certificate input hrelation⟩

end S31.Functional.SSAAirColumnCells
