import S31.Gadgets.Functional.Correspondence.FullDirectGateRowRoles
import S31.Gadgets.Functional.Correspondence.SyntheticSourceTraceCompletion

/-!
A proof-carrying certificate checker for the source-independent direct-Gate
constant derivation and padding island. The certificate contains exact fixed
gate triples and one coherent address-to-value table. The executable check
requires complete constant-band row coverage, the right one-hot operation
selector, isolated native addresses, canonical field words, local QM31
arithmetic, unique producer addresses, and the basis/inverse constants that
the public pack/unpack path consumes.

The checker is reusable for any admitted bounded direct source. It is not a
Lean implementation of Zig's gate emitter or of the Python base-256 constant
schedule. A native package must separately bind the checked certificate to
its exported fixed columns and preprocessed commitment root.
-/

namespace S31.Functional.Correspondence.NativeConstantIslandCertificate

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSACertificate
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAOutputAirCells
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.FullDirectGateRowRoles

/-- Every constant/padding physical row, in grouped native order. The source
instruction count determines the add-padding extent; source op mix determines
the add partition offset, but cannot add another constant row. -/
def constantPositions (certificate : Certificate) : List Nat :=
  let a := sourceAddCount certificate
  let A := compiledAddRows certificate
  (List.range (A - (11 + a))).map (11 + a + ·) ++
    [A] ++ (List.range 21).map (A + 7 + ·)

/-- The three constant-row intervals are independent of all source and
public boundary row bands. This is the arithmetic shape used when joining
the constant island to the projected roster. -/
theorem constant_position_band (certificate : Certificate)
    (hbudget : certificate.instructions.length ≤ 16) (row : Nat)
    (hrow : row ∈ constantPositions certificate) :
    (11 + sourceAddCount certificate ≤ row ∧
      row < compiledAddRows certificate) ∨
    row = compiledAddRows certificate ∨
    (compiledAddRows certificate + 7 ≤ row ∧
      row < compiledAddRows certificate + 28) := by
  have hspace := constant_add_start_bounded certificate hbudget
  simp only [constantPositions, List.mem_append, List.mem_map,
    List.mem_singleton] at hrow
  rcases hrow with (h | h) | h
  · obtain ⟨index, hindex, heq⟩ := h
    have hi := List.mem_range.mp hindex
    left
    constructor <;> omega
  · exact Or.inr (Or.inl h)
  · obtain ⟨index, hindex, heq⟩ := h
    have hi := List.mem_range.mp hindex
    exact Or.inr (Or.inr (by omega))

/-- Constants may occupy only the three externally fixed seed addresses,
the two nontrivial basis addresses, the three source-length-dependent inverse
addresses, and the fresh island allocation above all data wires. -/
def constantAddress (certificate : Certificate) (address : Nat) : Prop :=
  address = 0 ∨ address = 1 ∨ address = 2 ∨
    address = 15 ∨ address = 16 ∨
    address = 25 + certificate.instructions.length ∨
    address = 28 + certificate.instructions.length ∨
    address = 31 + certificate.instructions.length ∨
    33 + certificate.instructions.length ≤ address

instance (certificate : Certificate) (address : Nat) :
    Decidable (constantAddress certificate address) := by
  unfold constantAddress
  infer_instance

def roleAtNat (certificate : Certificate) (r : Nat) : Option RowRole :=
  if h : r < 512 then some (rowRole certificate ⟨r, h⟩) else none

/-- The complete one-hot selector must agree with the grouped physical
constant role at this row. -/
def constantSelector (certificate : Certificate) (cell : ColumnCell) : Prop :=
  (roleAtNat certificate cell.traceRow = some .constantAdd ∧
    cell.addFlag = 1 ∧ cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
    cell.pointwiseMulFlag = 0) ∨
  (roleAtNat certificate cell.traceRow = some .constantSub ∧
    cell.addFlag = 0 ∧ cell.subFlag = 1 ∧ cell.mulFlag = 0 ∧
    cell.pointwiseMulFlag = 0) ∨
  (roleAtNat certificate cell.traceRow = some .constantMul ∧
    cell.addFlag = 0 ∧ cell.subFlag = 0 ∧ cell.mulFlag = 1 ∧
    cell.pointwiseMulFlag = 0)

instance (certificate : Certificate) (cell : ColumnCell) :
    Decidable (constantSelector certificate cell) := by
  unfold constantSelector
  infer_instance

/-- A finite value table provides the same QM31 value at every use and
production of a given native address. Missing entries map to zero, but every
checked constant gate operand/output must have an in-bounds entry. -/
def wireOfValues (values : List Quad) (address : Nat) : Quad :=
  (values[address]?).getD (base 0)

def arithmeticCheck (values : List Quad) (cell : ColumnCell) : Bool :=
  (residuals (cellFlags cell)
    (wireOfValues values cell.in0)
    (wireOfValues values cell.in1)
    (wireOfValues values cell.out)).all (fun root => decide (root = 0))

/-- One source-independent native fixed gate triple with its honest values.
The address-isolation check prevents a constant gate from reading or writing
source/public data wires, except the intentionally shared seed/basis wires.
-/
def ConstantCellSound (certificate : Certificate) (values : List Quad)
    (cell : ColumnCell) : Prop :=
  constantSelector certificate cell ∧
  constantAddress certificate cell.in0 ∧
  constantAddress certificate cell.in1 ∧
  constantAddress certificate cell.out ∧
  cell.in0 < values.length ∧ cell.in1 < values.length ∧
  cell.out < values.length ∧
  cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
  cell.out < 2147483647 ∧ cell.mults < 2147483647 ∧
  arithmeticCheck values cell = true

instance (certificate : Certificate) (values : List Quad) (cell : ColumnCell) :
    Decidable (ConstantCellSound certificate values cell) := by
  unfold ConstantCellSound
  infer_instance

/-- Fixed public constants and the three multiplicative inverse-basis
values are pinned at their actual native addresses. The arithmetic checker
also requires their producers to occur in the constant row list. -/
def SeedValues (certificate : Certificate) (values : List Quad) : Prop :=
  values[0]? = some (base 0) ∧
  values[1]? = some (unit ⟨0, by decide⟩) ∧
  values[2]? = some (unit ⟨2, by decide⟩) ∧
  values[15]? = some (unit ⟨1, by decide⟩) ∧
  values[16]? = some (unit ⟨3, by decide⟩) ∧
  values[25 + certificate.instructions.length]? =
    some (unitInverse ⟨1, by decide⟩) ∧
  values[28 + certificate.instructions.length]? =
    some (unitInverse ⟨2, by decide⟩) ∧
  values[31 + certificate.instructions.length]? =
    some (unitInverse ⟨3, by decide⟩)

instance (certificate : Certificate) (values : List Quad) :
    Decidable (SeedValues certificate values) := by
  unfold SeedValues
  infer_instance

def seedProducerAddresses (certificate : Certificate) : List Nat :=
  [0, 1, 2, 15, 16,
    25 + certificate.instructions.length,
    28 + certificate.instructions.length,
    31 + certificate.instructions.length]

/-- An exact, finite checker contract. The `all` predicate is executable;
its theorem below extracts actual field arithmetic, rather than assuming
`cellAccepts` as a free premise. -/
def Valid (certificate : Certificate) (cells : List ColumnCell)
    (values : List Quad) : Prop :=
  cells.map ColumnCell.traceRow = constantPositions certificate ∧
  cells.all (fun cell => decide (ConstantCellSound certificate values cell)) = true ∧
  (cells.map ColumnCell.out).Nodup ∧
  SeedValues certificate values ∧
  (seedProducerAddresses certificate).all
    (fun address => decide (address ∈ cells.map ColumnCell.out)) = true

instance (certificate : Certificate) (cells : List ColumnCell)
    (values : List Quad) : Decidable (Valid certificate cells values) := by
  unfold Valid
  infer_instance

def check (certificate : Certificate) (cells : List ColumnCell)
    (values : List Quad) : Bool :=
  decide (Valid certificate cells values)

theorem check_sound (certificate : Certificate) (cells : List ColumnCell)
    (values : List Quad) (hcheck : check certificate cells values = true) :
    Valid certificate cells values := by
  simpa [check] using hcheck

/-- Every checked island gate has the exact selector role, isolated native
addresses, canonical fixed words, and a vanishing local operation relation
under one coherent finite value table. -/
theorem checked_cells_sound (certificate : Certificate)
    (cells : List ColumnCell) (values : List Quad)
    (hcheck : check certificate cells values = true) :
    ∀ cell ∈ cells, ConstantCellSound certificate values cell := by
  have hvalid := check_sound certificate cells values hcheck
  intro cell hcell
  have h := (List.all_eq_true.mp hvalid.2.1) cell hcell
  exact of_decide_eq_true h

/-- The executable residual check proves all nine installed QM31 operation
polynomials vanish at each certified source-independent native cell. -/
theorem checked_cells_arithmetic (certificate : Certificate)
    (cells : List ColumnCell) (values : List Quad)
    (hcheck : check certificate cells values = true) :
    ∀ cell ∈ cells, cellAccepts cell (wireOfValues values) := by
  intro cell hcell
  have hsound := checked_cells_sound certificate cells values hcheck cell hcell
  rcases hsound with ⟨_, _, _, _, _, _, _, _, _, _, _, hair⟩
  unfold arithmeticCheck at hair
  intro root hroot
  exact of_decide_eq_true ((List.all_eq_true.mp hair) root hroot)

/-- The checked list has exactly all required source-independent rows, once
each, and precisely `487-n` rows for an admitted bounded source. -/
theorem checked_rows_count (certificate : Certificate)
    (cells : List ColumnCell) (values : List Quad)
    (hbudget : certificate.instructions.length ≤ 16)
    (hcheck : check certificate cells values = true) :
    cells.map ColumnCell.traceRow = constantPositions certificate ∧
    cells.length = 487 - certificate.instructions.length := by
  have hvalid := check_sound certificate cells values hcheck
  have hconstant := constant_island_row_counts certificate hbudget
  constructor
  · exact hvalid.1
  · have hlen := congrArg List.length hvalid.1
    simp only [constantPositions, List.length_append, List.length_map,
      List.length_range, List.length_singleton] at hlen
    omega

end S31.Functional.Correspondence.NativeConstantIslandCertificate
