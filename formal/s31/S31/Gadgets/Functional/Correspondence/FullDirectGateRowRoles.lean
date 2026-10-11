import S31.Gadgets.Functional.Correspondence.SourcePhysicalAddressBounds

/-!
An exact, source-derived *operation-role* partition of the bounded direct
Gate profile's 512 physical rows. It distinguishes source arithmetic, public
pack/unpack/copy arithmetic, and the constant-derivation/padding island.

The theorem fixes every grouped role and its row count from accepted bytes.
It does not reproduce the native constant-island gate triples or prove that
native preprocessed columns or a PCS commitment equal this modeled roster.
-/

namespace S31.Functional.Correspondence.FullDirectGateRowRoles

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.SourceDeterminedDirectRows

/-- Eleven disjoint physical row roles in the grouped direct-Gate profile. -/
inductive RowRole where
  | inputPackAdd
  | sourceAdd
  | publicCopyAdd
  | constantAdd
  | constantSub
  | inputPackMul
  | outputInverseMul
  | constantMul
  | sourcePointwiseMul
  | outputMask
  | inputIdentity
deriving DecidableEq, Repr

/-- The complete role at each of the 512 physical rows. Source arithmetic
fills the leading portion of the add and pointwise partitions; public rows
occupy fixed-width bands; the remainder is constant derivation and padding.
-/
def rowRole (certificate : Certificate) (row : Fin 512) : RowRole :=
  let r := row.val
  let a := sourceAddCount certificate
  let m := sourceMulCount certificate
  let A := compiledAddRows certificate
  if r < 3 then .inputPackAdd
  else if r < 3 + a then .sourceAdd
  else if r < 11 + a then .publicCopyAdd
  else if r < A then .constantAdd
  else if r = A then .constantSub
  else if r < A + 4 then .inputPackMul
  else if r < A + 7 then .outputInverseMul
  else if r < A + 28 then .constantMul
  else if r < A + 28 + m then .sourcePointwiseMul
  else if r < A + 32 + m then .outputMask
  else .inputIdentity

private theorem fold_add_mul_count (instructions : List Instruction)
    (a m : Nat) :
    instructions.foldl
      (fun n instruction => n + if instruction.multiply then 0 else 1) a +
    instructions.foldl
      (fun n instruction => n + if instruction.multiply then 1 else 0) m =
      a + m + instructions.length := by
  induction instructions generalizing a m with
  | nil => simp
  | cons instruction rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      have h := ih (a + if instruction.multiply then 0 else 1)
        (m + if instruction.multiply then 1 else 0)
      cases hi : instruction.multiply <;> simp [hi] at h ⊢ <;> omega

/-- Each admitted source instruction accounts for exactly one of the two
source operation partitions. -/
theorem source_counts_sum (certificate : Certificate) :
    sourceAddCount certificate + sourceMulCount certificate =
      certificate.instructions.length := by
  simpa [sourceAddCount, sourceMulCount] using
    fold_add_mul_count certificate.instructions 0 0

/-- The add partition has enough room after the three pack adds, all source
adds and eight public copies for the constant/padding island. -/
theorem constant_add_start_bounded (certificate : Certificate)
    (hbudget : certificate.instructions.length ≤ 16) :
    11 + sourceAddCount certificate ≤ compiledAddRows certificate := by
  have hsum := source_counts_sum certificate
  unfold compiledAddRows
  omega

/-- The source-independent constant/padding island has exactly `465 - n`
add rows, one subtraction row and 21 ordinary multiplication rows. These
counts are source-dependent only through the instruction count `n`, with no
caller-chosen row-total or hidden arithmetic producers. -/
theorem constant_island_row_counts (certificate : Certificate)
    (hbudget : certificate.instructions.length ≤ 16) :
    compiledAddRows certificate - (11 + sourceAddCount certificate) =
      465 - certificate.instructions.length ∧
    (compiledAddRows certificate - (11 + sourceAddCount certificate)) +
      1 + 21 = 487 - certificate.instructions.length := by
  have hsum := source_counts_sum certificate
  have hspace := constant_add_start_bounded certificate hbudget
  unfold compiledAddRows at *
  constructor <;> omega

/-- Every physical row falls into exactly one explicitly described grouped
interval. The final interval ends at row 511 because the source-derived
partition equation ends at 512. The disjunction is intentionally at the
operation-role level; constant gate addresses remain a separate obligation.
-/
theorem direct_bytes_full_row_roles
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (row : Fin 512) :
    (rowRole certificate row = .inputPackAdd ∧ row.val < 3) ∨
    (rowRole certificate row = .sourceAdd ∧
      3 ≤ row.val ∧ row.val < 3 + sourceAddCount certificate) ∨
    (rowRole certificate row = .publicCopyAdd ∧
      3 + sourceAddCount certificate ≤ row.val ∧
      row.val < 11 + sourceAddCount certificate) ∨
    (rowRole certificate row = .constantAdd ∧
      11 + sourceAddCount certificate ≤ row.val ∧
      row.val < compiledAddRows certificate) ∨
    (rowRole certificate row = .constantSub ∧
      row.val = compiledAddRows certificate) ∨
    (rowRole certificate row = .inputPackMul ∧
      compiledAddRows certificate + 1 ≤ row.val ∧
      row.val < compiledAddRows certificate + 4) ∨
    (rowRole certificate row = .outputInverseMul ∧
      compiledAddRows certificate + 4 ≤ row.val ∧
      row.val < compiledAddRows certificate + 7) ∨
    (rowRole certificate row = .constantMul ∧
      compiledAddRows certificate + 7 ≤ row.val ∧
      row.val < compiledAddRows certificate + 28) ∨
    (rowRole certificate row = .sourcePointwiseMul ∧
      compiledAddRows certificate + 28 ≤ row.val ∧
      row.val < compiledAddRows certificate + 28 +
        sourceMulCount certificate) ∨
    (rowRole certificate row = .outputMask ∧
      compiledAddRows certificate + 28 + sourceMulCount certificate ≤ row.val ∧
      row.val < compiledAddRows certificate + 32 +
        sourceMulCount certificate) ∨
    (rowRole certificate row = .inputIdentity ∧
      compiledAddRows certificate + 32 + sourceMulCount certificate ≤ row.val ∧
      row.val < 512) := by
  have hbudget := checked_relation_instruction_bound sourceBytes
    normalizedBytes certificate hcheck
  have hspace := constant_add_start_bounded certificate hbudget
  have hpartition := direct_bytes_partition sourceBytes normalizedBytes
    certificate hcheck
  have hrow := row.isLt
  dsimp only [rowRole]
  split_ifs <;> simp_all <;> omega

/-- Every source-projected cell lands in its matching source-operation band
of the complete 512-row model, with the opcode selected by its checked
instruction. The proposition concerns `expectedCells`; native fixture parity
is established separately. -/
theorem checked_source_cell_role
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (cell : ColumnCell)
    (hcell : cell ∈ expectedCells certificate (compiledAddRows certificate)) :
    ∃ physicalRow : Fin 512,
      physicalRow.val = cell.traceRow ∧
      ((cell.addFlag = 1 ∧ rowRole certificate physicalRow = .sourceAdd) ∨
       (cell.pointwiseMulFlag = 1 ∧
         rowRole certificate physicalRow = .sourcePointwiseMul)) := by
  have hroster := direct_bytes_projected_roster sourceBytes normalizedBytes
    certificate hcheck
  have hbound : cell.traceRow < 512 := by
    have h := hroster.2.2 cell
      (List.mem_append.mpr (Or.inl hcell))
    simpa using h
  let physicalRow : Fin 512 := ⟨cell.traceRow, hbound⟩
  refine ⟨physicalRow, rfl, ?_⟩
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hcell
  have hnative : pair.2 ∈ expectedRows certificate
      (compiledAddRows certificate) := (List.of_mem_zip hpair).2
  have hband := expected_rows_partition certificate
    (compiledAddRows certificate) pair.2 hnative
  have hshape := (expected_rows_opcode_and_addresses certificate
    (compiledAddRows certificate)) pair hpair
  have hspace := constant_add_start_bounded certificate
    (checked_relation_instruction_bound sourceBytes normalizedBytes
      certificate hcheck)
  have hpartition := direct_bytes_partition sourceBytes normalizedBytes
    certificate hcheck
  have hroles := direct_bytes_full_row_roles sourceBytes normalizedBytes
    certificate hcheck physicalRow
  cases hkind : pair.1.multiply with
  | false =>
      have hrow : 3 ≤ physicalRow.val ∧
          physicalRow.val < 3 + sourceAddCount certificate := by
        simpa [physicalRow, expectedCell, hshape.2.1, hkind] using hband
      have hrole : rowRole certificate physicalRow = .sourceAdd := by
        rcases hroles with h | h | h | h | h | h | h | h | h | h | h <;>
          simp_all <;> omega
      exact Or.inl ⟨by simp [expectedCell, hkind], hrole⟩
  | true =>
      have hrow : compiledAddRows certificate + 28 ≤ physicalRow.val ∧
          physicalRow.val < compiledAddRows certificate + 28 +
            sourceMulCount certificate := by
        simpa [physicalRow, expectedCell, hshape.2.1, hkind] using hband
      have hrole : rowRole certificate physicalRow = .sourcePointwiseMul := by
        rcases hroles with h | h | h | h | h | h | h | h | h | h | h <;>
          simp_all <;> omega
      exact Or.inr ⟨by simp [expectedCell, hkind], hrole⟩

end S31.Functional.Correspondence.FullDirectGateRowRoles
