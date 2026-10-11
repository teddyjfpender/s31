import S31.Gadgets.Functional.Correspondence.AliasCanonicalIrBytes
import S31.Gadgets.Functional.Correspondence.AliasRawGateSoundness

/-!
The bounded direct-Gate layout has exactly 512 arithmetic rows: one fixed
subtraction, 27 fixed ordinary multiplications, eight fixed pointwise
multiplications, one pointwise row per checked source multiplication, and the
remaining addition rows. The source byte checker caps arithmetic producers at
16, so the addition-row count is determined by the checked source certificate.

This closes the *modeled layout count* premise for accepted source bytes. It
does not prove that native Zig emitted this layout, that a committed fixed
column equals the modeled roster, or that verifier acceptance authenticates
decoded cells.
-/

namespace S31.Functional.Correspondence.SourceDeterminedDirectRows

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.AliasRawGateSoundness

/-- The native profile's addition partition is forced by the checked number
of source pointwise multiplication producers. -/
def compiledAddRows (certificate : Certificate) : Nat :=
  476 - sourceMulCount certificate

private theorem partition_of_budget (certificate : Certificate)
    (hbudget : certificate.instructions.length ≤ 16) :
    compiledAddRows certificate + 1 + 27 +
      sourceMulCount certificate + 8 = 2 ^ 9 := by
  have hmul := source_mul_count_bounded certificate
  unfold compiledAddRows
  omega

/-- Exact direct-source and normalized bytes determine a valid 512-row
partition without a free `totalAddRows` parameter. -/
theorem direct_bytes_partition (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    compiledAddRows certificate + 1 + 27 +
      sourceMulCount certificate + 8 = 2 ^ 9 := by
  exact partition_of_budget certificate
    (checked_relation_instruction_bound sourceBytes normalizedBytes
      certificate hcheck)

/-- Alias bindings and redundant parentheses have no physical producer.
The canonical byte check fixes the same bounded producer count and therefore
the same source-determined partition. -/
theorem canonical_alias_bytes_partition
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    compiledAddRows certificate + 1 + 27 +
      sourceMulCount certificate + 8 = 2 ^ 9 := by
  obtain ⟨_, _, _, _, _, hrelation, _⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate (fun _ => 0) hcheck
  exact partition_of_budget certificate
    (checked_alias_relation_instruction_bound sourceBytes normalizedBytes
      certificate hrelation)

/-- Under the native profile equation, no second addition-row count can
produce the same accepted source certificate. This rules out choosing a
different grouped row offset while claiming the 512-row layout. -/
theorem partition_count_unique (certificate : Certificate)
    (totalAddRows : Nat)
    (hpartition : totalAddRows + 1 + 27 +
      sourceMulCount certificate + 8 = 2 ^ 9) :
    totalAddRows = compiledAddRows certificate := by
  unfold compiledAddRows
  omega

/-- Every accepted direct source has a complete modeled instruction plan,
distinct physical positions for source and public boundary cells, and all
projected positions inside the 512-row trace. The prior row-roster theorem's
partition premise is discharged from exact source bytes here. -/
theorem direct_bytes_projected_roster
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    SourcePlan certificate
      (expectedCells certificate (compiledAddRows certificate)) ∧
    (((expectedCells certificate (compiledAddRows certificate) ++
        (expectedInputCells certificate (compiledAddRows certificate) ++
          expectedOutputCells certificate (compiledAddRows certificate))).map
      ColumnCell.traceRow)).Nodup ∧
    (∀ cell ∈ expectedCells certificate (compiledAddRows certificate) ++
        (expectedInputCells certificate (compiledAddRows certificate) ++
          expectedOutputCells certificate (compiledAddRows certificate)),
      cell.traceRow < 2 ^ 9) := by
  exact checked_relation_modeled_row_roster sourceBytes normalizedBytes
    certificate (compiledAddRows certificate) hcheck
    (direct_bytes_partition sourceBytes normalizedBytes certificate hcheck)

/-- The source-derived partition also fixes the complete instruction order,
operation selectors, circuit and Gate wire addresses, and each projected
source/public row position. No row-count parameter is supplied by the caller.
-/
theorem direct_bytes_exact_row_roster
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    (∀ pair ∈ certificate.instructions.zip
        (expectedRows certificate (compiledAddRows certificate)),
      pair.2.circuitRow = 5 + pair.1.id ∧
      pair.2.multiply = pair.1.multiply ∧
      pair.2.in0 = address pair.1.lhs ∧
      pair.2.in1 = address pair.1.rhs ∧
      pair.2.out = address pair.1.id) ∧
    ((expectedRows certificate (compiledAddRows certificate)).map
      NativeSourceRow.multiply =
        certificate.instructions.map Instruction.multiply) ∧
    ((expectedCells certificate (compiledAddRows certificate)).map
      (fun cell => (cell.addFlag, cell.pointwiseMulFlag)) =
        certificate.instructions.map (fun instruction =>
          (if instruction.multiply then 0 else 1,
           if instruction.multiply then 1 else 0))) ∧
    SourcePlan certificate
      (expectedCells certificate (compiledAddRows certificate)) ∧
    (((expectedCells certificate (compiledAddRows certificate) ++
        (expectedInputCells certificate (compiledAddRows certificate) ++
          expectedOutputCells certificate (compiledAddRows certificate))).map
      ColumnCell.traceRow)).Nodup ∧
    (∀ cell ∈ expectedCells certificate (compiledAddRows certificate) ++
        (expectedInputCells certificate (compiledAddRows certificate) ++
          expectedOutputCells certificate (compiledAddRows certificate)),
      cell.traceRow < 2 ^ 9) := by
  exact checked_relation_modeled_exact_row_roster sourceBytes normalizedBytes
    certificate (compiledAddRows certificate) hcheck
    (direct_bytes_partition sourceBytes normalizedBytes certificate hcheck)

/-- Canonical alias admission determines the same grouped source schedule.
In the modeled profile, every source and public-boundary cell has a distinct
physical position. The body has no extra alias rows, and its operation list
remains the exact instruction list extracted from source bytes. -/
theorem canonical_alias_projected_rows_distinct
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    SourcePlan certificate
      (expectedCells certificate (compiledAddRows certificate)) ∧
    ((expectedRows certificate (compiledAddRows certificate)).map
      NativeSourceRow.multiply =
        certificate.instructions.map Instruction.multiply) ∧
    (((expectedCells certificate (compiledAddRows certificate) ++
        (expectedInputCells certificate (compiledAddRows certificate) ++
          expectedOutputCells certificate (compiledAddRows certificate))).map
      ColumnCell.traceRow)).Nodup := by
  obtain ⟨_, _, _, _, _, hrelation, _⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate (fun _ => 0) hcheck
  have hbudget := checked_alias_relation_instruction_bound sourceBytes
    normalizedBytes certificate hrelation
  have ha := source_add_count_bounded certificate
  have hm := source_mul_count_bounded certificate
  have hspace :
      11 + sourceAddCount certificate ≤ compiledAddRows certificate := by
    unfold compiledAddRows
    omega
  have hsource :
      ((expectedCells certificate (compiledAddRows certificate)).map
        ColumnCell.traceRow).Nodup := by
    apply expected_cells_trace_rows_nodup
    omega
  have hpublic := expected_public_rows_nodup certificate
    (compiledAddRows certificate) hspace
  have hdisjoint : List.Disjoint
      ((expectedCells certificate (compiledAddRows certificate)).map
        ColumnCell.traceRow)
      ((expectedInputCells certificate (compiledAddRows certificate) ++
        expectedOutputCells certificate (compiledAddRows certificate)).map
          ColumnCell.traceRow) := by
    intro physicalRow hsourceRow hpublicRow
    obtain ⟨sourceCell, hsourceCell, hsourceEq⟩ :=
      List.mem_map.mp hsourceRow
    obtain ⟨publicCell, hpublicCell, hpublicEq⟩ :=
      List.mem_map.mp hpublicRow
    exact expected_source_public_rows_disjoint certificate
      (compiledAddRows certificate) hspace sourceCell hsourceCell
      publicCell hpublicCell (hsourceEq.trans hpublicEq.symm)
  refine ⟨source_plan_expected certificate (compiledAddRows certificate),
    expected_rows_opcode_sequence certificate (compiledAddRows certificate),
    ?_⟩
  rw [List.map_append]
  exact hsource.append hpublic hdisjoint

end S31.Functional.Correspondence.SourceDeterminedDirectRows
