import S31.Gadgets.Functional.Correspondence.HonestSourceCellWitness

/-!
Bounds for the source-projected native direct-Gate fixed columns. The source
byte parser bounds the number of instructions, while successful arithmetic
execution bounds every positional operand and result index. Together these
give actual canonical M31 bounds for every source address and multiplicity.

This is a property of Lean's modeled `expectedCells`, not an assertion that
native emitted or committed columns equal those cells.
-/

namespace S31.Functional.Correspondence.SourcePhysicalAddressBounds

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSAAirRows
open S31.Functional.Correspondence.SourceDeterminedDirectRows

private theorem trace_indices_bounded {values final : List Lanes}
    {instructions : List Instruction}
    (htrace : AcceptsTrace values instructions final) :
    ∀ instruction ∈ instructions,
      instruction.id < values.length + instructions.length ∧
      instruction.lhs < values.length + instructions.length ∧
      instruction.rhs < values.length + instructions.length := by
  induction htrace with
  | done => simp
  | @next values final instruction rest output hrow _ ih =>
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        obtain ⟨_, _, hid, hleft, hright, _⟩ := hrow
        have hl : instruction.lhs < values.length :=
          (List.getElem?_eq_some_iff.mp hleft).1
        have hr : instruction.rhs < values.length :=
          (List.getElem?_eq_some_iff.mp hright).1
        simp only [List.length_cons]
        omega
      · have h := ih item htail
        simp only [List.length_append, List.length_singleton] at h
        simp only [List.length_cons]
        omega

private theorem source_read_count_le (instructions : List Instruction)
    (id start : Nat) :
    instructions.foldl
      (fun count instruction =>
        count + (if instruction.lhs == id then 1 else 0) +
          (if instruction.rhs == id then 1 else 0)) start ≤
      start + 2 * instructions.length := by
  induction instructions generalizing start with
  | nil => simp
  | cons instruction rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      have h := ih (start + (if instruction.lhs == id then 1 else 0) +
        (if instruction.rhs == id then 1 else 0))
      by_cases hl : instruction.lhs == id <;>
        by_cases hr : instruction.rhs == id <;>
        simp [hl, hr] at h ⊢ <;> omega

/-- A use count includes at most two reads per source instruction and four
public result-mask reads. -/
theorem source_uses_bounded (certificate : Certificate) (id : Nat) :
    sourceUses certificate id ≤
      2 * certificate.instructions.length + 4 := by
  have h := source_read_count_le certificate.instructions id 0
  simp only [sourceUses] at *
  split_ifs <;> omega

/-- Every positional source operand and result fits an address below 39 for
an executable certificate with the parser's sixteen-instruction budget. -/
theorem trace_source_addresses_bounded {final : List Lanes}
    (certificate : Certificate) (input : Lanes)
    (hbudget : certificate.instructions.length ≤ 16)
    (htrace : AcceptsTrace [input] certificate.instructions final) :
    ∀ instruction ∈ certificate.instructions,
      address instruction.lhs < 39 ∧
      address instruction.rhs < 39 ∧
      address instruction.id < 39 := by
  intro instruction hmember
  have h := trace_indices_bounded htrace instruction hmember
  simp only [List.length_singleton] at h
  unfold address
  omega

/-- Every modeled source-projected AIR cell has canonical field-address
and multiplicity words. No unproved numeric bound is needed to attach
`fixedMatches` to an honest decoded source trace. -/
theorem expected_source_cells_canonical {final : List Lanes}
    (certificate : Certificate) (input : Lanes)
    (hbudget : certificate.instructions.length ≤ 16)
    (htrace : AcceptsTrace [input] certificate.instructions final) :
    ∀ cell ∈ expectedCells certificate (compiledAddRows certificate),
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
      cell.out < 2147483647 ∧ cell.mults < 2147483647 := by
  intro cell hcell
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hcell
  have hinstruction : pair.1 ∈ certificate.instructions := by
    exact (List.of_mem_zip hpair).1
  have haddr := trace_source_addresses_bounded certificate input
    hbudget htrace pair.1 hinstruction
  have hshape := (expected_rows_opcode_and_addresses certificate
    (compiledAddRows certificate)) pair hpair
  have hm := source_uses_bounded certificate pair.1.id
  simp only [expectedCell, hshape.2.2.1, hshape.2.2.2.1,
    hshape.2.2.2.2, sourceUses] at *
  omega

end S31.Functional.Correspondence.SourcePhysicalAddressBounds
