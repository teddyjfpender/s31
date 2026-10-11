import S31.Gadgets.Functional.Correspondence.AcceptedPublicPhysicalTrace
import S31.Gadgets.Functional.Correspondence.SourcePhysicalAddressBounds

/-!
Canonical fixed-column words for the combined projected direct-Gate source
and public-boundary roster. This is a modeled decoded trace, not an assertion
that production committed fixed columns equal the model.
-/

namespace S31.Functional.Correspondence.AcceptedPublicFixedCells

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.SourcePhysicalAddressBounds
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
open S31.Functional.Correspondence.HonestPublicBoundaryWire

/-- A byte-admitted certificate's selected output is a real SSA wire in the
executed value list, whose length is fixed by the instruction count. -/
theorem checked_selected_output_id_bound
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    certificate.output < 1 + certificate.instructions.length := by
  let input : Lanes := fun _ => 0
  have hparse : ∃ parsed, parseBytes sourceBytes = some parsed := by
    unfold checkRelation at hcheck
    cases hp : parseBytes sourceBytes with
    | none => simp [hp] at hcheck
    | some parsed => exact ⟨parsed, rfl⟩
  obtain ⟨parsed, hparse⟩ := hparse
  let output := parsed.meaning.eval input
  have hdenotation : denotation sourceBytes input = some output := by
    simp [denotation, hparse, output]
  have hexecute : executeNormalized certificate input = some output := by
    rw [checked_relation_sound sourceBytes normalizedBytes certificate input
      hcheck]
    exact hdenotation
  rw [execute_normalized_eq_execute] at hexecute
  unfold execute at hexecute
  cases hrun : certificate.instructions.foldlM executeStep [input] with
  | none => simp [hrun] at hexecute
  | some final =>
      have hselected : final[certificate.output]? = some output := by
        simpa [hrun] using hexecute
      have htrace := S31.Functional.SSAAirRows.executing_trace_has_air_rows
        certificate.instructions [input] final hrun
      have hlen : final.length = 1 + certificate.instructions.length := by
        simpa using accepted_trace_length htrace
      have hbound := (List.getElem?_eq_some_iff.mp hselected).1
      omega

theorem public_cells_canonical
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∀ cell ∈ expectedInputCells certificate (compiledAddRows certificate) ++
        expectedOutputCells certificate (compiledAddRows certificate),
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647 := by
  have hbudget := checked_relation_instruction_bound sourceBytes
    normalizedBytes certificate hcheck
  have houtput := checked_selected_output_id_bound sourceBytes
    normalizedBytes certificate hcheck
  have huse : sourceInputUses certificate ≤
      2 * certificate.instructions.length + 4 := by
    have h := source_uses_bounded certificate 0
    simp only [sourceUses, sourceInputUses] at h ⊢
    omega
  intro cell hcell
  simp only [expectedInputCells, expectedOutputCells,
    expectedMaskCells, List.mem_append] at hcell
  rcases hcell with hinput | houtputCell
  · rcases hinput with ((hpackAdd | hpackMul) | hcopy) | hself
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hpackAdd
      have hii : i < 3 := List.mem_range.mp hi
      interval_cases i <;> simp [expectedPackAddCell] <;> omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hpackMul
      have hii : i < 3 := List.mem_range.mp hi
      interval_cases i <;>
        simp [expectedPackMulCell, maskBasisAddress]
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hcopy
      have hii : i < 4 := List.mem_range.mp hi
      simp [expectedInputCopyCell]
      omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hself
      have hii : i < 4 := List.mem_range.mp hi
      simp [expectedInputSelfCell]
      omega
  · rcases houtputCell with (hmask | hinverse) | hcopy
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmask
      have hii : i < 4 := List.mem_range.mp hi
      interval_cases i <;>
        simp [expectedMaskCell, address, maskAddress,
          maskBasisAddress] <;> omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hinverse
      have hii : i < 3 := List.mem_range.mp hi
      interval_cases i <;>
        simp [expectedInverseCell, maskAddress, resultAddress] <;> omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hcopy
      have hii : i < 4 := List.mem_range.mp hi
      interval_cases i <;>
        simp [expectedCopyCell, resultAddress] <;> omega

theorem projected_cells_canonical
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∀ cell ∈ projectedCells certificate,
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647 := by
  intro cell hcell
  rcases List.mem_append.mp hcell with hsource | hpublic
  · exact checked_direct_source_cells_canonical sourceBytes normalizedBytes
      certificate hcheck cell hsource
  · exact public_cells_canonical sourceBytes normalizedBytes certificate
      hcheck cell hpublic

/-- Each source/public projected cell appears at its intended distinct row
with exact selector, address, and multiplicity fixed words in the synthetic
decoded 512-row trace. Its arithmetic witness is supplied separately by
`checked_direct_projected_trace_exists`. -/
theorem checked_projected_fixed_matches
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (wire : Nat → Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∀ cell ∈ projectedCells certificate,
      fixedMatches (trace (projectedCells certificate) wire) cell := by
  have hroster := direct_bytes_projected_roster sourceBytes
    normalizedBytes certificate hcheck
  have hnodup : ((projectedCells certificate).map ColumnCell.traceRow).Nodup := by
    simpa [projectedCells] using hroster.2.1
  have hbound : ∀ cell ∈ projectedCells certificate,
      cell.traceRow < 512 := by
    intro cell hcell
    have h := hroster.2.2 cell (by simpa [projectedCells] using hcell)
    norm_num at h
    exact h
  have hcanonical := projected_cells_canonical sourceBytes normalizedBytes
    certificate hcheck
  intro cell hcell
  obtain ⟨i, hi, hflags, hin0, hin1, hout, hmult⟩ :=
    zeroTrace_fixed (projectedCells certificate) hnodup hbound hcanonical
      [] cell hcell
  refine ⟨i, hi, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [trace, row] using hflags
  · simpa [trace, row] using hin0
  · simpa [trace, row] using hin1
  · simpa [trace, row] using hout
  · simpa [trace, row] using hmult

/-- A single concrete 512-row decoded trace now satisfies every installed
local arithmetic root *and* has exact fixed selectors, addresses, and
multiplicities for every source/input/output projected cell. The remainder
is synthetic zero-add padding, so full native fixed-column equality and
Gate balance are still not asserted. -/
theorem checked_direct_projected_physical_trace_exists
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      denotation sourceBytes input = some output ∧
      allArithmeticRootsZero (trace (projectedCells certificate) wire) ∧
      (∀ cell ∈ projectedCells certificate,
        fixedMatches (trace (projectedCells certificate) wire) cell) ∧
      wire (address certificate.output) = packM31 output := by
  obtain ⟨wire, output, hdenotation, harithmetic, hselected⟩ :=
    checked_direct_projected_trace_exists sourceBytes normalizedBytes
      certificate input hcheck
  exact ⟨wire, output, hdenotation, harithmetic,
    checked_projected_fixed_matches sourceBytes normalizedBytes certificate
      wire hcheck, hselected⟩

/-- Literal-byte entry point for the combined selected fixed/main witness. -/
theorem checked_u8_direct_projected_physical_trace_exists
    (sourceBytes normalizedBytes : List UInt8) (certificate : Certificate)
    (input : Lanes)
    (hcheck : checkRelation (sourceBytes.map UInt8.toNat)
      (normalizedBytes.map UInt8.toNat) = some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      denotation (sourceBytes.map UInt8.toNat) input = some output ∧
      allArithmeticRootsZero (trace (projectedCells certificate) wire) ∧
      (∀ cell ∈ projectedCells certificate,
        fixedMatches (trace (projectedCells certificate) wire) cell) ∧
      wire (address certificate.output) = packM31 output :=
  checked_direct_projected_physical_trace_exists
    (sourceBytes.map UInt8.toNat) (normalizedBytes.map UInt8.toNat)
    certificate input hcheck

end S31.Functional.Correspondence.AcceptedPublicFixedCells
