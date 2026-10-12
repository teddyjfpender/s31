import S31.Gadgets.Functional.Correspondence.HonestPublicBoundaryWire
import S31.Gadgets.Functional.Correspondence.SyntheticSourceTraceCompletion

/-!
An honest arithmetic completion for every projected direct-Gate source and
public-boundary cell. All other rows are still synthetic zero-add padding;
this is not a native full-roster or Gate-balanced trace.
-/

namespace S31.Functional.Correspondence.AcceptedPublicPhysicalTrace

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.HonestPublicBoundaryWire

def projectedCells (certificate : Certificate) :
    List S31.Functional.SSAAirColumnCells.ColumnCell :=
  expectedCells certificate (compiledAddRows certificate) ++
    (expectedInputCells certificate (compiledAddRows certificate) ++
      expectedOutputCells certificate (compiledAddRows certificate))

/-- All four input self rows, in addition to the copies and pack rows of
`InputBoundary`, satisfy their selected pointwise identity polynomial. -/
theorem input_cells_accept (certificate : Certificate) (totalAddRows : Nat)
    (wire : Nat → Quad) (input : Lanes)
    (hinput : InputBoundary certificate totalAddRows wire input)
    (hunit : wire 1 = unit ⟨0, by decide⟩) :
    ∀ cell ∈ expectedInputCells certificate totalAddRows,
      cellAccepts cell wire := by
  intro cell hcell
  simp only [expectedInputCells, List.mem_append] at hcell
  rcases hcell with (((hadd | hmul) | hcopy) | hself)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hadd
    have hindex : i < 3 := List.mem_range.mp hi
    simpa [cellAccepts, cellFlags, expectedPackAddCell] using
      hinput.packAdds ⟨i, hindex⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmul
    have hindex : i < 3 := List.mem_range.mp hi
    simpa [cellAccepts, cellFlags, expectedPackMulCell] using
      hinput.packMuls ⟨i, hindex⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hcopy
    have hindex : i < 4 := List.mem_range.mp hi
    simpa [cellAccepts, cellFlags, expectedInputCopyCell] using
      hinput.copies ⟨i, hindex⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hself
    have hindex : i < 4 := List.mem_range.mp hi
    have hraw := input_copy_scalar_bound certificate totalAddRows wire input
      hinput ⟨i, hindex⟩
    change accepts (encode .pointwiseMul) (wire (11 + i)) (wire 1)
      (wire (11 + i))
    rw [hraw, hunit]
    apply (accepts_encoded .pointwiseMul _ _ _).mpr
    simp [evaluate, S31.Gadgets.Packed.pointwise, base, unit]

theorem output_cells_accept (certificate : Certificate) (totalAddRows : Nat)
    (wire : Nat → Quad) (output : Lanes)
    (houtput : OutputBoundary certificate totalAddRows wire output) :
    ∀ cell ∈ expectedOutputCells certificate totalAddRows,
      cellAccepts cell wire := by
  intro cell hcell
  simp only [expectedOutputCells, List.mem_append] at hcell
  rcases hcell with (hmask | hinverse) | hcopy
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmask
    have hindex : i < 4 := List.mem_range.mp hi
    exact houtput.masks ⟨i, hindex⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hinverse
    have hindex : i < 3 := List.mem_range.mp hi
    exact houtput.inverses ⟨i, hindex⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hcopy
    have hindex : i < 4 := List.mem_range.mp hi
    exact houtput.copies ⟨i, hindex⟩

theorem projected_cells_accept (certificate : Certificate)
    (wire : Nat → Quad) (input output : Lanes)
    (hsource : nativePolynomialRows certificate wire)
    (hinput : InputBoundary certificate (compiledAddRows certificate)
      wire input)
    (houtput : OutputBoundary certificate (compiledAddRows certificate)
      wire output)
    (hunit : wire 1 = unit ⟨0, by decide⟩) :
    ∀ cell ∈ projectedCells certificate, cellAccepts cell wire := by
  intro cell hcell
  rcases List.mem_append.mp hcell with hsourceCell | hpublicCell
  · exact expected_source_cells_accept certificate
      (compiledAddRows certificate) wire hsource cell hsourceCell
  · rcases List.mem_append.mp hpublicCell with hinputCell | houtputCell
    · exact input_cells_accept certificate (compiledAddRows certificate)
        wire input hinput hunit cell hinputCell
    · exact output_cells_accept certificate (compiledAddRows certificate)
        wire output houtput cell houtputCell

/-- For arbitrary admitted source bytes and input, all 41-or-fewer
source/input/output projected cells fit in a concrete 512-row decoded trace
whose installed local arithmetic roots vanish. Nonprojected rows use
synthetic zero-add padding; fixed native constant rows and Gate balance are
not claimed. -/
theorem checked_direct_projected_trace_exists
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      denotation sourceBytes input = some output ∧
      allArithmeticRootsZero (trace (projectedCells certificate) wire) ∧
      wire (address certificate.output) = packM31 output := by
  obtain ⟨wire, output, hdenotation, hsource, hinput, houtput,
    hselected, hunit⟩ := checked_direct_public_boundary_exists
      sourceBytes normalizedBytes certificate input hcheck
  exact ⟨wire, output, hdenotation,
    arithmetic_complete (projectedCells certificate) wire
      (projected_cells_accept certificate wire input output hsource
        hinput houtput hunit), hselected⟩

/-- A literal-byte API for the same theorem. The parser and checker see the
actual byte values, so no out-of-range `Nat` token can enter this statement.
-/
theorem checked_u8_direct_projected_trace_exists
    (sourceBytes normalizedBytes : List UInt8) (certificate : Certificate)
    (input : Lanes)
    (hcheck : checkRelation (sourceBytes.map UInt8.toNat)
      (normalizedBytes.map UInt8.toNat) = some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      denotation (sourceBytes.map UInt8.toNat) input = some output ∧
      allArithmeticRootsZero (trace (projectedCells certificate) wire) ∧
      wire (address certificate.output) = packM31 output :=
  checked_direct_projected_trace_exists
    (sourceBytes.map UInt8.toNat) (normalizedBytes.map UInt8.toNat)
    certificate input hcheck

end S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
