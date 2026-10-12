import S31.Gadgets.Functional.Correspondence.OptimizedTextBytes
import S31.Gadgets.Functional.Correspondence.SourceDeterminedDirectRows
import S31.Gadgets.Functional.SSANativePolynomialRows
import S31.Gadgets.Functional.SSAInstalledBytecodePublicOutput
import S31.Gadgets.Functional.TextSquare4Air

/-!
The optimized source-byte fragment admits reversed add/mul operands and
repeated expressions. `checkBytes` binds the source spelling, normalized JSON,
and compact canonical IR. This module carries that *same compact certificate*
to the direct-Gate projected arithmetic cells and selected public result.

The assumptions deliberately distinguish three different checks: exact bytes,
observed fixed-cell equality, and locally accepted arithmetic on one coherent
wire map. The input boundary is the existing public packing relation. No
premise here asserts that a STARK verifier authenticates those observed cells
or wire values, nor that native Zig implements the modeled optimizer for every
accepted source.
-/

namespace S31.Functional.Correspondence.OptimizedSourceAirRows

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSACertificate
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.CanonicalDagOptimization
open S31.Functional.Correspondence.OptimizedTextBytes
open S31.Functional.Correspondence.SourceDeterminedDirectRows

/-- Every projected source operation of the compact DAG is locally accepted
at the modeled direct-Gate addresses. A repeated source expression adds no
second operation cell: `expectedCells` is built from `compact.instructions`.
The equality with `observedCells` must be checked against an actual export. -/
theorem optimized_source_projected_air_sound
    (sourceBytes normalizedBytes canonicalBytes : SSATextBytes.Token)
    (compact : Certificate) (observedCells : List ColumnCell)
    (wire : Nat → Quad) (input : Lanes)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact)
    (hcells : observedCells = expectedCells compact (compiledAddRows compact))
    (hboundary : InputBoundary compact (compiledAddRows compact) wire input)
    (hlocal : ∀ cell ∈ observedCells, cellAccepts cell wire) :
    observedCells = expectedCells compact (compiledAddRows compact) ∧
      ∃ output : Lanes,
        denotation sourceBytes input = some output ∧
        wire (address compact.output) = packM31 output := by
  obtain ⟨parsed, hparse, _, _, _, hexecute⟩ :=
    checked_bytes_sound sourceBytes normalizedBytes canonicalBytes
      compact input hbytes
  let output : Lanes := parsed.meaning.eval input
  have hdenotation : denotation sourceBytes input = some output := by
    simp [denotation, hparse, output]
  have hrun : executeNormalized compact input = some output := by
    rw [hexecute]
    exact hdenotation
  have hplan := source_plan_expected compact (compiledAddRows compact)
  have hsource : sourceCellsEvaluated compact observedCells wire := by
    intro instruction hmember
    obtain ⟨cell, hcell, hflag0, hflag1, hflag2, hflag3,
      hin0, hin1, hout, _⟩ := hplan instruction hmember
    have hobserved : cell ∈ observedCells := by
      rw [hcells]
      exact hcell
    exact ⟨cell, hobserved, hflag0, hflag1, hflag2, hflag3,
      hin0, hin1, hout, hlocal cell hobserved⟩
  have hinput : wire (address 0) = packM31 input := by
    simpa [address] using packed_input_bound compact
      (compiledAddRows compact) wire input hboundary
  exact ⟨hcells, output, hdenotation,
    selected_wire_matches_execution compact wire input output hinput
      (source_cells_imply_polynomial_rows compact observedCells wire hsource)
      hrun⟩

/-- If the same selected circuit wire is pinned to a claimed public output,
the claim equals the meaning of the original optimized source spelling.
This is arbitrary-wire local soundness, conditional on the declared row and
input premises; it does not infer them from proof verification. -/
theorem optimized_source_claim_sound
    (sourceBytes normalizedBytes canonicalBytes : SSATextBytes.Token)
    (compact : Certificate) (observedCells : List ColumnCell)
    (wire : Nat → Quad) (input claimed : Lanes)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact)
    (hcells : observedCells = expectedCells compact (compiledAddRows compact))
    (hboundary : InputBoundary compact (compiledAddRows compact) wire input)
    (hlocal : ∀ cell ∈ observedCells, cellAccepts cell wire)
    (hclaim : wire (address compact.output) = packM31 claimed) :
    denotation sourceBytes input = some claimed := by
  obtain ⟨_, output, hdenotation, hselected⟩ :=
    optimized_source_projected_air_sound sourceBytes normalizedBytes
      canonicalBytes compact observedCells wire input
      hbytes hcells hboundary hlocal
  have hsame : output = claimed :=
    S31.Functional.TextSquare4Air.packM31_injective
      (hselected.symm.trans hclaim)
  simpa [hsame] using hdenotation

/-- The existing eleven output-path mask, inverse and copy rows derive the
selected-wire claim from four scalar public pins. With the source, compact
operation cells and input boundary above, a modeled direct-Gate public output
therefore has exactly the original optimized source meaning. -/
theorem optimized_source_public_output_sound
    (sourceBytes normalizedBytes canonicalBytes : SSATextBytes.Token)
    (compact : Certificate) (observedCells : List ColumnCell)
    (wire : Nat → Quad) (input claimed : Lanes)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact)
    (hcells : observedCells = expectedCells compact (compiledAddRows compact))
    (hinput : InputBoundary compact (compiledAddRows compact) wire input)
    (hlocal : ∀ cell ∈ observedCells, cellAccepts cell wire)
    (houtput : OutputBoundary compact (compiledAddRows compact) wire claimed) :
    denotation sourceBytes input = some claimed := by
  exact optimized_source_claim_sound sourceBytes normalizedBytes canonicalBytes
    compact observedCells wire input claimed hbytes hcells hinput hlocal
    (output_boundary_claim compact (compiledAddRows compact) wire claimed houtput)

set_option maxRecDepth 8192 in
/-- The handwritten reversed/CSE example retains three compact arithmetic
producers, in source order. The direct physical trace groups add rows before
pointwise multiplication, so the multiplication is at row 503 while the last
source add is at row 4. The source's fourth arithmetic `let` reuses wire 3
and contributes no fourth AIR operation row. -/
theorem reversed_and_repeated_compact_air_rows :
    (expectedCells compactExample (compiledAddRows compactExample)).map
      ColumnCell.traceRow = [3, 503, 4] ∧
    (expectedCells compactExample (compiledAddRows compactExample)).map
      ColumnCell.out = [23, 24, 25] ∧
    (expectedCells compactExample (compiledAddRows compactExample)).map
      (fun cell => (cell.addFlag, cell.pointwiseMulFlag)) =
        [(1, 0), (0, 1), (1, 0)] := by decide

end S31.Functional.Correspondence.OptimizedSourceAirRows
