import S31.Gadgets.Functional.Correspondence.SyntheticSourceTraceCompletion
import S31.Gadgets.Functional.Correspondence.SourcePhysicalAddressBounds

/-!
Unconditional source-slice physical satisfiability for exact direct source
and normalized bytes. The checked source determines canonical source-cell
addresses and multiplicities, so the synthetic 512-row arithmetic trace
matches every projected source fixed cell without a caller-supplied bound.

The rest of the fixed/main roster is synthetic zero-add padding; this is not
the native honest base trace or a Gate-balanced trace.
-/

namespace S31.Functional.Correspondence.AcceptedSourcePhysicalTrace

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
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.SourcePhysicalAddressBounds
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion

/-- Exact accepted source bytes and any input construct a 512-row decoded
trace. Every installed local arithmetic root vanishes; *every* projected
source fixed cell matches its row, selectors, addresses, and multiplicity;
and the selected source wire has the parsed value. No physical trace, row
equation, canonical address bound, or coherent wire map is assumed. -/
theorem checked_direct_source_trace_exists
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      SSATextBytes.denotation sourceBytes input = some output ∧
      allArithmeticRootsZero
        (trace (expectedCells certificate (compiledAddRows certificate)) wire) ∧
      (∀ cell ∈ expectedCells certificate (compiledAddRows certificate),
        fixedMatches
          (trace (expectedCells certificate (compiledAddRows certificate)) wire)
          cell) ∧
      wire (address certificate.output) = packM31 output := by
  obtain ⟨wire, output, hdenotation, hair, hselected⟩ :=
    accepted_direct_arithmetic_trace_exists sourceBytes normalizedBytes
      certificate input hcheck
  have hcanonical := checked_direct_source_cells_canonical sourceBytes
    normalizedBytes certificate hcheck
  exact ⟨wire, output, hdenotation, hair,
    selected_source_fixed_of_canonical_bounds sourceBytes normalizedBytes
      certificate wire hcheck hcanonical, hselected⟩

end S31.Functional.Correspondence.AcceptedSourcePhysicalTrace
