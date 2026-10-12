import S31.Gadgets.Functional.Correspondence.AcceptedPublicPhysicalTrace
import S31.Gadgets.Functional.Correspondence.AliasCanonicalIrBytes

/-!
Constructive projected arithmetic witness for every source accepted by the
bounded three-file alias checker. A lexical alias or redundant parenthesis
adds no producer. The output can select an earlier producer even when later
eager arithmetic instructions have zero Gate output multiplicity.

This covers the modeled source/input/output projected cells. The remaining
native constant and padding rows, full native fixed-column roster, exact
Gate balance, committed trace authentication and PCS/FRI are separate joins.
-/

namespace S31.Functional.Correspondence.AcceptedAliasPublicPhysicalTrace

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSADirectGateBridge
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.HonestPublicBoundaryWire
open S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.SourceDeterminedDirectRows

/-- Exact source, normalized relation, and canonical IR bytes determine a
producer-only positional certificate. For every input, its actual alias-byte
denotation has one coherent modeled assignment across all source arithmetic
and public input/output cells. The selected result may be an earlier producer;
the later eager instructions remain present and locally constrained. -/
theorem checked_alias_public_boundary_exists
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      SSAAliasTextBytes.denotation sourceBytes input = some output ∧
      nativePolynomialRows certificate wire ∧
      InputBoundary certificate (compiledAddRows certificate) wire input ∧
      OutputBoundary certificate (compiledAddRows certificate) wire output ∧
      wire (address certificate.output) = packM31 output ∧
      wire 1 = unit ⟨0, by decide⟩ := by
  obtain ⟨parsed, hparse, _, _, _, _, hsemantics⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate input hcheck
  let output := parsed.meaning.eval input
  have hdenotation : SSAAliasTextBytes.denotation sourceBytes input =
      some output := by
    simp [SSAAliasTextBytes.denotation, hparse, output]
  have hexecute : executeNormalized certificate input = some output :=
    hsemantics.trans hdenotation
  obtain ⟨wire, hsource, hinput, houtput, hselected, hunit⟩ :=
    executed_public_boundary_exists certificate input output hexecute
  exact ⟨wire, output, hdenotation, hsource, hinput, houtput, hselected,
    hunit⟩

/-- The alias certificate has a concrete decoded 512-row trace on which all
installed local arithmetic roots vanish. Every source and public boundary
projected cell is evaluated under the *same* wire assignment. Nonprojected
rows use synthetic zero-add padding, so this is a model satisfiability result
rather than a native full-witness or proof-verifier theorem. -/
theorem checked_alias_projected_trace_exists
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      SSAAliasTextBytes.denotation sourceBytes input = some output ∧
      allArithmeticRootsZero (trace (projectedCells certificate) wire) ∧
      wire (address certificate.output) = packM31 output := by
  obtain ⟨wire, output, hdenotation, hsource, hinput, houtput,
    hselected, hunit⟩ := checked_alias_public_boundary_exists sourceBytes
      normalizedBytes canonicalBytes certificate input hcheck
  exact ⟨wire, output, hdenotation,
    arithmetic_complete (projectedCells certificate) wire
      (projected_cells_accept certificate wire input output hsource
        hinput houtput hunit), hselected⟩

/-- The same constructive statement for literal file-byte arrays. -/
theorem checked_u8_alias_projected_trace_exists
    (sourceBytes normalizedBytes canonicalBytes : List UInt8)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkAliasCanonical (sourceBytes.map UInt8.toNat)
      (normalizedBytes.map UInt8.toNat) (canonicalBytes.map UInt8.toNat) =
      some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      SSAAliasTextBytes.denotation (sourceBytes.map UInt8.toNat) input =
        some output ∧
      allArithmeticRootsZero (trace (projectedCells certificate) wire) ∧
      wire (address certificate.output) = packM31 output :=
  checked_alias_projected_trace_exists
    (sourceBytes.map UInt8.toNat) (normalizedBytes.map UInt8.toNat)
    (canonicalBytes.map UInt8.toNat) certificate input hcheck

end S31.Functional.Correspondence.AcceptedAliasPublicPhysicalTrace
