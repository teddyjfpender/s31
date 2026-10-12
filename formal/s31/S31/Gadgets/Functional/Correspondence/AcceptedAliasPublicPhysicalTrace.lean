import S31.Gadgets.Functional.Correspondence.AcceptedPublicPhysicalTrace
import S31.Gadgets.Functional.Correspondence.AcceptedPublicFixedCells
import S31.Gadgets.Functional.Correspondence.AliasCanonicalIrBytes

/-!
Constructive projected arithmetic witness for every source accepted by the
bounded three-file alias checker. A lexical alias or redundant parenthesis
adds no producer. The output can select an earlier producer even when later
eager arithmetic instructions have zero Gate output multiplicity.

This covers the modeled source/input/output projected cells, their distinct
in-range physical rows, and their fixed tuples. The remaining native
constant and padding rows, full native fixed-column roster, exact
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
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSADirectGateBridge
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.AliasRawGateSoundness
open S31.Functional.Correspondence.HonestPublicBoundaryWire
open S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.SourcePhysicalAddressBounds
open S31.Functional.Correspondence.AcceptedPublicFixedCells
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness

/-- Three-file alias admission gives an actual eager SSA execution for every
public input. This keeps the selected output and every trailing producer in
the same executed certificate. -/
theorem checked_alias_executes
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ∃ output : Lanes, executeNormalized certificate input = some output := by
  obtain ⟨parsed, hparse, _, _, _, _, hsemantics⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate input hcheck
  refine ⟨parsed.meaning.eval input, ?_⟩
  rw [hsemantics]
  simp [SSAAliasTextBytes.denotation, hparse]

/-- Alias erasure preserves the same source and public row placement: every
modeled projected cell is in the decoded trace's physical range and no two
projected cells claim the same row. The exact 512-row partition is determined
by the accepted producer count. -/
theorem checked_alias_projected_rows
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ((projectedCells certificate).map ColumnCell.traceRow).Nodup ∧
    (∀ cell ∈ projectedCells certificate, cell.traceRow < 512) := by
  obtain ⟨_, _, _, _, _, hrelation, _⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate (fun _ => 0) hcheck
  have hbudget := checked_alias_relation_instruction_bound sourceBytes
    normalizedBytes certificate hrelation
  have hpartition := canonical_alias_bytes_partition sourceBytes
    normalizedBytes canonicalBytes certificate hcheck
  have hnodup :=
    (canonical_alias_projected_rows_distinct sourceBytes normalizedBytes
      canonicalBytes certificate hcheck).2.2
  refine ⟨by simpa [projectedCells] using hnodup, ?_⟩
  intro cell hcell
  rcases List.mem_append.mp hcell with hsource | hpublic
  · have hrow : cell.traceRow ∈
        (expectedRows certificate (compiledAddRows certificate)).map
          NativeSourceRow.traceRow := by
      rw [← expected_cells_trace_rows_eq]
      exact List.mem_map_of_mem hsource
    obtain ⟨row, hrow, heq⟩ := List.mem_map.mp hrow
    have hbounded := source_rows_within_512_of_budget certificate
      (compiledAddRows certificate) hbudget hpartition row hrow
    norm_num at hbounded
    simpa [heq] using hbounded
  · have hbounded := public_cells_within_512_of_budget certificate
      (compiledAddRows certificate) hbudget hpartition cell hpublic
    norm_num at hbounded
    exact hbounded

/-- All modeled projected fixed selector, address, and multiplicity words
are canonical field words under the checked producer budget and execution. -/
theorem checked_alias_projected_canonical
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ∀ cell ∈ projectedCells certificate,
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647 := by
  obtain ⟨_, _, _, _, _, hrelation, _⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate (fun _ => 0) hcheck
  have hbudget := checked_alias_relation_instruction_bound sourceBytes
    normalizedBytes certificate hrelation
  let input : Lanes := fun _ => 0
  obtain ⟨output, hexecute⟩ := checked_alias_executes sourceBytes
    normalizedBytes canonicalBytes certificate input hcheck
  have houtput := selected_output_id_bound_of_execution certificate
    input output hexecute
  have hsource : ∀ cell ∈ expectedCells certificate
      (compiledAddRows certificate),
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647 := by
    rw [execute_normalized_eq_execute] at hexecute
    unfold execute at hexecute
    cases hrun : certificate.instructions.foldlM executeStep [input] with
    | none => simp [hrun] at hexecute
    | some final =>
        have htrace := S31.Functional.SSAAirRows.executing_trace_has_air_rows
          certificate.instructions [input] final hrun
        exact expected_source_cells_canonical certificate input hbudget
          htrace
  intro cell hcell
  rcases List.mem_append.mp hcell with hsourceCell | hpublicCell
  · exact hsource cell hsourceCell
  · exact public_cells_canonical_of_bounds certificate hbudget houtput
      cell hpublicCell

/-- Every admitted alias's projected cell appears at its distinct physical
row with the exact modeled fixed tuple in the same synthetic 512-row trace.
This makes no claim about the source-independent native fixed roster. -/
theorem checked_alias_projected_fixed_matches
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (wire : Nat → Quad)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ∀ cell ∈ projectedCells certificate,
      fixedMatches (trace (projectedCells certificate) wire) cell := by
  obtain ⟨hnodup, hbound⟩ := checked_alias_projected_rows sourceBytes
    normalizedBytes canonicalBytes certificate hcheck
  have hcanonical := checked_alias_projected_canonical sourceBytes
    normalizedBytes canonicalBytes certificate hcheck
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

/-- Strong projected-row join for arbitrary exact three-file admitted alias
programs and public inputs. Every projected cell occupies a unique in-range
physical row and its complete modeled fixed tuple matches the constructed
decoded trace. Nonprojected rows remain synthetic; this is not a native
full-roster or proof-authentication statement. -/
theorem checked_alias_projected_physical_trace_exists
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      SSAAliasTextBytes.denotation sourceBytes input = some output ∧
      allArithmeticRootsZero (trace (projectedCells certificate) wire) ∧
      ((projectedCells certificate).map ColumnCell.traceRow).Nodup ∧
      (∀ cell ∈ projectedCells certificate, cell.traceRow < 512) ∧
      (∀ cell ∈ projectedCells certificate,
        fixedMatches (trace (projectedCells certificate) wire) cell) ∧
      wire (address certificate.output) = packM31 output := by
  obtain ⟨wire, output, hdenotation, harithmetic, hselected⟩ :=
    checked_alias_projected_trace_exists sourceBytes normalizedBytes
      canonicalBytes certificate input hcheck
  obtain ⟨hnodup, hbound⟩ := checked_alias_projected_rows sourceBytes
    normalizedBytes canonicalBytes certificate hcheck
  exact ⟨wire, output, hdenotation, harithmetic, hnodup, hbound,
    checked_alias_projected_fixed_matches sourceBytes normalizedBytes
      canonicalBytes certificate wire hcheck, hselected⟩

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

/-- Literal file-byte entry point for the complete projected-row join. -/
theorem checked_u8_alias_projected_physical_trace_exists
    (sourceBytes normalizedBytes canonicalBytes : List UInt8)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkAliasCanonical (sourceBytes.map UInt8.toNat)
      (normalizedBytes.map UInt8.toNat) (canonicalBytes.map UInt8.toNat) =
      some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      SSAAliasTextBytes.denotation (sourceBytes.map UInt8.toNat) input =
        some output ∧
      allArithmeticRootsZero (trace (projectedCells certificate) wire) ∧
      ((projectedCells certificate).map ColumnCell.traceRow).Nodup ∧
      (∀ cell ∈ projectedCells certificate, cell.traceRow < 512) ∧
      (∀ cell ∈ projectedCells certificate,
        fixedMatches (trace (projectedCells certificate) wire) cell) ∧
      wire (address certificate.output) = packM31 output :=
  checked_alias_projected_physical_trace_exists
    (sourceBytes.map UInt8.toNat) (normalizedBytes.map UInt8.toNat)
    (canonicalBytes.map UInt8.toNat) certificate input hcheck

end S31.Functional.Correspondence.AcceptedAliasPublicPhysicalTrace
