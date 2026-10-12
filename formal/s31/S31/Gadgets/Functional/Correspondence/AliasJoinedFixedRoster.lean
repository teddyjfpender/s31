import S31.Gadgets.Functional.Correspondence.AcceptedAliasPublicPhysicalTrace
import S31.Gadgets.Functional.Correspondence.CheckedFullLocalArithmeticComposition

/-!
The exact three-file alias byte check suffices to determine a complete
512-row *modeled fixed roster*, without a second producer-only source spelling.
The constant-island check remains an explicit premise. This proves fixed
selectors, addresses, and multiplicities on a constructed decoded trace; it
does not identify those rows with native committed columns or authenticate
STARK openings.
-/

namespace S31.Functional.Correspondence.AliasJoinedFixedRoster

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAProjectedRowCompleteness
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.AliasCanonicalIrBytes
open S31.Functional.Correspondence.AliasRawGateSoundness
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.AcceptedAliasPublicPhysicalTrace
open S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness

/-- Three-file alias admission and a checked island yield a distinct,
in-range, complete 512-row fixed-cell roster. No direct spelling is assumed.
-/
theorem checked_alias_joined_roster_complete
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (island : List ColumnCell)
    (values : List Quad)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    (joinedCells certificate island).length = 512 ∧
    ((joinedCells certificate island).map ColumnCell.traceRow).Nodup ∧
    (∀ cell ∈ joinedCells certificate island, cell.traceRow < 512) ∧
    (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
      cell.traceRow = row.val) := by
  obtain ⟨_, _, _, _, _, hrelation, _⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate (fun _ => 0) halias
  have hbudget := checked_alias_relation_instruction_bound sourceBytes
    normalizedBytes certificate hrelation
  have hislandRows := checked_rows_count certificate island values
    hbudget hisland
  have hprojected := checked_alias_projected_rows sourceBytes
    normalizedBytes canonicalBytes certificate halias
  have hprojectedLength : (projectedCells certificate).length =
      certificate.instructions.length + 25 := by
    simp [projectedCells, expectedInputCells, expectedOutputCells,
      expectedMaskCells, expected_cells_length]
  have hlength : (joinedCells certificate island).length = 512 := by
    simp only [joinedCells, List.length_append]
    omega
  have hnodup : ((joinedCells certificate island).map
      ColumnCell.traceRow).Nodup := by
    have hislandNodup : (island.map ColumnCell.traceRow).Nodup := by
      rw [hislandRows.1]
      exact constant_positions_nodup certificate hbudget
    have hdisjoint : List.Disjoint
        ((projectedCells certificate).map ColumnCell.traceRow)
        (island.map ColumnCell.traceRow) := by
      rw [hislandRows.1]
      exact projected_constant_rows_disjoint_of_budget certificate hbudget
    simpa [joinedCells, List.map_append] using
      hprojected.1.append hislandNodup hdisjoint
  have hbound : ∀ cell ∈ joinedCells certificate island,
      cell.traceRow < 512 := by
    intro cell hcell
    rcases List.mem_append.mp hcell with hprojectedCell | hislandCell
    · exact hprojected.2 cell hprojectedCell
    · have hrow : cell.traceRow ∈ constantPositions certificate := by
        rw [← hislandRows.1]
        exact List.mem_map_of_mem hislandCell
      have hband := constant_position_band certificate hbudget
        cell.traceRow hrow
      have hA : compiledAddRows certificate ≤ 476 := by
        unfold compiledAddRows
        omega
      rcases hband with h | h | h <;> omega
  let rows := (joinedCells certificate island).map ColumnCell.traceRow
  have hsubset : rows.toFinset ⊆ Finset.range 512 := by
    intro row hrow
    have hmem : row ∈ rows := List.mem_toFinset.mp hrow
    obtain ⟨cell, hcell, heq⟩ := List.mem_map.mp hmem
    exact Finset.mem_range.mpr (by simpa [rows] using
      (heq ▸ hbound cell hcell))
  have hcard : rows.toFinset.card = (Finset.range 512).card := by
    rw [List.toFinset_card_of_nodup (by simpa [rows] using hnodup)]
    simp [rows, hlength]
  have heq : rows.toFinset = Finset.range 512 :=
    Finset.eq_of_subset_of_card_le hsubset hcard.symm.le
  refine ⟨hlength, hnodup, hbound, ?_⟩
  intro row
  have hmem : row.val ∈ rows := List.mem_toFinset.mp
    (heq.symm ▸ Finset.mem_range.mpr row.isLt)
  obtain ⟨cell, hcell, hrow⟩ := List.mem_map.mp hmem
  exact ⟨cell, hcell, hrow⟩

/-- Every fixed tuple in the complete modeled roster matches the same
constructed decoded trace, for every wire assignment. The alias source bytes
alone determine the projected tuples; the island checker determines the rest.
-/
theorem checked_alias_joined_fixed_matches
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (island : List ColumnCell)
    (values : List Quad) (wire : Nat → Quad)
    (halias : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    ∀ cell ∈ joinedCells certificate island,
      fixedMatches (trace (joinedCells certificate island) wire) cell := by
  have hroster := checked_alias_joined_roster_complete sourceBytes
    normalizedBytes canonicalBytes certificate island values halias hisland
  have hcanonical : ∀ cell ∈ joinedCells certificate island,
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647 := by
    intro cell hcell
    rcases List.mem_append.mp hcell with hprojected | hislandCell
    · exact checked_alias_projected_canonical sourceBytes normalizedBytes
        canonicalBytes certificate halias cell hprojected
    · have hsound := checked_cells_sound certificate island values
        hisland cell hislandCell
      rcases hsound with ⟨_, _, _, _, _, _, _, h0, h1, ho, hm, _⟩
      exact ⟨h0, h1, ho, hm⟩
  intro cell hcell
  obtain ⟨i, hi, hflags, hin0, hin1, hout, hmult⟩ :=
    zeroTrace_fixed (joinedCells certificate island) hroster.2.1
      hroster.2.2.1 hcanonical [] cell hcell
  refine ⟨i, hi, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [trace, row] using hflags
  · simpa [trace, row] using hin0
  · simpa [trace, row] using hin1
  · simpa [trace, row] using hout
  · simpa [trace, row] using hmult

end S31.Functional.Correspondence.AliasJoinedFixedRoster
