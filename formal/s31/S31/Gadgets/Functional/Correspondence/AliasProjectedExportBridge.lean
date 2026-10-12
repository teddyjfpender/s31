import S31.Gadgets.Functional.Correspondence.ZeroPhysicalTraceWitness
import S31.Gadgets.Functional.GeneratedDirectGateBridge

/-!
The alias square and the pinned native `functional_square4` export have the
same positional SSA certificate and the same 27 projected direct-Gate cells.
Their source programs have different names, so this is a certificate-level
projection equality, not a claim that the native compiler was run on the
alias source bytes. Full fixed columns, witness main columns, external
component events and commitment authentication remain separate obligations.
-/

namespace S31.Functional.Correspondence.AliasProjectedExportBridge

open S31.Functional.Correspondence.ZeroPhysicalTraceWitness

private theorem certificates_match :
    squareCertificate =
      S31.Functional.GeneratedDirectGateBridge.certificate := by decide

private theorem add_row_counts_match :
    (474 : Nat) =
      S31.Functional.GeneratedDirectGateBridge.observedAddRows := by decide

/-- The exact source-derived selector, address, multiplicity and row-index
roster of the alias sample equals the three projected cell lists extracted
from the pinned native square4 package. The equality is over `ColumnCell`
values, not a digest or a source-name comparison. -/
theorem alias_square_projected_cells_equal_export :
    squareCells =
      S31.Functional.GeneratedDirectGateBridge.observedColumnCells ++
      S31.Functional.GeneratedDirectGateBridge.observedInputCells ++
      S31.Functional.GeneratedDirectGateBridge.observedOutputCells := by
  rw [squareCells, roster, certificates_match, add_row_counts_match,
    ← S31.Functional.GeneratedDirectGateBridge.observed_source_columns_match,
    ← S31.Functional.GeneratedDirectGateBridge.observed_input_cells_match,
    ← S31.Functional.GeneratedDirectGateBridge.observed_output_cells_match]

/-- Alias text admission and the observed fixed-cell projection agree on a
single positional certificate, while preserving the distinct source bytes. -/
theorem alias_admitted_export_projection :
    S31.Functional.SSAAliasTextBytes.checkAliasRelation
      S31.Functional.SSAAliasTextBytes.aliasSquareSource squareNormalized =
        some S31.Functional.GeneratedDirectGateBridge.certificate ∧
    squareCells =
      S31.Functional.GeneratedDirectGateBridge.observedColumnCells ++
      S31.Functional.GeneratedDirectGateBridge.observedInputCells ++
      S31.Functional.GeneratedDirectGateBridge.observedOutputCells := by
  constructor
  · simpa only [certificates_match] using alias_square_relation
  · exact alias_square_projected_cells_equal_export

end S31.Functional.Correspondence.AliasProjectedExportBridge
