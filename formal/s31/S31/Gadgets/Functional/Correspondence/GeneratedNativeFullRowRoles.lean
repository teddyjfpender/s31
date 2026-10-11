import S31.Gadgets.Functional.Correspondence.FullDirectGateRowRoles
import S31.Gadgets.Functional.Correspondence.GeneratedNativeSourceCells

/-!
Four pinned native `inspect-topology` source-cell exports are checked against
the complete modeled 512-row operation-role partition. The fixture generator
independently checked all eight full native fixed columns and recorded their
digests; this Lean module checks the exported source cells and row roles.

The fixtures are samples at one, eight, fifteen, and sixteen source gates.
They are not a proof that arbitrary future native emissions or PCS openings
equal the modeled fixed columns.
-/

namespace S31.Functional.Correspondence.GeneratedNativeFullRowRoles

open S31.Functional.SSACertificate
open S31.Functional.SSAAirColumnCells
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.FullDirectGateRowRoles
open S31.Functional.Correspondence.GeneratedNativeSourceCells
open S31.Functional.Correspondence.GeneratedMutationRows

/-- Executable independent role check for one exported source cell. It checks
the complete one-hot selector and its exact 512-row grouped position. -/
def sourceCellRoleMatches (certificate : Certificate) (cell : ColumnCell) : Bool :=
  if h : cell.traceRow < 512 then
    let role := rowRole certificate ⟨cell.traceRow, h⟩
    (cell.addFlag == 1 && cell.subFlag == 0 && cell.mulFlag == 0 &&
      cell.pointwiseMulFlag == 0 && role == .sourceAdd) ||
    (cell.addFlag == 0 && cell.subFlag == 0 && cell.mulFlag == 0 &&
      cell.pointwiseMulFlag == 1 && role == .sourcePointwiseMul)
  else false

/-- Native source cells equal the source-byte-derived model, occupy matching
full-roster operation roles, and leave the expected number of constant /
padding additions. The byte-to-cell equality itself comes from the prior
generated native fixture theorem. -/
def NativeRoleParity (certificate : Certificate) (cells : List ColumnCell) : Prop :=
  cells = expectedCells certificate (compiledAddRows certificate) ∧
  cells.length = certificate.instructions.length ∧
  cells.all (sourceCellRoleMatches certificate) = true ∧
  compiledAddRows certificate - (11 +
    S31.Functional.SSAOutputAirCells.sourceAddCount certificate) =
      465 - certificate.instructions.length

theorem case00_native_roles :
    NativeRoleParity case00Certificate case00NativeCells := by
  refine ⟨case00_source_to_native_cells.2, ?_, ?_, ?_⟩ <;> decide

theorem case07_native_roles :
    NativeRoleParity case07Certificate case07NativeCells := by
  refine ⟨case07_source_to_native_cells.2, ?_, ?_, ?_⟩ <;> decide

theorem case14_native_roles :
    NativeRoleParity case14Certificate case14NativeCells := by
  refine ⟨case14_source_to_native_cells.2, ?_, ?_, ?_⟩ <;> decide

theorem case16_native_roles :
    NativeRoleParity case16Certificate case16NativeCells := by
  refine ⟨case16_source_to_native_cells.2, ?_, ?_, ?_⟩ <;> decide

end S31.Functional.Correspondence.GeneratedNativeFullRowRoles
