import S31.Gadgets.Functional.Correspondence.GeneratedOrderedSubtractionNativeRows

/-!
A conditional source-to-native-row theorem for `release_sub4/manual.s31`.
The three selected fixed cells are the real native export, independently
matched against the parsed source DAG. A single address-to-value map supplies
all row operands and results, so a read at an address cannot silently take a
different value in a later row. The theorem assumes this ideal coherent map
and local packed AIR acceptance; Gate lookup and PCS authentication of actual
proof openings remain to be established.
-/

namespace S31.Functional.Correspondence.OrderedSubtractionNativeSoundness

open S31.Functional.SSAAirColumnCells
open OrderedSubtractionBytes
open GeneratedOrderedSubtractionRelease
open GeneratedOrderedSubtractionNativeRows

/-- Interpret the selected one-hot native opcode using the installed packed
arithmetic relation. The exact fixed-cell theorem below supplies the selector
and addresses; malformed selector combinations are not admitted by that
theorem. -/
def packedAt (wire : Nat → Lanes) (tailA tailB : Tail)
    (cell : ColumnCell) : Prop :=
  if cell.addFlag = 1 then
    SourceFunctionBytes.Op.packed .add
      (wire cell.in0) (wire cell.in1) (wire cell.out) tailA tailB
  else if cell.subFlag = 1 then
    SourceFunctionBytes.Op.packed .sub
      (wire cell.in0) (wire cell.in1) (wire cell.out) tailA tailB
  else if cell.pointwiseMulFlag = 1 then
    SourceFunctionBytes.Op.packed .mul
      (wire cell.in0) (wire cell.in1) (wire cell.out) tailA tailB
  else False

/-- Every coherent assignment satisfying the three native selected rows
forces both the exact source-byte denotation and the public arithmetic claim.
This is conditional on the single coherent wire map and local row premises;
it is not a theorem about cryptographic proof acceptance. -/
theorem selected_native_rows_sound (fixed : List ColumnCell)
    (wire : Nat → Lanes) (input claim : Lanes) (tailA tailB : Tail)
    (hfixed : fixed = nativeCells)
    (hrows : fixed.Forall (packedAt wire tailA tailB))
    (hinput : wire 22 = input) (houtput : wire 25 = claim) :
    denotation sourceBytes input = some claim ∧
      claim = (fun i => (0 : S31.M31) - (input i + input i)) ∧
      fixed = OrderedSubtractionNativeRows.expectedCells expectedParsed := by
  have hplan := hfixed.trans native_cells_match_source
  subst fixed
  have hfirst : SourceFunctionBytes.Op.packed .add
      (wire 22) (wire 22) (wire 23) tailA tailB := by
    have h := hrows.1
    simpa [nativeCells, packedAt] using h
  have hsecond : SourceFunctionBytes.Op.packed .sub
      (wire 22) (wire 23) (wire 24) tailA tailB := by
    have h := hrows.2.1
    simpa [nativeCells, packedAt] using h
  have hthird : SourceFunctionBytes.Op.packed .sub
      (wire 24) (wire 22) (wire 25) tailA tailB := by
    have h := hrows.2.2
    simpa [nativeCells, packedAt] using h
  have haccept : OrderedSubtractionRelease.accepts
      (wire 22) (wire 23) (wire 24) (wire 25) tailA tailB :=
    ⟨hfirst, hsecond, hthird⟩
  have hsource := OrderedSubtractionConcrete.concrete_source_sound
    (wire 22) (wire 23) (wire 24) (wire 25) tailA tailB haccept
  have hclaim := OrderedSubtractionRelease.arbitrary_witness_sound
    (wire 22) (wire 23) (wire 24) (wire 25) tailA tailB haccept
  rw [hinput, houtput] at hsource hclaim
  exact ⟨hsource, hclaim, hplan⟩

end S31.Functional.Correspondence.OrderedSubtractionNativeSoundness
