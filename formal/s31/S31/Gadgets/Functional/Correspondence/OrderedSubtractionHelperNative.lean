import S31.Gadgets.Functional.Correspondence.GeneratedOrderedSubtractionHelper
import S31.Gadgets.Functional.Correspondence.OrderedSubtractionNativeSoundness

/-!
The checked-in pure helper and direct spellings have the same normalized
three-operation DAG, selected native fixed cells, and conditional packed-row
soundness theorem. This is a source-byte proof of zero helper gate overhead
for this bounded static call. Native main-row and lookup authentication remain
explicit external obligations.
-/

namespace S31.Functional.Correspondence.OrderedSubtractionHelperNative

open S31.Functional.SSAAirColumnCells
open OrderedSubtractionBytes
open GeneratedOrderedSubtractionHelper
open GeneratedOrderedSubtractionNativeRows
open GeneratedOrderedSubtractionRelease

theorem helper_selected_native_rows_sound (fixed : List ColumnCell)
    (wire : Nat → Lanes) (input claim : Lanes) (tailA tailB : Tail)
    (hfixed : fixed = nativeCells)
    (hrows : fixed.Forall
      (OrderedSubtractionNativeSoundness.packedAt wire tailA tailB))
    (hinput : wire 22 = input) (houtput : wire 25 = claim) :
    OrderedSubtractionHelperBytes.denotation functionalBytes input = some claim ∧
      claim = (fun i => (0 : S31.M31) - (input i + input i)) ∧
      fixed = OrderedSubtractionNativeRows.expectedCells expectedParsed := by
  have h := OrderedSubtractionNativeSoundness.selected_native_rows_sound
    fixed wire input claim tailA tailB hfixed hrows hinput houtput
  rw [helper_direct_denotation_equal input]
  exact h

end S31.Functional.Correspondence.OrderedSubtractionHelperNative
