import S31.Gadgets.Functional.Correspondence.OrderedSubtractionNativeRows

/-! Generated from the sealed native `release_sub4` topology by
`ordered_subtraction_native_fixture.py`. Selected fixed cells are compared
with the independent source schedule. A fresh native run also compares the
functional helper package's complete fixed columns and AIR geometry. The
fixed-column hash and key root are recorded below. This exported-artifact
check does not authenticate arbitrary proof openings. Do not edit directly. -/

namespace S31.Functional.Correspondence.GeneratedOrderedSubtractionNativeRows

open S31.Functional.SSAAirColumnCells
open S31.Functional.Correspondence.OrderedSubtractionNativeRows
open S31.Functional.Correspondence.GeneratedOrderedSubtractionRelease

-- Native preprocessed root: ca3dad2dfaa22e18e5707334c182c1e242e219b7d806e65d047da9719834a6cf
-- Full fixed-column SHA-256: eb815a6b49b79b74b69515fea78dac6dac51ea6a23419b2b896e0fecfb33af5b
-- Native exporter binary SHA-256: 43025dd1f31b59e7bd638a4b5b7159624ebbd0ae2f70bfc23ff4dddf0e44a274

def nativeCells : List ColumnCell := [
  { traceRow := 3, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 22, out := 23, mults := 1 },
  { traceRow := 474, addFlag := 0, subFlag := 1, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 23, out := 24, mults := 1 },
  { traceRow := 475, addFlag := 0, subFlag := 1, mulFlag := 0, pointwiseMulFlag := 0, in0 := 24, in1 := 22, out := 25, mults := 4 }
]

def changedSubSelectorCells : List ColumnCell := [
  { traceRow := 3, addFlag := 1, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 22, out := 23, mults := 1 },
  { traceRow := 474, addFlag := 0, subFlag := 0, mulFlag := 0, pointwiseMulFlag := 0, in0 := 22, in1 := 23, out := 24, mults := 1 },
  { traceRow := 475, addFlag := 0, subFlag := 1, mulFlag := 0, pointwiseMulFlag := 0, in0 := 24, in1 := 22, out := 25, mults := 4 }
]

theorem native_cells_match_source :
    nativeCells = expectedCells expectedParsed := by decide

theorem native_partition_is_512 :
    addRows expectedParsed + (1 + countOp expectedParsed.instructions .sub) +
      27 + (8 + countOp expectedParsed.instructions .mul) = 512 := by
  exact partition_count expectedParsed (by decide)

theorem changed_sub_selector_rejected :
    changedSubSelectorCells ≠ expectedCells expectedParsed := by decide

end S31.Functional.Correspondence.GeneratedOrderedSubtractionNativeRows
