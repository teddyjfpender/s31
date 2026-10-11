import S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
import S31.Gadgets.Air.DirectGateNativeIndices

/-!
The selected Gate component's three OODS sampled-value trees. The resident
verifier reads these values before the separate PCS opening verification.
All statements here are conditional on the exact selected mask shape; no
statement authenticates a sample or proves its polynomial evaluation.
-/

namespace S31.Gadgets.Air.DirectGateOodsOpenings

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
open S31.Gadgets.Air.DirectGateNativeIndices

/-- `fixed` is indexed by global preprocessed column, while the other two
trees use the selected component's zero-based trace spans. -/
structure Samples where
  fixed : Fin 8 → List QM
  main : Fin 12 → List QM
  interaction : Fin 8 → List QM

/-- Exact sample-list lengths expected by the selected Gate geometry. -/
structure Shape (samples : Samples) : Prop where
  fixed : ∀ i, (samples.fixed i).length = 1
  main : ∀ i, (samples.main i).length = 1
  interactionFirst : ∀ i, i.val < 4 → (samples.interaction i).length = 1
  interactionLast : ∀ i, 4 ≤ i.val → (samples.interaction i).length = 2

def fixedRead (samples : Samples) (column : Fin 8) : Option QM :=
  (samples.fixed (fixedReadOrder column))[0]?

def mainRead (samples : Samples) (column : Fin 12) : Option QM :=
  (samples.main column)[0]?

def interactionRead (samples : Samples) (column : Fin 8)
    (offset : Int) : Option QM :=
  interactionMaskRead samples.interaction column offset

/-- Every default below is unreachable when `Shape` holds. Keeping this
function total lets the same theorem quantify over arbitrary proof masks. -/
def cellsOfSamples (samples : Samples) : Cells where
  localFixed i := (fixedRead samples i).getD 0
  main i := (mainRead samples i).getD 0
  interaction i := (interactionRead samples i 0).getD 0
  previousInteraction i := (interactionRead samples i (-1)).getD 0

private theorem singleton_at_zero {xs : List QM} (h : xs.length = 1) :
    xs[0]? = some (xs[0]?.getD 0) := by
  cases xs with
  | nil => simp at h
  | cons x xs => simp

theorem fixed_read_eq_cells (samples : Samples) (shape : Shape samples)
    (column : Fin 8) :
    fixedRead samples column =
      some ((cellsOfSamples samples).localFixed column) := by
  exact singleton_at_zero (shape.fixed (fixedReadOrder column))

theorem main_read_eq_cells (samples : Samples) (shape : Shape samples)
    (column : Fin 12) :
    mainRead samples column = some ((cellsOfSamples samples).main column) := by
  exact singleton_at_zero (shape.main column)

theorem interaction_current_eq_cells (samples : Samples) (shape : Shape samples)
    (column : Fin 8) :
    interactionRead samples column 0 =
      some ((cellsOfSamples samples).interaction column) := by
  fin_cases column <;>
    simp [interactionRead, interactionMaskRead, interactionOffsets,
      offsetIndex, cellsOfSamples, shape.interactionFirst, shape.interactionLast]

theorem interaction_previous_eq_cells (samples : Samples) (shape : Shape samples)
    (column : Fin 8) (h : 4 ≤ column.val) :
    interactionRead samples column (-1) =
      some ((cellsOfSamples samples).previousInteraction column) := by
  fin_cases column <;>
    simp_all [interactionRead, interactionMaskRead, interactionOffsets,
      offsetIndex, cellsOfSamples, shape.interactionLast]

end S31.Gadgets.Air.DirectGateOodsOpenings
