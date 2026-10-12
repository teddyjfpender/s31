import S31.Gadgets.Air.DirectGateOodsLogUp
import S31.Gadgets.Air.CompositionFold

/-!
Pure eleven-root Gate composition model at supplied QM31 OODS samples.
The inverse zeroifier is an explicit input; its nonzero provenance and the
Fiat–Shamir coefficient draw are separate verifier obligations.
-/

namespace S31.Gadgets.Air.DirectGateOodsComposition

open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.DirectGatePolynomial

def arithmeticCells (cells : Cells) : ArithmeticCells QM where
  localFixed := cells.localFixed
  main := cells.main

def pureRoots (cells : Cells) (alpha z claimedScaled : QM) : List QM :=
  modeledArithmetic (arithmeticCells cells) ++
    [pair cells alpha z, last cells alpha z claimedScaled]

theorem pure_roots_length (cells : Cells) (alpha z claimedScaled : QM) :
    (pureRoots cells alpha z claimedScaled).length = 11 := by
  simp [pureRoots, modeledArithmetic]

/-- The native accumulator applies one common inverse zeroifier to every
selected root before its left-to-right Horner fold. -/
def quotientFold (coefficient inverseZeroifier : QM)
    (roots : List QM) : QM :=
  S31.Gadgets.Air.CompositionFold.fold coefficient
    (roots.map (· * inverseZeroifier))

theorem quotient_fold_factor (coefficient inverseZeroifier : QM)
    (roots : List QM) :
    quotientFold coefficient inverseZeroifier roots =
      S31.Gadgets.Air.CompositionFold.fold coefficient roots *
        inverseZeroifier := by
  let step := fun (acc root : QM) => acc * coefficient + root
  have aux (xs : List QM) (acc : QM) :
      (xs.map (· * inverseZeroifier)).foldl step
        (acc * inverseZeroifier) =
        (xs.foldl step acc) * inverseZeroifier := by
    induction xs generalizing acc with
    | nil => rfl
    | cons root rest ih =>
        simp only [List.map_cons, List.foldl_cons]
        calc
          (rest.map (· * inverseZeroifier)).foldl step
              (step (acc * inverseZeroifier) (root * inverseZeroifier)) =
            (rest.map (· * inverseZeroifier)).foldl step
              ((step acc root) * inverseZeroifier) := by
                congr 1
                dsimp [step]
                ring
          _ = (rest.foldl step (step acc root)) * inverseZeroifier :=
            ih (step acc root)
  simpa [quotientFold, S31.Gadgets.Air.CompositionFold.fold, step]
    using aux roots 0

end S31.Gadgets.Air.DirectGateOodsComposition
