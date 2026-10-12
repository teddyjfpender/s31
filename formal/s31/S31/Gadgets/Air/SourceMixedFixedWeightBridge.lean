import S31.Gadgets.Air.SourceMixedLookupBound
import S31.Gadgets.Functional.Correspondence.GeneratedMixedFixedRows

/-!
Kernel-checked multiplicity totals for the complete N1/N8 native fixed-row
exports. The bridge to an ideal `Boundary` explicitly assumes that its
ordered row multiplicities equal the exported eighth fixed column. This is
source-pinned honest-emitter evidence, not verifier authentication of a
prover-chosen fixed or main trace.
-/

namespace S31.Gadgets.Air.SourceMixedFixedWeightBridge

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedLookupBound

namespace Fixed
open S31.Functional.Correspondence.GeneratedMixedFixedRows

/-- The eighth entry of every exported row is the native preprocessed Gate
output multiplicity. The generated file separately proves all rows have
width eight, so the `getD` fallback is not reached. -/
def weights (fixedRows : List (List Nat)) : List Nat :=
  fixedRows.map fun row => row[7]?.getD 0

theorem n1_sum : (weights N1.fixedRows).sum = 1041 := by decide
theorem n8_sum : (weights N8.fixedRows).sum = 1097 := by decide

end Fixed

/-- If the modeled N1 Gate rows have exactly the native exported output
multiplicities, the numeric multiplicity part of `SourceShape` is discharged.
The other shape fields remain explicit source-to-Lean obligations. -/
theorem n1_source_shape (boundary : Boundary 1)
    (hrows : boundary.rows.length = 512)
    (hweights : boundary.rows.map CanonicalRow.multiplicity =
      Fixed.weights
        S31.Functional.Correspondence.GeneratedMixedFixedRows.N1.fixedRows)
    (huses : boundary.baselineUses = [])
    (hyields : boundary.baselineYields = [])
    (hrounds : ∀ call, boundary.rounds call = 16) :
    SourceShape boundary := by
  refine ⟨hrows, ?_, huses, hyields, hrounds⟩
  rw [hweights, Fixed.n1_sum]

theorem n8_source_shape (boundary : Boundary 8)
    (hrows : boundary.rows.length = 512)
    (hweights : boundary.rows.map CanonicalRow.multiplicity =
      Fixed.weights
        S31.Functional.Correspondence.GeneratedMixedFixedRows.N8.fixedRows)
    (huses : boundary.baselineUses = [])
    (hyields : boundary.baselineYields = [])
    (hrounds : ∀ call, boundary.rounds call = 16) :
    SourceShape boundary := by
  refine ⟨hrows, ?_, huses, hyields, hrounds⟩
  rw [hweights, Fixed.n8_sum]

end S31.Gadgets.Air.SourceMixedFixedWeightBridge
