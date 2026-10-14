import S31.Gadgets.PcsFri.NativeCircleQuotientRows
import S31.Gadgets.PcsFri.SparseP05AcceptedH3Roster
import Mathlib.Tactic

/-!
One-row algebra for the accepted sparse Gate H3 claim roster. The native
`complexConjugateLineCoeffs` numerator is modeled by `nativeNumerator`; its
CM31 determinant is modeled here in field coordinates. The Zig fixture reads
the accepted verifier's first authenticated lifted query and checks all 73
concrete sampled rows against the production PCS quotient evaluator.

These theorems are conditional on the row divisor and interpolation guard.
They do not prove any whole-domain degree bound or identify the S-two paper's
batch width.
-/

namespace S31.PcsFri.SparseP05AcceptedH3Rows

open S31.Gadgets.PcsFri.NativeCircleQuotientRows
open S31.PcsFri.SparseP05AcceptedH3Roster

/-- The accepted claim map contains 73 QM31 points. Every captured point has
a nonzero imaginary CM31 y-coordinate, the concrete guard needed by native
`complexConjugateLineCoeffs`. The values are generated from accepted proof
limbs and checked here as finite arithmetic, not assumed. -/
theorem accepted_claim_y_imaginary_guard :
    SparseP05AcceptedH3Data.claimYImag.length = 73 ∧
    ∀ pair ∈ SparseP05AcceptedH3Data.claimYImag, pair ≠ (0, 0) := by
  decide

variable {F : Type*} [Field F]

/-- The exact determinant used by native `denominatorInversesInto`: the
real/imaginary CM31 coordinates of the OOD point are explicit. -/
def rowDivisor (x₀ y₀ x₁ y₁ rowX rowY : F) : F :=
  (x₀ - rowX) * y₁ - (y₀ - rowY) * x₁

/-- The unweighted `ownQuotientAt` row word, with numerator from the
conjugate OOD point/value and the native determinant. -/
def ownRow (x₀ y₀ x₁ y₁ v₀ v₁ u rowX rowY source : F) : F :=
  nativeNumerator v₀ v₁ y₀ y₁ u rowY source /
    rowDivisor x₀ y₀ x₁ y₁ rowX rowY

theorem ownRow_cross_mul
    (x₀ y₀ x₁ y₁ v₀ v₁ u rowX rowY source : F)
    (hdiv : rowDivisor x₀ y₀ x₁ y₁ rowX rowY ≠ 0) :
    ownRow x₀ y₀ x₁ y₁ v₀ v₁ u rowX rowY source *
      rowDivisor x₀ y₀ x₁ y₁ rowX rowY =
      nativeNumerator v₀ v₁ y₀ y₁ u rowY source := by
  simp [ownRow, hdiv]

/-- After removing the native `-2*u*y₁` scale, the row equals the residual
against the two-point affine claim divided by the same determinant. -/
theorem ownRow_eq_scaled_affine_residual
    (x₀ y₀ x₁ y₁ v₀ v₁ u rowX rowY source : F)
    (hy : y₁ ≠ 0) :
    ownRow x₀ y₀ x₁ y₁ v₀ v₁ u rowX rowY source =
      (-2 * u * y₁) *
        ((source - affineClaim v₀ v₁ y₀ y₁ rowY) /
          rowDivisor x₀ y₀ x₁ y₁ rowX rowY) := by
  unfold ownRow
  exact nativeQuotient_eq_scaled_own_quotient
    v₀ v₁ y₀ y₁ u rowY source
    (rowDivisor x₀ y₀ x₁ y₁ rowX rowY) hy

/-- The variables retained for one source-bound candidate row. -/
structure RowData (F : Type*) where
  x₀ : F
  y₀ : F
  x₁ : F
  y₁ : F
  v₀ : F
  v₁ : F
  u : F
  rowX : F
  rowY : F
  source : F

def divisor (r : RowData F) : F :=
  rowDivisor r.x₀ r.y₀ r.x₁ r.y₁ r.rowX r.rowY

def quotient (r : RowData F) : F :=
  ownRow r.x₀ r.y₀ r.x₁ r.y₁ r.v₀ r.v₁ r.u r.rowX r.rowY r.source

def numerator (r : RowData F) : F :=
  nativeNumerator r.v₀ r.v₁ r.y₀ r.y₁ r.u r.rowY r.source

/-- Explicit finite roster coverage lets a row premise for each candidate
claim reach every accepted claim index. The premise is visible: this theorem
does not authenticate rows or infer a polynomial from sampled values. -/
theorem all_accepted_rows_cross_mul
    (row : Nat → RowData F)
    (hdiv : ∀ i ∈ explicitClaimRefs, divisor (row i) ≠ 0) :
    ∀ i, i < 73 → quotient (row i) * divisor (row i) = numerator (row i) := by
  apply transfer_to_all_accepted_claims
  intro i hi
  simpa [quotient, divisor, numerator] using
    ownRow_cross_mul (row i).x₀ (row i).y₀ (row i).x₁ (row i).y₁
      (row i).v₀ (row i).v₁ (row i).u (row i).rowX (row i).rowY
      (row i).source
      (by simpa [divisor] using hdiv i hi)

end S31.PcsFri.SparseP05AcceptedH3Rows
