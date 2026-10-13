import S31.Gadgets.PcsFri.FoldAlgebra
import S31.Gadgets.PcsFri.SparseCascadeQueries

/-!
One *exact* CAS05 paired sparse fold round, separated from proximity claims.

The native verifier reads two source values at `pairBase r step`; after the
first step it also reads two values from the preceding line commitment at
the same rows. Its `foldPair` is `(a+b)+α(a-b)/coordinate`. The subsequent
`foldInsertedPair` computes the previous-line fold plus `α²` times the source
fold. This is the order in `paired_cascade_experimental.zig`; the older
`FoldAlgebra.circleAccumulate` is a different, generic ordering.

The polynomial theorem below uses finite coefficient tuples, not an oracle
degree assumption. The row theorem assumes the opened values are evaluations
at conjugate coordinate pairs and that the verifier's next-row equality
passed. For any single pair with nonzero coordinate in odd characteristic,
such local affine coefficients can always be interpolated. This theorem does
not establish a globally low-degree committed oracle or correlated agreement.
Authentication and the global-oracle relation remain separate obligations.
-/

namespace S31.Gadgets.PcsFri.PairedSparseRound

open Polynomial
open S31.Gadgets.PcsFri.FoldAlgebra
open S31.Gadgets.PcsFri.SparseCascadeQueries

variable {F : Type*} [Field F]

/-- The exact native `foldInsertedPair` order, after successful inversion of
the two nonzero base-field coordinates. -/
def nativeInsertedRound (alpha x y previousEven previousOdd
    insertedEven insertedOdd : F) : F :=
  pairFold alpha x⁻¹ previousEven previousOdd +
    alpha ^ 2 * pairFold alpha y⁻¹ insertedEven insertedOdd

/-- One coefficient pair evaluated at the two conjugate coordinates. -/
def atPositive (c₀ c₁ coordinate : F) : F := c₀ + coordinate * c₁
def atNegative (c₀ c₁ coordinate : F) : F := c₀ - coordinate * c₁

/-- The exact challenge polynomial for one interior CAS05 round. The factor
two is retained because the native inverse butterfly omits a half. -/
noncomputable def roundPolynomial (p₀ p₁ q₀ q₁ : F) : Polynomial F :=
  C (2 * p₀) + X * C (2 * p₁) +
    X ^ 2 * C (2 * q₀) + X ^ 3 * C (2 * q₁)

theorem eval_roundPolynomial (alpha p₀ p₁ q₀ q₁ : F) :
    eval alpha (roundPolynomial p₀ p₁ q₀ q₁) =
      2 * (p₀ + alpha * p₁) + alpha ^ 2 * 2 * (q₀ + alpha * q₁) := by
  simp [roundPolynomial]
  ring

/-- A genuine finite coefficient/evaluation refinement of the native fold.
Both coordinates must be nonzero because Zig rejects failed inversions. -/
theorem nativeInsertedRound_of_coefficients
    (alpha x y p₀ p₁ q₀ q₁ : F) (hx : x ≠ 0) (hy : y ≠ 0) :
    nativeInsertedRound alpha x y
      (atPositive p₀ p₁ x) (atNegative p₀ p₁ x)
      (atPositive q₀ q₁ y) (atNegative q₀ q₁ y) =
        eval alpha (roundPolynomial p₀ p₁ q₀ q₁) := by
  rw [eval_roundPolynomial]
  simp only [nativeInsertedRound, atPositive, atNegative]
  rw [pairFold_affine p₀ p₁ alpha x hx,
      pairFold_affine q₀ q₁ alpha y hy]
  ring

theorem roundPolynomial_natDegree_le (p₀ p₁ q₀ q₁ : F) :
    (roundPolynomial p₀ p₁ q₀ q₁).natDegree ≤ 3 := by
  unfold roundPolynomial
  compute_degree!

/-- At step zero the native checker has no preceding line commitment. -/
theorem firstRound_of_coefficients (alpha y q₀ q₁ : F) (hy : y ≠ 0) :
    pairFold alpha y⁻¹ (atPositive q₀ q₁ y)
      (atNegative q₀ q₁ y) = 2 * (q₀ + alpha * q₁) := by
  exact pairFold_affine q₀ q₁ alpha y hy

/-- Native circle coordinates for a conjugate pair. The points keep their
`x` coordinate and have opposite `y` coordinates. -/
structure CirclePoint (F : Type*) where
  x : F
  y : F

def conjugate (p : CirclePoint F) : CirclePoint F := ⟨p.x, -p.y⟩
def double (p : CirclePoint F) : CirclePoint F :=
  ⟨p.x * p.x - p.y * p.y, p.x * p.y + p.y * p.x⟩

/-- Circle doubling commutes with conjugation. It does not identify the two
conjugate points: the verifier selects one projected row with the raw low
bit, while the fold combines both opened rows at their shared `y` scale. -/
theorem double_conjugate (p : CirclePoint F) :
    double (conjugate p) = conjugate (double p) := by
  cases p with
  | mk x y =>
      simp only [double, conjugate]
      congr 1 <;> ring

/-- A two-coefficient circle evaluation at one point. Every two opened words
can be interpolated locally when the coordinate and `2` are invertible, so
this definition does not assert global degree one for the committed oracle. -/
def circlePairEval (q₀ q₁ : F) (p : CirclePoint F) : F :=
  q₀ + p.y * q₁

theorem circlePairEval_conjugate (q₀ q₁ : F) (p : CirclePoint F) :
    circlePairEval q₀ q₁ (conjugate p) = atNegative q₀ q₁ p.y := by
  simp [circlePairEval, conjugate, atNegative]
  ring

/-- The source value at the selected projected row is one of the two opened
values. The raw low bit chooses the circle half; it is not discarded by
projection. -/
theorem selected_source_point_from_pair (r step : Nat)
    (point : Nat → CirclePoint F)
    (hpair : point (pairBase r step + 1) =
      conjugate (point (pairBase r step))) :
    point (projectedCircleRow r step) =
      if r % 2 = 0 then point (pairBase r step)
      else conjugate (point (pairBase r step)) := by
  have hbit : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hbit with hzero | hone
  · simp [projectedCircleRow, hzero]
  · simp [projectedCircleRow, hone, hpair]

/-- The exact raw-query row used by the next line check is the quotient of
the current even source row by two. -/
theorem next_line_row_from_source_pair (r step : Nat) :
    pairBase r step / 2 = lineFoldRow r step :=
  opened_pair_folds_to_line_row r step

/-- The next line row lies in the next authenticated adjacent pair. -/
theorem next_line_row_is_opened (r step : Nat) :
    lineFoldRow r step = pairBase r (step + 1) ∨
      lineFoldRow r step = pairBase r (step + 1) + 1 :=
  line_row_in_next_opened_pair r step

/-- If the four authenticated opened values really are evaluations of two
coefficient pairs at the native coordinates, the accepted interior equality
identifies the selected next line word with this degree-three polynomial.
`hcheck` is exactly the verifier's `IntermediateFoldMismatch` check. -/
theorem accepted_interior_round_polynomial
    (r step : Nat) (alpha x y p₀ p₁ q₀ q₁ : F)
    (previous source nextLine : Nat → F)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hp₀ : previous (pairBase r step) = atPositive p₀ p₁ x)
    (hp₁ : previous (pairBase r step + 1) = atNegative p₀ p₁ x)
    (hq₀ : source (pairBase r step) = atPositive q₀ q₁ y)
    (hq₁ : source (pairBase r step + 1) = atNegative q₀ q₁ y)
    (hcheck : nativeInsertedRound alpha x y
      (previous (pairBase r step)) (previous (pairBase r step + 1))
      (source (pairBase r step)) (source (pairBase r step + 1)) =
        nextLine (lineFoldRow r step)) :
    nextLine (lineFoldRow r step) =
      eval alpha (roundPolynomial p₀ p₁ q₀ q₁) := by
  rw [hp₀, hp₁, hq₀, hq₁] at hcheck
  exact hcheck.symm.trans
    (nativeInsertedRound_of_coefficients alpha x y p₀ p₁ q₀ q₁ hx hy)

/-- A finite source pair obtained by evaluating the same local coefficient
pair at conjugate circle points. This removes the two source-row premises
from the preceding theorem, but the point-pair premise still needs a native
canonical-domain refinement and commitment binding. -/
theorem accepted_interior_round_from_circle_pair
    (r step : Nat) (alpha x p₀ p₁ q₀ q₁ : F)
    (point : Nat → CirclePoint F)
    (previous nextLine : Nat → F)
    (hx : x ≠ 0)
    (hy : (point (pairBase r step)).y ≠ 0)
    (hpair : point (pairBase r step + 1) =
      conjugate (point (pairBase r step)))
    (hp₀ : previous (pairBase r step) = atPositive p₀ p₁ x)
    (hp₁ : previous (pairBase r step + 1) = atNegative p₀ p₁ x)
    (hcheck : nativeInsertedRound alpha x
      (point (pairBase r step)).y
      (previous (pairBase r step)) (previous (pairBase r step + 1))
      (circlePairEval q₀ q₁ (point (pairBase r step)))
      (circlePairEval q₀ q₁ (point (pairBase r step + 1))) =
        nextLine (lineFoldRow r step)) :
    nextLine (lineFoldRow r step) =
      eval alpha (roundPolynomial p₀ p₁ q₀ q₁) := by
  apply accepted_interior_round_polynomial r step alpha x
    (point (pairBase r step)).y p₀ p₁ q₀ q₁
    previous (fun row => circlePairEval q₀ q₁ (point row)) nextLine
    hx hy hp₀ hp₁
  · rfl
  · simpa [hpair] using circlePairEval_conjugate q₀ q₁
      (point (pairBase r step))
  · exact hcheck

end S31.Gadgets.PcsFri.PairedSparseRound
