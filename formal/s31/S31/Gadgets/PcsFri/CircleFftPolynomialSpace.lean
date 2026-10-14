import S31.Gadgets.PcsFri.CircleRecursiveBasisDegree
import Mathlib.Tactic

/-!
The paper's circle FFT space of order `k >= 1` is represented here as
`P(x) + y Q(x)` with both ordinary polynomial degrees strictly below
`2^(k-1)`. The native recursive coefficient basis has precisely this
stronger, two-component degree property; a two-sided Laurent radius alone
does not state the excluded top FFT basis direction.

This is an algebraic model of the coefficient recurrence. It does not prove
that the Zig FFT/interpolant produces these coefficients or identify all
native FRI oracle functions with the published protocol.
-/

namespace S31.Gadgets.PcsFri.CircleFftPolynomialSpace

open Polynomial
open S31.Gadgets.PcsFri.CircleRecursiveBasisDegree

variable {F : Type*} [Field F]

noncomputable def xFactorPolynomial : Nat → Polynomial F
  | 0 => X
  | j + 1 => C 2 * xFactorPolynomial j ^ 2 - 1

def pairValue {E : Type*} [Field E] [Algebra F E]
    (pair : Polynomial F × Polynomial F) (x y : E) : E :=
  eval₂ (algebraMap F E) x pair.1 + y * eval₂ (algebraMap F E) x pair.2

/-- Coefficient log zero has one scalar; coefficient log one has `c₀+c₁y`.
Every higher merge multiplies the upper half by the appropriate native
double-angle x factor, separately in the two polynomial components. -/
noncomputable def coefficientPair : Nat → List F → Polynomial F × Polynomial F
  | 0, coefficients => (C (coefficients.headD 0), 0)
  | 1, coefficients =>
      (C (coefficients.headD 0), C ((coefficients.drop 1).headD 0))
  | k + 2, coefficients =>
      let left := coefficientPair (k + 1) (coefficients.take (2 ^ (k + 1)))
      let right := coefficientPair (k + 1) (coefficients.drop (2 ^ (k + 1)))
      let factor := xFactorPolynomial k
      (left.1 + factor * right.1, left.2 + factor * right.2)

/-- Exact two-component form of the paper's `L'_k(F)` for `k >= 1`.
The full radius-`2^(k-1)` Laurent band has one more dimension; bounding
both component degrees excludes that extra top direction. -/
def InCircleFftSpace (k : Nat) (pair : Polynomial F × Polynomial F) : Prop :=
  pair.1.natDegree < 2 ^ (k - 1) ∧
  pair.2.natDegree < 2 ^ (k - 1)

theorem xFactorPolynomial_degree (j : Nat) :
    (xFactorPolynomial (F := F) j).natDegree ≤ 2 ^ j := by
  induction j with
  | zero => simp [xFactorPolynomial]
  | succ j ih =>
      have hsquare : ((xFactorPolynomial (F := F) j) ^ 2).natDegree ≤
          2 * (2 ^ j) := by
        calc
          _ ≤ 2 * (xFactorPolynomial (F := F) j).natDegree := by
            simpa [Nat.mul_comm] using
              (Polynomial.natDegree_pow_le (xFactorPolynomial (F := F) j) 2)
          _ ≤ 2 * (2 ^ j) := Nat.mul_le_mul_left 2 ih
      have hscaled : (C (2 : F) * xFactorPolynomial j ^ 2).natDegree ≤
          2 * (2 ^ j) := by
        calc
          _ ≤ (C (2 : F)).natDegree +
              ((xFactorPolynomial (F := F) j) ^ 2).natDegree :=
                Polynomial.natDegree_mul_le
          _ ≤ 2 * (2 ^ j) := by simpa using hsquare
      have hdiff : (C (2 : F) * xFactorPolynomial j ^ 2 - 1).natDegree ≤
          2 * (2 ^ j) :=
        (Polynomial.natDegree_sub_le _ _).trans (max_le hscaled (by simp))
      simpa [xFactorPolynomial, pow_succ, Nat.mul_comm] using hdiff

private theorem step_degree
    (k : Nat) (left right : Polynomial F × Polynomial F)
    (hleft : InCircleFftSpace (k + 1) left)
    (hright : InCircleFftSpace (k + 1) right) :
    InCircleFftSpace (k + 2)
      (left.1 + xFactorPolynomial k * right.1,
       left.2 + xFactorPolynomial k * right.2) := by
  have factorBound : (xFactorPolynomial (F := F) k).natDegree ≤ 2 ^ k :=
    xFactorPolynomial_degree k
  have bound (a b : Polynomial F)
      (ha : a.natDegree < 2 ^ k) (hb : b.natDegree < 2 ^ k) :
      (a + xFactorPolynomial k * b).natDegree < 2 ^ (k + 1) := by
    have hmul : (xFactorPolynomial k * b).natDegree < 2 ^ (k + 1) := by
      have hprod := Polynomial.natDegree_mul_le
        (p := xFactorPolynomial k) (q := b)
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by simp [pow_succ, Nat.mul_comm]
      omega
    have hsum := Polynomial.natDegree_add_le a (xFactorPolynomial k * b)
    omega
  simp only [InCircleFftSpace, Nat.add_sub_cancel] at hleft hright ⊢
  exact ⟨bound left.1 right.1 hleft.1 hright.1,
    bound left.2 right.2 hleft.2 hright.2⟩

/-- Every source-transcribed recursive coefficient vector lies in the
paper-shaped circle FFT space, rather than only in the one-dimension-larger
two-sided Laurent band. The theorem is independent of coefficient values. -/
theorem coefficientPair_in_fft_space
    (k : Nat) (hk : 1 ≤ k) (coefficients : List F) :
    InCircleFftSpace k (coefficientPair k coefficients) := by
  induction k using Nat.strong_induction_on generalizing coefficients with
  | h k ih =>
      cases k with
      | zero => omega
      | succ k =>
          cases k with
          | zero =>
              simp [coefficientPair, InCircleFftSpace]
          | succ j =>
              have hleft := ih (j + 1) (by omega) (by omega)
                (coefficients.take (2 ^ (j + 1)))
              have hright := ih (j + 1) (by omega) (by omega)
                (coefficients.drop (2 ^ (j + 1)))
              simpa only [coefficientPair] using
                step_degree j
                  (coefficientPair (j + 1)
                    (coefficients.take (2 ^ (j + 1))))
                  (coefficientPair (j + 1)
                    (coefficients.drop (2 ^ (j + 1))))
                  hleft hright

theorem xFactorPolynomial_eval
    {E : Type*} [Field E] [Algebra F E]
    (x : E) (j : Nat) :
    eval₂ (algebraMap F E) x (xFactorPolynomial (F := F) j) =
      xFactorValue x j := by
  induction j with
  | zero => simp [xFactorPolynomial, xFactorValue]
  | succ j ih =>
      simp only [xFactorPolynomial, xFactorValue,
        Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_pow, Polynomial.eval₂_C,
        Polynomial.eval₂_one, ih]
      rw [show (algebraMap F E) (2 : F) = (2 : E) by
        exact _root_.map_ofNat (algebraMap F E) 2]

/-- Evaluating the two ordinary-polynomial components on a circle point
equals the recursive field-value evaluator for every coefficient slot.
Consequently the stronger FFT-space witness is tied to the same evaluation
rule as the existing Laurent word. -/
theorem coefficientPair_eval
    {E : Type*} [Field E] [Algebra F E]
    (x y : E) (k : Nat) (coefficients : List F) :
    pairValue (coefficientPair k coefficients) x y =
      recursiveValue x y k coefficients := by
  induction k using Nat.strong_induction_on generalizing coefficients with
  | h k ih =>
      cases k with
      | zero => simp [coefficientPair, pairValue, recursiveValue]
      | succ k =>
          cases k with
          | zero =>
              cases coefficients with
              | nil => simp [coefficientPair, pairValue, recursiveValue,
                  nativeFactorValue, List.take]
              | cons a rest =>
                  cases rest with
                  | nil => simp [coefficientPair, pairValue, recursiveValue,
                      nativeFactorValue, List.take]
                  | cons b rest =>
                      simp [coefficientPair, pairValue, recursiveValue,
                        nativeFactorValue, List.take, mul_comm]
          | succ j =>
              have hleft := ih (j + 1) (by omega)
                (coefficients.take (2 ^ (j + 1)))
              have hright := ih (j + 1) (by omega)
                (coefficients.drop (2 ^ (j + 1)))
              let left := coefficientPair (j + 1)
                (coefficients.take (2 ^ (j + 1)))
              let right := coefficientPair (j + 1)
                (coefficients.drop (2 ^ (j + 1)))
              change pairValue
                  (left.1 + xFactorPolynomial j * right.1,
                   left.2 + xFactorPolynomial j * right.2) x y =
                recursiveValue x y (j + 1)
                  (coefficients.take (2 ^ (j + 1))) +
                recursiveValue x y (j + 1)
                  (coefficients.drop (2 ^ (j + 1))) * xFactorValue x j
              dsimp [pairValue] at hleft hright ⊢
              rw [Polynomial.eval₂_add, Polynomial.eval₂_add,
                Polynomial.eval₂_mul, Polynomial.eval₂_mul,
                xFactorPolynomial_eval]
              linear_combination hleft + xFactorValue x j * hright

/-- The ordinary-polynomial FFT-space witness and the existing Laurent word
evaluate identically at every nonzero Fourier point satisfying the circle
coordinate equations. This is a mathematical basis identity, not native FFT
array provenance. -/
theorem coefficientPair_matches_laurent
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i : F) (hi : i ^ 2 = -1) (z : Eˣ)
    (k : Nat) (coefficients : List F) :
    pairValue (coefficientPair k coefficients)
      (CircleLaurentDegree.fourierX z.val z⁻¹.val)
      (CircleLaurentDegree.fourierY
        ((algebraMap F E) i) z.val z⁻¹.val) =
      LaurentPolynomial.eval₂ (algebraMap F E) z
        (coefficientWord i k coefficients) := by
  rw [coefficientPair_eval]
  exact (coefficientWord_eval_algebra i hi z k coefficients).symm

/-- The three sparse Gate source-height coefficient vectors have the exact
paper-shaped component degree caps: `<32768`, `<512`, and `<8`. -/
theorem accepted_sparse_source_fft_spaces
    (coefficients₁₇ coefficients₁₁ coefficients₅ : List F) :
    InCircleFftSpace 16 (coefficientPair 16 coefficients₁₇) ∧
    InCircleFftSpace 10 (coefficientPair 10 coefficients₁₁) ∧
    InCircleFftSpace 4 (coefficientPair 4 coefficients₅) := by
  exact ⟨coefficientPair_in_fft_space 16 (by decide) coefficients₁₇,
    coefficientPair_in_fft_space 10 (by decide) coefficients₁₁,
    coefficientPair_in_fft_space 4 (by decide) coefficients₅⟩

theorem accepted_sparse_component_thresholds :
    2 ^ (16 - 1) = 32768 ∧
    2 ^ (10 - 1) = 512 ∧
    2 ^ (4 - 1) = 8 := by decide

end S31.Gadgets.PcsFri.CircleFftPolynomialSpace
