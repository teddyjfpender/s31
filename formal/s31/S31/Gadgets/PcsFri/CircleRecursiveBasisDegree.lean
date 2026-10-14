import S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
import S31.Gadgets.PcsFri.CircleLaurentUniqueness
import S31.Gadgets.PcsFri.SparseP05TwoQDegree
import Mathlib.Tactic

/-!
An all-coefficient algebraic model of native `CircleCoefficients` evaluation.
The native factor schedule is `y, x, doubleX(x), doubleX²(x), ...`, and its
recursive half merge is `left + right * factor[k-1]`. We prove the resulting
Laurent support bound for *every* coefficient list, not just the first four
slots. Matching the native iterative carry loop, FFT interpolation, and
authenticated source columns to this model are separate refinements.
-/

namespace S31.Gadgets.PcsFri.CircleRecursiveBasisDegree

open LaurentPolynomial AddMonoidAlgebra
open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.CircleLaurentQuotient
open S31.Gadgets.PcsFri.CircleLaurentUniqueness
open S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
open S31.Gadgets.PcsFri.NativeCircleQuotientRows

variable {F : Type*} [Field F]

theorem constant_in_band (c : F) (n : Nat) :
    InCircleBand n (C c : CirclePoly F) := by
  intro k hk
  by_cases h : k = 0
  · subst k
    constructor <;> simp
  · have hz : (C c : CirclePoly F) k = 0 := by
      simp [LaurentPolynomial.C_apply, h]
    exact False.elim (hk hz)

/-- Support radii add under multiplication. The proof shifts each Laurent
word to an ordinary polynomial, multiplies there, then shifts back. -/
theorem band_mul (f g : CirclePoly F) (n m : Nat)
    (hf : InCircleBand n f) (hg : InCircleBand m g) :
    InCircleBand (n + m) (f * g) := by
  obtain ⟨p, hp, hfp⟩ := band_has_shifted_polynomial f n hf
  obtain ⟨q, hq, hgq⟩ := band_has_shifted_polynomial g m hg
  have hpq : (p * q).natDegree ≤ 2 * (n + m) := by
    have hmul : (p * q).natDegree ≤ p.natDegree + q.natDegree :=
      Polynomial.natDegree_mul_le
    omega
  have hband := shifted_polynomial_in_band (p * q) (n + m) hpq
  have hrepr : f * g = (p * q).toLaurent * T (-((n + m : Nat) : ℤ)) := by
    rw [hfp, hgq, map_mul]
    have hshift : (T (-(n : ℤ)) : CirclePoly F) * T (-(m : ℤ)) =
        T (-((n + m : Nat) : ℤ)) := by
      rw [← LaurentPolynomial.T_add]
      congr 1
      push_cast
      ring
    rw [← hshift]
    ring
  rw [hrepr]
  exact hband

/-- The x-coordinate after `j` native `doubleX` applications, as a Laurent
word. `xFactor 0` is x itself. -/
noncomputable def xFactor (i : F) : Nat → CirclePoly F
  | 0 => xLaurent i
  | j + 1 => C 2 * (xFactor i j * xFactor i j) - 1

def xFactorValue (x : F) : Nat → F
  | 0 => x
  | j + 1 => 2 * (xFactorValue x j) ^ 2 - 1

noncomputable def nativeFactor (i : F) : Nat → CirclePoly F
  | 0 => yLaurent i
  | j + 1 => xFactor i j

def nativeFactorValue (x y : F) : Nat → F
  | 0 => y
  | j + 1 => xFactorValue x j

def factorRadius : Nat → Nat
  | 0 => 1
  | j + 1 => 2 ^ j

theorem xFactor_band (i : F) (j : Nat) :
    InCircleBand (2 ^ j) (xFactor i j) := by
  induction j with
  | zero =>
      simpa [xFactor] using line_in_band_one i 0 0 0 (-1)
  | succ j ih =>
      have hsq : InCircleBand (2 ^ j + 2 ^ j)
          (xFactor i j * xFactor i j) :=
        band_mul _ _ (2 ^ j) (2 ^ j) ih ih
      have hscaled : InCircleBand (0 + (2 ^ j + 2 ^ j))
          (C 2 * (xFactor i j * xFactor i j)) :=
        band_mul _ _ 0 (2 ^ j + 2 ^ j)
          (constant_in_band 2 0) hsq
      have htarget : 0 + (2 ^ j + 2 ^ j) = 2 ^ (j + 1) := by
        simp [pow_succ]
        omega
      simp only [xFactor]
      exact band_sub _ _ (2 ^ (j + 1))
        (by simpa [htarget] using hscaled)
        (by simpa using constant_in_band (1 : F) (2 ^ (j + 1)))

theorem nativeFactor_band (i : F) (j : Nat) :
    InCircleBand (factorRadius j) (nativeFactor i j) := by
  cases j with
  | zero => simpa [nativeFactor, factorRadius] using
      line_in_band_one i 0 0 1 0
  | succ j => simpa [nativeFactor, factorRadius] using xFactor_band i j

/-- Radius of a `2^k`-coefficient native circle word. -/
def coefficientRadius : Nat → Nat
  | 0 => 0
  | k + 1 => 2 ^ k

theorem radius_step (k : Nat) :
    coefficientRadius k + factorRadius k = coefficientRadius (k + 1) := by
  cases k with
  | zero => decide
  | succ k =>
      simp [coefficientRadius, factorRadius, pow_succ]
      omega

/-- Source-transcribed recursive coefficient evaluator in the Laurent
model. The list split and high-factor index match native
`evalAtPointRecursive`; arbitrary-length lists are padded/truncated by the
model's `headD`/`take`/`drop` behavior, so the exact native length check is
still an external precondition. -/
noncomputable def coefficientWord (i : F) : Nat → List F → CirclePoly F
  | 0, coefficients => C (coefficients.headD 0)
  | k + 1, coefficients =>
      coefficientWord i k (coefficients.take (2 ^ k)) +
        coefficientWord i k (coefficients.drop (2 ^ k)) * nativeFactor i k

/-- Every coefficient word in the native recursive basis has its claimed
two-sided Laurent radius. This covers arbitrary coefficient values at every
valid log length, conditional on the evaluator refinement. -/
theorem coefficientWord_band (i : F) (k : Nat) (coefficients : List F) :
    InCircleBand (coefficientRadius k)
      (coefficientWord i k coefficients) := by
  induction k generalizing coefficients with
  | zero =>
      simpa [coefficientWord, coefficientRadius] using
        constant_in_band (coefficients.headD 0) 0
  | succ k ih =>
      have hleft := ih (coefficients.take (2 ^ k))
      have hright := ih (coefficients.drop (2 ^ k))
      have hproduct := band_mul
        (coefficientWord i k (coefficients.drop (2 ^ k)))
        (nativeFactor i k)
        (coefficientRadius k) (factorRadius k)
        hright (nativeFactor_band i k)
      rw [coefficientWord]
      apply band_add
      · exact band_mono _ _ _ (by rw [← radius_step k]; omega) hleft
      · simpa only [radius_step k] using hproduct

/-- The three accepted sparse Gate source heights use trace coefficient logs
16/10/4 after blowup two. The full recursive basis proves the exact Laurent
radii assumed by the separate two-Q degree join for arbitrary coefficient
values, once a native column is refined to this evaluator. -/
theorem accepted_sparse_source_bands
    (i : F) (coefficients₁₇ coefficients₁₁ coefficients₅ : List F) :
    InCircleBand 32768 (coefficientWord i 16 coefficients₁₇) ∧
    InCircleBand 512 (coefficientWord i 10 coefficients₁₁) ∧
    InCircleBand 8 (coefficientWord i 4 coefficients₅) := by
  exact ⟨by simpa [coefficientRadius] using
      coefficientWord_band i 16 coefficients₁₇,
    by simpa [coefficientRadius] using
      coefficientWord_band i 10 coefficients₁₁,
    by simpa [coefficientRadius] using
      coefficientWord_band i 4 coefficients₅⟩

theorem accepted_sparse_radii_match_two_q :
    coefficientRadius 16 = SparseP05TwoQDegree.sourceRadius 17 ∧
    coefficientRadius 10 = SparseP05TwoQDegree.sourceRadius 11 ∧
    coefficientRadius 4 = SparseP05TwoQDegree.sourceRadius 5 := by
  decide

theorem accepted_height_recursive_radius (h : Nat)
    (hh : h ∈ SparseP05TwoQDegree.acceptedHeights) :
    coefficientRadius (h - 1) = SparseP05TwoQDegree.sourceRadius h := by
  simp only [SparseP05TwoQDegree.acceptedHeights,
    Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl <;> decide

/-- The field-value half-split recurrence transcribed from native
`evalAtPointRecursive`. The validity condition is `coefficients.length=2^k`;
the Lean definition is total to make the algebraic induction explicit. -/
def recursiveValue
    {E : Type*} [Field E] [Algebra F E]
    (x y : E) : Nat → List F → E
  | 0, coefficients => (algebraMap F E) (coefficients.headD 0)
  | k + 1, coefficients =>
      recursiveValue x y k (coefficients.take (2 ^ k)) +
        recursiveValue x y k (coefficients.drop (2 ^ k)) *
          nativeFactorValue x y k

theorem xFactor_eval_algebra
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i : F) (hi : i ^ 2 = -1) (z : Eˣ) (j : Nat) :
    eval₂ (algebraMap F E) z (xFactor i j) =
      xFactorValue (fourierX z.val z⁻¹.val) j := by
  induction j with
  | zero =>
      simpa [xFactor, xFactorValue] using eval_xLaurent_algebra i hi z
  | succ j ih =>
      change eval₂ (algebraMap F E) z
          (C 2 * (xFactor i j * xFactor i j) - 1) = _
      rw [(eval₂ (algebraMap F E) z).map_sub,
        (eval₂ (algebraMap F E) z).map_mul,
        (eval₂ (algebraMap F E) z).map_mul,
        (eval₂ (algebraMap F E) z).map_one,
        LaurentPolynomial.eval₂_C, ih]
      simp only [xFactorValue]
      rw [show (algebraMap F E) (2 : F) = (2 : E) by
        exact _root_.map_ofNat (algebraMap F E) 2]
      ring

theorem nativeFactor_eval_algebra
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i : F) (hi : i ^ 2 = -1) (z : Eˣ) (j : Nat) :
    eval₂ (algebraMap F E) z (nativeFactor i j) =
      nativeFactorValue
        (fourierX z.val z⁻¹.val)
        (fourierY ((algebraMap F E) i) z.val z⁻¹.val) j := by
  cases j with
  | zero =>
      simpa [nativeFactor, nativeFactorValue] using
        eval_yLaurent_algebra i hi z
  | succ j =>
      simpa [nativeFactor, nativeFactorValue] using
        xFactor_eval_algebra i hi z j

/-- All coefficient slots in the source-transcribed recursive evaluator
equal evaluation of one Laurent word, including secure-field OOD points.
This is a mathematical recurrence identity; the native carry implementation,
its input length check, and FFT coefficient origin still need refinement. -/
theorem coefficientWord_eval_algebra
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i : F) (hi : i ^ 2 = -1) (z : Eˣ)
    (k : Nat) (coefficients : List F) :
    eval₂ (algebraMap F E) z (coefficientWord i k coefficients) =
      recursiveValue (fourierX z.val z⁻¹.val)
        (fourierY ((algebraMap F E) i) z.val z⁻¹.val)
        k coefficients := by
  induction k generalizing coefficients with
  | zero =>
      simp [coefficientWord, recursiveValue]
  | succ k ih =>
      simp only [coefficientWord, recursiveValue, map_add, map_mul,
        ih, nativeFactor_eval_algebra i hi z k]

/-- A fully populated recursive source word plus two correct *projected*
recursive evaluations gives its two own quotient polynomials at the exact
accepted height bound. This composes all-coefficient source degree with the
two-Q quotient construction. Both claim certificates must name the source
height and imaginary unit used by that evaluator. The value equalities are
deliberately about the source-transcribed recursive evaluator; proving they equal the captured
native sampled values is the remaining selected-implementation refinement. -/
theorem accepted_recursive_word_two_q_own_quotients
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (h : Nat) (hh : h ∈ SparseP05TwoQDegree.acceptedHeights)
    (i : F) (hi : i ^ 2 = -1) (coefficients : List F)
    (c₀ c₁ : SparseP05TwoQDegree.ProjectedConjugateClaim F E)
    (hheight₀ : c₀.sourceHeight = h)
    (hheight₁ : c₁.sourceHeight = h)
    (_himag₀ : c₀.i = i)
    (_himag₁ : c₁.i = i)
    (hdistinct : c₀.z ≠ c₁.z)
    (hvalue₀ : recursiveValue
      (fourierX c₀.z.val c₀.z⁻¹.val)
      (fourierY ((algebraMap F E) i) c₀.z.val c₀.z⁻¹.val)
      (h - 1) coefficients =
        eval₂ (algebraMap F E) c₀.z c₀.interpolation)
    (hvalue₁ : recursiveValue
      (fourierX c₁.z.val c₁.z⁻¹.val)
      (fourierY ((algebraMap F E) i) c₁.z.val c₁.z⁻¹.val)
      (h - 1) coefficients =
        eval₂ (algebraMap F E) c₁.z c₁.interpolation) :
    ∃ q₀ q₁ : CirclePoly F,
      InCircleBand (SparseP05TwoQDegree.sourceRadius h - 1) q₀ ∧
      InCircleBand (SparseP05TwoQDegree.sourceRadius h - 1) q₁ ∧
      coefficientWord i (h - 1) coefficients = c₀.interpolation +
        nativeLineLaurent c₀.i c₀.x₀ c₀.y₀ c₀.x₁ c₀.y₁ * q₀ ∧
      coefficientWord i (h - 1) coefficients = c₁.interpolation +
        nativeLineLaurent c₁.i c₁.x₀ c₁.y₀ c₁.x₁ c₁.y₁ * q₁ := by
  have hf : InCircleBand (SparseP05TwoQDegree.sourceRadius h)
      (coefficientWord i (h - 1) coefficients) := by
    rw [← accepted_height_recursive_radius h hh]
    exact coefficientWord_band i (h - 1) coefficients
  have hclaim₀ : eval₂ (algebraMap F E) c₀.z
      (coefficientWord i (h - 1) coefficients) =
        eval₂ (algebraMap F E) c₀.z c₀.interpolation := by
    rw [coefficientWord_eval_algebra i hi c₀.z (h - 1) coefficients]
    exact hvalue₀
  have hclaim₁ : eval₂ (algebraMap F E) c₁.z
      (coefficientWord i (h - 1) coefficients) =
        eval₂ (algebraMap F E) c₁.z c₁.interpolation := by
    rw [coefficientWord_eval_algebra i hi c₁.z (h - 1) coefficients]
    exact hvalue₁
  exact SparseP05TwoQDegree.accepted_height_two_q_own_quotients_exist
    h hh (coefficientWord i (h - 1) coefficients) hf c₀ c₁
    hheight₀ hheight₁ hdistinct hclaim₀ hclaim₁

end S31.Gadgets.PcsFri.CircleRecursiveBasisDegree
