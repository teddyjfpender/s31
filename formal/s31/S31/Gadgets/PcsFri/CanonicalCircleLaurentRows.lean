import S31.Gadgets.PcsFri.NativeCircleQuotientRows
import S31.Gadgets.PcsFri.SparseCascadeQueries
import Mathlib.Tactic

/-!
An exact low-degree native circle evaluation block and canonical-domain row
index model. The finite coefficient block is the first four slots of native
`CircleCoefficients`: factors `y, x`, then the carry evaluator merges
`(c₀+c₁y) + x(c₂+c₃y)`. The domain model transcribes the native
`halfOdds`/conjugate-half and bit-reversal formulas for every log size.

This file does not prove the native FFT interpolation algorithm, native group
arithmetic, or authentication of the opened rows. Those joins remain explicit.
-/

namespace S31.Gadgets.PcsFri.CanonicalCircleLaurentRows

open LaurentPolynomial AddMonoidAlgebra
open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.NativeCircleQuotientRows
open S31.Gadgets.PcsFri.SparseCascadeQueries

variable {F : Type*} [Field F]

/-- The first native circle-basis factor `x` as a radius-one Laurent
polynomial. The existing `yLaurent` is the factor at slot zero. -/
noncomputable def xLaurent (i : F) : CirclePoly F :=
  nativeLineLaurent i 0 0 0 (-1)

theorem eval_xLaurent (i : F) (hi : i ^ 2 = -1) (t : Fˣ) :
    eval₂ (RingHom.id F) t (xLaurent i) = fourierX t.val t⁻¹.val := by
  rw [xLaurent, eval_nativeLineLaurent i 0 0 0 (-1) hi t]
  simp [CircleVanishingLine.nativeLine]

theorem eval_xLaurent_algebra
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i : F) (hi : i ^ 2 = -1) (z : Eˣ) :
    eval₂ (algebraMap F E) z (xLaurent i) =
      fourierX z.val z⁻¹.val := by
  rw [xLaurent, eval_nativeLine_algebra i 0 0 0 (-1) hi z]
  simp [CircleVanishingLine.nativeLine]

/-- Four coefficient slots of the native circle evaluator, in storage order.
The source evaluator uses factors `[y,x]` and a carry-style merge. -/
def nativeFourBlock (c₀ c₁ c₂ c₃ x y : F) : F :=
  (c₀ + c₁ * y) + (c₂ + c₃ * y) * x

noncomputable def fourBlockLaurent (i c₀ c₁ c₂ c₃ : F) : CirclePoly F :=
  C c₀ + C c₁ * yLaurent i +
    C c₂ * xLaurent i + C c₃ * (xLaurent i * yLaurent i)

/-- The exact first four native circle-basis coefficient slots evaluate as
the finite Laurent polynomial. This proves the basis change at degree four;
it does not take row equality as a premise. -/
theorem nativeFourBlock_eq_eval_laurent
    (i c₀ c₁ c₂ c₃ : F) (hi : i ^ 2 = -1) (t : Fˣ) :
    nativeFourBlock c₀ c₁ c₂ c₃
      (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val) =
      eval₂ (RingHom.id F) t (fourBlockLaurent i c₀ c₁ c₂ c₃) := by
  simp only [fourBlockLaurent, map_add, map_mul, LaurentPolynomial.eval₂_C,
    RingHom.id_apply, eval_yLaurent i hi t, eval_xLaurent i hi t]
  unfold nativeFourBlock
  ring

theorem nativeFourBlock_eq_eval_laurent_algebra
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (i c₀ c₁ c₂ c₃ : F) (hi : i ^ 2 = -1) (z : Eˣ) :
    nativeFourBlock ((algebraMap F E) c₀) ((algebraMap F E) c₁)
      ((algebraMap F E) c₂) ((algebraMap F E) c₃)
      (fourierX z.val z⁻¹.val)
      (fourierY ((algebraMap F E) i) z.val z⁻¹.val) =
      eval₂ (algebraMap F E) z (fourBlockLaurent i c₀ c₁ c₂ c₃) := by
  simp only [fourBlockLaurent, map_add, map_mul, LaurentPolynomial.eval₂_C,
    eval_xLaurent_algebra i hi z, eval_yLaurent_algebra i hi z]
  unfold nativeFourBlock
  ring

theorem fourBlock_in_band_two (i c₀ c₁ c₂ c₃ : F) :
    InCircleBand 2 (fourBlockLaurent i c₀ c₁ c₂ c₃) := by
  unfold fourBlockLaurent
  apply band_add
  · apply band_add
    · apply band_add
      · exact band_mono 1 2 _ (by omega) (constant_in_band_one _)
      · exact band_mono 1 2 _ (by omega)
          (scale_in_band_one _ _ (line_in_band_one i 0 0 1 0))
    · exact band_mono 1 2 _ (by omega)
        (scale_in_band_one _ _ (line_in_band_one i 0 0 0 (-1)))
  · apply band_mono 2 2 _ (by omega)
    have hproduct : InCircleBand 2 (xLaurent i * yLaurent i) :=
      line_mul_band i 0 0 0 (-1) 1 (yLaurent i)
        (line_in_band_one i 0 0 1 0)
    intro k hk
    have hne : (xLaurent i * yLaurent i) k ≠ 0 := by
      intro hz
      apply hk
      rw [← LaurentPolynomial.smul_eq_C_mul]
      simp [hz]
    exact hproduct k hne

/-- Native `@bitReverse(i) >> (wordBits-k)` for an in-range k-bit row,
written as the corresponding recurrence on low bits. -/
def bitReverse : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, row => 2 ^ k * (row % 2) + bitReverse k (row / 2)

theorem bitReverse_lt (k row : Nat) : bitReverse k row < 2 ^ k := by
  induction k generalizing row with
  | zero => simp [bitReverse]
  | succ k ih =>
    have h := ih (row / 2)
    have hmod : row % 2 = 0 ∨ row % 2 = 1 := by omega
    rcases hmod with hzero | hone
    · simp only [bitReverse, pow_succ, hzero, mul_zero, zero_add]
      omega
    · simp only [bitReverse, pow_succ, hone, mul_one]
      omega

theorem bitReverse_even (k row : Nat) :
    bitReverse (k + 1) (2 * row) = bitReverse k row := by
  simp [bitReverse]

theorem bitReverse_odd (k row : Nat) :
    bitReverse (k + 1) (2 * row + 1) = 2 ^ k + bitReverse k row := by
  have hmod : (2 * row + 1) % 2 = 1 := by omega
  have hdiv : (2 * row + 1) / 2 = row := by omega
  simp [bitReverse, hmod, hdiv]

abbrev CircleIndex := ZMod (2 ^ 31)

/-- Native `CirclePointIndex.subgroupGen(log_size)` at its valid sizes. -/
def subgroupGeneratorIndex (logSize : Nat) : CircleIndex :=
  ((2 ^ (31 - logSize) : Nat) : CircleIndex)

/-- Native `Coset.indexAt`: initial generator index plus the subgroup step. -/
def cosetIndex (initial : CircleIndex) (logSize natural : Nat) : CircleIndex :=
  initial + (natural : CircleIndex) * subgroupGeneratorIndex logSize

/-- The native construction is `Coset.halfOdds(k-1)`; it calls
`subgroupGen((k-1)+2)` for the initial index and `subgroupGen(k-1)` for the
step. -/
def halfOddsIndex (k natural : Nat) : CircleIndex :=
  cosetIndex (subgroupGeneratorIndex ((k - 1) + 2)) (k - 1) natural

/-- Native `halfOdds(k-1)` has initial generator exponent `2^(30-k)` and
step exponent `2^(32-k)` in the circle group of order `2^31`. -/
def canonicalHalfIndex (k natural : Nat) : CircleIndex :=
  ((2 ^ (30 - k) : Nat) : CircleIndex) +
    ((natural : CircleIndex) * ((2 ^ (32 - k) : Nat) : CircleIndex))

theorem halfOddsIndex_eq_canonical (k natural : Nat)
    (hk : 1 ≤ k) (hmax : k ≤ 30) :
    halfOddsIndex k natural = canonicalHalfIndex k natural := by
  have hinit : 31 - ((k - 1) + 2) = 30 - k := by omega
  have hstep : 31 - (k - 1) = 32 - k := by omega
  simp only [halfOddsIndex, cosetIndex, subgroupGeneratorIndex,
    canonicalHalfIndex, hinit, hstep]

/-- Native `CircleDomain.indexAt`: first half is `halfOdds`; second half is
the pointwise group inverse of the same half. -/
def canonicalNaturalIndex (k natural : Nat) : CircleIndex :=
  if natural < 2 ^ (k - 1) then canonicalHalfIndex k natural
  else -canonicalHalfIndex k (natural - 2 ^ (k - 1))

def canonicalStorageIndex (k row : Nat) : CircleIndex :=
  canonicalNaturalIndex k (bitReverse k row)

/-- Adjacent even/odd bit-reversed storage rows address the same half-coset
index with opposite circle-group sign, for every positive log size. -/
theorem canonical_storage_pair (k row : Nat) :
    canonicalStorageIndex (k + 1) (2 * row) =
      canonicalHalfIndex (k + 1) (bitReverse k row) ∧
    canonicalStorageIndex (k + 1) (2 * row + 1) =
      -canonicalHalfIndex (k + 1) (bitReverse k row) := by
  have hb := bitReverse_lt k row
  constructor
  · simp [canonicalStorageIndex, canonicalNaturalIndex,
      bitReverse_even, hb]
  · simp [canonicalStorageIndex, canonicalNaturalIndex,
      bitReverse_odd]

theorem canonical_sparse_pair_conjugate_indices
    (k raw height : Nat) :
    canonicalStorageIndex (k + 1)
      (pairBase raw height + 1) =
      -canonicalStorageIndex (k + 1) (pairBase raw height) := by
  unfold pairBase
  have h := canonical_storage_pair k (raw / 2 ^ (height + 1))
  simpa only [mul_comm, Nat.add_comm] using h.2.trans (congrArg Neg.neg h.1.symm)

theorem fourierX_inverse (t : Fˣ) :
    fourierX (t⁻¹).val ((t⁻¹)⁻¹).val =
      fourierX t.val t⁻¹.val := by
  simp [fourierX, add_comm]

theorem fourierY_inverse (i : F) (t : Fˣ) :
    fourierY i (t⁻¹).val ((t⁻¹)⁻¹).val =
      -fourierY i t.val t⁻¹.val := by
  simp [fourierY]
  ring

/-- A source-transcribed row evaluator: native four-slot coefficient order,
native bit-reversed canonical-domain index, and Fourier coordinates. The
actual M31 circle generator's index-to-point implementation is a separate
refinement premise. -/
def fourBlockAtStorage (i c₀ c₁ c₂ c₃ : F)
    (coordinate : CircleIndex → Fˣ) (k row : Nat) : F :=
  let t := coordinate (canonicalStorageIndex k row)
  nativeFourBlock c₀ c₁ c₂ c₃
    (fourierX t.val t⁻¹.val) (fourierY i t.val t⁻¹.val)

/-- For the native sparse pair, one four-slot coefficient vector yields
conjugate row evaluations. The only geometry premise is the circle-generator
law `coordinate(-index)=coordinate(index)⁻¹`; no row-value equalities are
assumed. -/
theorem four_block_sparse_pair_conjugate
    (i c₀ c₁ c₂ c₃ : F)
    (coordinate : CircleIndex → Fˣ)
    (hneg : ∀ j, coordinate (-j) = (coordinate j)⁻¹)
    (k raw height : Nat) :
    let t := coordinate (canonicalStorageIndex (k + 1)
      (pairBase raw height))
    fourBlockAtStorage i c₀ c₁ c₂ c₃ coordinate (k + 1)
      (pairBase raw height + 1) =
      nativeFourBlock c₀ c₁ c₂ c₃
        (fourierX t.val t⁻¹.val)
        (-fourierY i t.val t⁻¹.val) := by
  dsimp [fourBlockAtStorage]
  rw [canonical_sparse_pair_conjugate_indices k raw height,
    hneg, fourierX_inverse, fourierY_inverse]

/-- Concrete CAS05 own-quotient existence for the first four native circle
coefficient slots. The native OOD claim expression replaces a polynomial
evaluation premise, and `fourBlock_in_band_two` discharges source degree. -/
theorem four_block_native_claim_constructs_own_quotient
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (z : Eˣ) (d i x₀ y₀ x₁ y₁ v₀ v₁ c₀ c₁ c₂ c₃ : F)
    (hi : i ^ 2 = -1)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hminpoly : (minpoly F z.val).Monic)
    (hdegree : (minpoly F z.val).natDegree = 2)
    (u : E)
    (hsampledX : fourierX z.val z⁻¹.val =
      (algebraMap F E) x₀ + u * (algebraMap F E) x₁)
    (hsampledY : fourierY ((algebraMap F E) i) z.val z⁻¹.val =
      (algebraMap F E) y₀ + u * (algebraMap F E) y₁)
    (hnativeClaim : nativeFourBlock
      ((algebraMap F E) c₀) ((algebraMap F E) c₁)
      ((algebraMap F E) c₂) ((algebraMap F E) c₃)
      (fourierX z.val z⁻¹.val)
      (fourierY ((algebraMap F E) i) z.val z⁻¹.val) =
        (algebraMap F E) v₀ + u * (algebraMap F E) v₁) :
    ∃ q : CirclePoly F,
      InCircleBand 1 q ∧
      fourBlockLaurent i c₀ c₁ c₂ c₃ =
        interpolationLaurent i v₀ v₁ y₀ y₁ +
          nativeLineLaurent i x₀ y₀ x₁ y₁ * q := by
  have hclaim : eval₂ (algebraMap F E) z
      (fourBlockLaurent i c₀ c₁ c₂ c₃) =
      (algebraMap F E) v₀ + u * (algebraMap F E) v₁ := by
    rwa [nativeFourBlock_eq_eval_laurent_algebra i c₀ c₁ c₂ c₃ hi z] at hnativeClaim
  exact native_claim_constructs_circle_quotient z 2 (by omega)
    d i x₀ y₀ x₁ y₁ v₀ v₁ hi h₀ h₁ hy hminpoly hdegree
    u hsampledX hsampledY (fourBlockLaurent i c₀ c₁ c₂ c₃)
    (fourBlock_in_band_two i c₀ c₁ c₂ c₃) hclaim

end S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
