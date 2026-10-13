import Mathlib.Tactic

/-!
The experimental multi-height FRI kernel uses the native inverse butterfly
`a+b+alpha*(a-b)/u`; the displayed S-two circle/line FFT butterfly uses half
that value. An insertion of a new height prevents one global rescaling from
identifying the two cascades. This module states the exact local change of
variables: after `i` native folds, divide the carried layer by `2^i` and
divide the newly inserted height-`i` batch by `2^(i-1)`.

This is field algebra only. It does not identify the Zig twiddle schedule,
prove a proximity reduction, or authenticate the scaled oracle ensemble.
-/

namespace S31.Gadgets.PcsFri.FriCascadeNormalization

variable {F : Type*} [Field F] [NeZero (2 : F)]

def nativePair (a b u alpha : F) : F :=
  a + b + alpha * (a - b) * u⁻¹

def paperPair (a b u alpha : F) : F :=
  nativePair a b u alpha / 2

def nativeInsert (previousEven previousOdd insertedEven insertedOdd
    lineX circleY alpha : F) : F :=
  nativePair previousEven previousOdd lineX alpha +
    alpha ^ 2 * nativePair insertedEven insertedOdd circleY alpha

def paperInsert (previousEven previousOdd insertedEven insertedOdd
    lineX circleY alpha : F) : F :=
  paperPair previousEven previousOdd lineX alpha +
    alpha ^ 2 * paperPair insertedEven insertedOdd circleY alpha

theorem nativePair_eq_twice_paper (a b u alpha : F) :
    nativePair a b u alpha = 2 * paperPair a b u alpha := by
  simp only [paperPair]
  field_simp [NeZero.ne (2 : F)]

omit [NeZero (2 : F)] in
theorem nativePair_scale (scale a b u alpha : F) :
    nativePair (scale * a) (scale * b) u alpha =
      scale * nativePair a b u alpha := by
  simp only [nativePair]
  ring

omit [NeZero (2 : F)] in
theorem paperPair_scale (scale a b u alpha : F) :
    paperPair (scale * a) (scale * b) u alpha =
      scale * paperPair a b u alpha := by
  simp only [paperPair, nativePair_scale]
  ring

/-- A scaled previous layer and an unscaled new height do not acquire the
same factor. The two terms have coefficients `2*scale` and `2`. -/
theorem nativeInsert_two_scales (scale previousEven previousOdd insertedEven
    insertedOdd lineX circleY alpha : F) :
    nativeInsert (scale * previousEven) (scale * previousOdd)
      insertedEven insertedOdd lineX circleY alpha =
      (2 * scale) * paperPair previousEven previousOdd lineX alpha +
        2 * alpha ^ 2 * paperPair insertedEven insertedOdd circleY alpha := by
  rw [nativeInsert, nativePair_scale, nativePair_eq_twice_paper,
    nativePair_eq_twice_paper]
  ring

/-- Exact local refinement into the normalized paper insertion. At height
`i`, choose `scale=2^i`; the newly inserted batch must be rescaled by
`scale⁻¹` in the paper relation. -/
theorem nativeInsert_scaled_paper (scale previousEven previousOdd insertedEven
    insertedOdd lineX circleY alpha : F) (hscale : scale ≠ 0) :
    nativeInsert (scale * previousEven) (scale * previousOdd)
      insertedEven insertedOdd lineX circleY alpha =
      (2 * scale) * paperInsert previousEven previousOdd
        (scale⁻¹ * insertedEven) (scale⁻¹ * insertedOdd)
        lineX circleY alpha := by
  rw [nativeInsert_two_scales]
  simp only [paperInsert, paperPair_scale]
  field_simp [hscale]

theorem nativeInsert_pow_two (i : Nat) (previousEven previousOdd insertedEven
    insertedOdd lineX circleY alpha : F) :
    nativeInsert ((2 : F) ^ i * previousEven) ((2 : F) ^ i * previousOdd)
      insertedEven insertedOdd lineX circleY alpha =
      (2 : F) ^ (i + 1) * paperInsert previousEven previousOdd
        (((2 : F) ^ i)⁻¹ * insertedEven)
        (((2 : F) ^ i)⁻¹ * insertedOdd) lineX circleY alpha := by
  calc
    nativeInsert ((2 : F) ^ i * previousEven) ((2 : F) ^ i * previousOdd)
        insertedEven insertedOdd lineX circleY alpha =
        (2 * (2 : F) ^ i) * paperInsert previousEven previousOdd
          (((2 : F) ^ i)⁻¹ * insertedEven)
          (((2 : F) ^ i)⁻¹ * insertedOdd) lineX circleY alpha :=
      nativeInsert_scaled_paper ((2 : F) ^ i) previousEven previousOdd
        insertedEven insertedOdd lineX circleY alpha
        (pow_ne_zero i (NeZero.ne (2 : F)))
    _ = (2 : F) ^ (i + 1) * paperInsert previousEven previousOdd
          (((2 : F) ^ i)⁻¹ * insertedEven)
          (((2 : F) ^ i)⁻¹ * insertedOdd) lineX circleY alpha := by
      rw [pow_succ]
      ring

/-- Already at the second fold, multiplying the unscaled paper insertion by
four gives a different result. The height-dependent rescaling is necessary. -/
theorem unscaled_second_insertion_counterexample :
    nativeInsert (0 : ℚ) 0 1 0 1 1 1 ≠
      4 * paperInsert (0 : ℚ) 0 1 0 1 1 1 := by
  norm_num [nativeInsert, paperInsert, nativePair, paperPair]

end S31.Gadgets.PcsFri.FriCascadeNormalization
