import S31.Gadgets.PcsFri.Cas07SparseP05Join
import S31.Gadgets.PcsFri.CircleLaurentQuotient
import Mathlib.Tactic

/-!
The algebraic join needed by a *separate-instance* two-Q degree-corrected
opening. Two bounded original polynomials that agree with the same source
oracle on sufficiently overlapping rows must be one polynomial. Each
conjugate two-point own quotient can then force its own projected OOD claim.

The agreement sets, degree bounds, line roots, and source ownership are
premises. Neither the native verifier nor the published single-Q Protocol 4
currently supplies their two-instance correlated-agreement/BCS reduction.
-/

namespace S31.Gadgets.PcsFri.SparseP05TwoQDegree

open LaurentPolynomial
open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.CircleLaurentUniqueness
open S31.Gadgets.PcsFri.Cas07SparseP05Join
open S31.Gadgets.PcsFri.CircleLaurentQuotient

variable {F : Type*} [Field F]

/-- Conditional Laurent radius for a source column of *extended* log height
`h` and blowup two. It is half the native `2^(h-1)` coefficient count. The
full native coefficient-to-Laurent band refinement remains to be proved. -/
def sourceRadius (h : Nat) : Nat := 2 ^ (h - 2)

def acceptedHeights : Finset Nat := {5, 11, 17}

theorem accepted_height_radii :
    sourceRadius 17 = 32768 ∧ sourceRadius 11 = 512 ∧
      sourceRadius 5 = 8 := by
  decide

/-- Full source domains have numerical room for the strict Laurent
uniqueness threshold. This does not derive any agreement set from FRI. -/
theorem accepted_height_agreement_thresholds :
    (2 * sourceRadius 17 = 65536 ∧ 65536 < 2 ^ (17 : Nat)) ∧
    (2 * sourceRadius 11 = 1024 ∧ 1024 < 2 ^ (11 : Nat)) ∧
    (2 * sourceRadius 5 = 16 ∧ 16 < 2 ^ (5 : Nat)) := by
  decide

theorem accepted_height_radius_positive (h : Nat)
    (hh : h ∈ acceptedHeights) : 1 ≤ sourceRadius h := by
  simp only [acceptedHeights, Finset.mem_insert, Finset.mem_singleton] at hh
  rcases hh with rfl | rfl | rfl <;> decide

/-- The native `repeatedDoubleOnCircleQM31` loop body, in field notation. -/
def circleDouble {E : Type*} [Field E] (p : E × E) : E × E :=
  (2 * p.1 ^ 2 - 1, 2 * p.1 * p.2)

def projectedPoint {E : Type*} [Field E] (h : Nat)
    (raw : E × E) : E × E :=
  (circleDouble^[17 - h]) raw

theorem accepted_projection_counts :
    17 - 17 = 0 ∧ 17 - 11 = 6 ∧ 17 - 5 = 12 := by
  decide

theorem circleDouble_stays_on_circle
    {E : Type*} [Field E] (p : E × E)
    (hc : p.1 ^ 2 + p.2 ^ 2 = 1) :
    (circleDouble p).1 ^ 2 + (circleDouble p).2 ^ 2 = 1 := by
  dsimp [circleDouble]
  calc
    ((2 : E) * p.1 ^ 2 - 1) ^ 2 + (2 * p.1 * p.2) ^ 2 =
        1 + 4 * p.1 ^ 2 * (p.1 ^ 2 + p.2 ^ 2 - 1) := by ring
    _ = 1 := by rw [hc]; ring

theorem projectedPoint_stays_on_circle
    {E : Type*} [Field E] (raw : E × E)
    (hc : raw.1 ^ 2 + raw.2 ^ 2 = 1) (folds : Nat) :
    ((circleDouble^[folds]) raw).1 ^ 2 +
      ((circleDouble^[folds]) raw).2 ^ 2 = 1 := by
  induction folds with
  | zero => simpa using hc
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact circleDouble_stays_on_circle _ ih

/-- One native doubling squares the Fourier parameter of a circle point. -/
theorem circleDouble_fourier_square
    {E : Type*} [Field E] (i : E) (hi : i ^ 2 = -1)
    (p : E × E) (hc : p.1 ^ 2 + p.2 ^ 2 = 1) :
    (circleDouble p).1 + i * (circleDouble p).2 =
      (p.1 + i * p.2) ^ 2 := by
  dsimp [circleDouble]
  calc
    (2 : E) * p.1 ^ 2 - 1 + i * (2 * p.1 * p.2) =
        p.1 ^ 2 - p.2 ^ 2 + 2 * i * p.1 * p.2 := by
      linear_combination hc
    _ = (p.1 + i * p.2) ^ 2 := by
      calc
        p.1 ^ 2 - p.2 ^ 2 + 2 * i * p.1 * p.2 =
            p.1 ^ 2 + 2 * i * p.1 * p.2 + i ^ 2 * p.2 ^ 2 := by
          rw [hi]
          ring
        _ = (p.1 + i * p.2) ^ 2 := by ring

/-- This is the algebraic point-normalization law for all accepted source
heights. It does not yet identify the native QM31 coefficient evaluator with
the formal Laurent evaluation at this Fourier coordinate. -/
theorem projected_fourier_power
    {E : Type*} [Field E] (i : E) (hi : i ^ 2 = -1)
    (raw : E × E) (hc : raw.1 ^ 2 + raw.2 ^ 2 = 1)
    (folds : Nat) :
    ((circleDouble^[folds]) raw).1 +
      i * ((circleDouble^[folds]) raw).2 =
        (raw.1 + i * raw.2) ^ (2 ^ folds) := by
  induction folds with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply',
        circleDouble_fourier_square i hi _
          (projectedPoint_stays_on_circle raw hc k), ih]
      calc
        ((raw.1 + i * raw.2) ^ (2 ^ k)) ^ 2 =
            (raw.1 + i * raw.2) ^ ((2 ^ k) * 2) := by
          rw [pow_mul]
        _ = (raw.1 + i * raw.2) ^ (2 ^ (k + 1)) := by
          rw [pow_succ]

/-- Geometric and algebraic certificates for one *projected, source-height*
conjugate OOD point. In native terms the point is `Q_h=[2^(17-h)]Q_top`.
The structure deliberately requires its own nondegenerate line and
degree-two Fourier certificate; a guard at raw `Q_top` cannot be substituted.
The value claim against the source polynomial is supplied separately. -/
structure ProjectedConjugateClaim
    (F E : Type*) [Field F] [Field E] [Algebra F E] where
  z : Eˣ
  rawPoint : E × E
  sourceHeight : Nat
  hheight : sourceHeight ∈ acceptedHeights
  d : F
  i : F
  x₀ : F
  y₀ : F
  x₁ : F
  y₁ : F
  interpolation : CirclePoly F
  hi : i ^ 2 = -1
  hrawCircle : rawPoint.1 ^ 2 + rawPoint.2 ^ 2 = 1
  hprojected : z.val = (projectedPoint sourceHeight rawPoint).1 +
    (algebraMap F E) i * (projectedPoint sourceHeight rawPoint).2
  hcircle₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1
  hcircle₁ : x₀ * x₁ + y₀ * y₁ = 0
  hy : y₁ ≠ 0
  hminpoly : (minpoly F z.val).Monic
  hdegree : (minpoly F z.val).natDegree = 2
  hlineRoot : eval₂ (algebraMap F E) z
    (nativeLineLaurent i x₀ y₀ x₁ y₁) = 0
  hinterpolation : InCircleBand 1 interpolation

/-- A claim certificate's Fourier parameter is the raw point's parameter
raised by exactly the native source-height normalization exponent. -/
theorem ProjectedConjugateClaim.z_eq_projected_power
    {E : Type*} [Field E] [Algebra F E]
    (c : ProjectedConjugateClaim F E) :
    c.z.val = (c.rawPoint.1 +
      (algebraMap F E) c.i * c.rawPoint.2) ^
        (2 ^ (17 - c.sourceHeight)) := by
  have hiE : ((algebraMap F E) c.i) ^ 2 = -1 := by
    rw [← map_pow, c.hi, map_neg, map_one]
  rw [c.hprojected]
  exact projected_fourier_power ((algebraMap F E) c.i) hiE
    c.rawPoint c.hrawCircle (17 - c.sourceHeight)

/-- A correct claim at each of two distinct source-height OOD points gives
two *separate* own quotients of the same bounded original. Each quotient is
one Laurent radius lower, and the reconstructions agree coefficientwise.
The `n` bound is later instantiated as `sourceRadius h` for h=17/11/5.
This is a coefficient theorem, not a claim that native FRI has tested the
three required whole oracles. -/
theorem two_distinct_q_own_quotients_exist
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (n : Nat) (hn : 1 ≤ n) (f : CirclePoly F)
    (hf : InCircleBand n f)
    (c₀ c₁ : ProjectedConjugateClaim F E)
    (_hdistinct : c₀.z ≠ c₁.z)
    (hclaim₀ : eval₂ (algebraMap F E) c₀.z f =
      eval₂ (algebraMap F E) c₀.z c₀.interpolation)
    (hclaim₁ : eval₂ (algebraMap F E) c₁.z f =
      eval₂ (algebraMap F E) c₁.z c₁.interpolation) :
    ∃ q₀ q₁ : CirclePoly F,
      InCircleBand (n - 1) q₀ ∧ InCircleBand (n - 1) q₁ ∧
      f = c₀.interpolation +
        nativeLineLaurent c₀.i c₀.x₀ c₀.y₀ c₀.x₁ c₀.y₁ * q₀ ∧
      f = c₁.interpolation +
        nativeLineLaurent c₁.i c₁.x₀ c₁.y₀ c₁.x₁ c₁.y₁ * q₁ ∧
      c₀.interpolation +
        nativeLineLaurent c₀.i c₀.x₀ c₀.y₀ c₀.x₁ c₀.y₁ * q₀ =
      c₁.interpolation +
        nativeLineLaurent c₁.i c₁.x₀ c₁.y₀ c₁.x₁ c₁.y₁ * q₁ := by
  obtain ⟨q₀, hq₀, hrel₀⟩ := native_circle_quotient_exists
    c₀.z n hn c₀.d c₀.i c₀.x₀ c₀.y₀ c₀.x₁ c₀.y₁
    c₀.hi c₀.hcircle₀ c₀.hcircle₁ c₀.hy c₀.hminpoly
    c₀.hdegree c₀.hlineRoot f c₀.interpolation hf
    c₀.hinterpolation hclaim₀
  obtain ⟨q₁, hq₁, hrel₁⟩ := native_circle_quotient_exists
    c₁.z n hn c₁.d c₁.i c₁.x₀ c₁.y₀ c₁.x₁ c₁.y₁
    c₁.hi c₁.hcircle₀ c₁.hcircle₁ c₁.hy c₁.hminpoly
    c₁.hdegree c₁.hlineRoot f c₁.interpolation hf
    c₁.hinterpolation hclaim₁
  exact ⟨q₀, q₁, hq₀, hq₁, hrel₀, hrel₁, hrel₀.symm.trans hrel₁⟩

/-- Apply the two-Q construction at exactly one of the three accepted source
heights, requiring both claim certificates to name that source height. The
quotient bound is `32767`, `511`, or `7`, respectively. The
source `InCircleBand` premise still needs full native coefficient refinement. -/
theorem accepted_height_two_q_own_quotients_exist
    [NeZero (2 : F)]
    {E : Type*} [Field E] [Algebra F E]
    (h : Nat) (hh : h ∈ acceptedHeights)
    (f : CirclePoly F) (hf : InCircleBand (sourceRadius h) f)
    (c₀ c₁ : ProjectedConjugateClaim F E)
    (_hheight₀ : c₀.sourceHeight = h)
    (_hheight₁ : c₁.sourceHeight = h)
    (hdistinct : c₀.z ≠ c₁.z)
    (hclaim₀ : eval₂ (algebraMap F E) c₀.z f =
      eval₂ (algebraMap F E) c₀.z c₀.interpolation)
    (hclaim₁ : eval₂ (algebraMap F E) c₁.z f =
      eval₂ (algebraMap F E) c₁.z c₁.interpolation) :
    ∃ q₀ q₁ : CirclePoly F,
      InCircleBand (sourceRadius h - 1) q₀ ∧
      InCircleBand (sourceRadius h - 1) q₁ ∧
      f = c₀.interpolation +
        nativeLineLaurent c₀.i c₀.x₀ c₀.y₀ c₀.x₁ c₀.y₁ * q₀ ∧
      f = c₁.interpolation +
        nativeLineLaurent c₁.i c₁.x₀ c₁.y₀ c₁.x₁ c₁.y₁ * q₁ := by
  obtain ⟨q₀, q₁, hq₀, hq₁, hrel₀, hrel₁, _⟩ :=
    two_distinct_q_own_quotients_exist (sourceRadius h)
      (accepted_height_radius_positive h hh) f hf c₀ c₁
      hdistinct hclaim₀ hclaim₁
  exact ⟨q₀, q₁, hq₀, hq₁, hrel₀, hrel₁⟩

/-- If two candidate originals each agree with one verifier-owned source
oracle, the overlap criterion forces the same *whole* Laurent polynomial.
This supplies the algebraic source-binding requirement for two independent
single-Q tests; it does not extract the required sets from their proofs. -/
theorem same_source_large_overlap_forces_one_original
    [DecidableEq F]
    (n : Nat) (source : Fˣ → F)
    (f₀ f₁ : CirclePoly F) (hf₀ : InCircleBand n f₀)
    (hf₁ : InCircleBand n f₁)
    (domain rows₀ rows₁ : Finset Fˣ)
    (hrows₀ : rows₀ ⊆ domain) (hrows₁ : rows₁ ⊆ domain)
    (hoverlap : domain.card + 2 * n < rows₀.card + rows₁.card)
    (hsource₀ : ∀ t ∈ rows₀, eval₂ (RingHom.id F) t f₀ = source t)
    (hsource₁ : ∀ t ∈ rows₁, eval₂ (RingHom.id F) t f₁ = source t) :
    f₀ = f₁ := by
  have hmany := intersection_large_enough domain rows₀ rows₁ n
    hrows₀ hrows₁ hoverlap
  apply band_eq_of_agreement f₀ f₁ n hf₀ hf₁
    (rows₀ ∩ rows₁) hmany
  intro t ht
  obtain ⟨ht₀, ht₁⟩ := Finset.mem_inter.mp ht
  rw [hsource₀ t ht₀, hsource₁ t ht₁]

/-- Two *distinct* projected OOD points can be handled algebraically by
separate point-specific own quotients, provided both tests are bound to the
same source rows and each has a sufficiently large joint original/quotient
agreement set. `z₀ ≠ z₁` names the multi-Q case; the algebra also works if
the points coincide. The outputs state both claims about one polynomial. -/
theorem two_distinct_q_claims_of_shared_source
    [DecidableEq F]
    {E : Type*} [Field E] [Algebra F E]
    (z₀ z₁ : Eˣ) (_hdistinct : z₀ ≠ z₁)
    (n : Nat) (hn : 1 ≤ n)
    (source own₀ own₁ : Fˣ → F)
    (f₀ f₁ interpolation₀ interpolation₁ q₀ q₁ : CirclePoly F)
    (hf₀ : InCircleBand n f₀) (hf₁ : InCircleBand n f₁)
    (hinterpolation₀ : InCircleBand 1 interpolation₀)
    (hinterpolation₁ : InCircleBand 1 interpolation₁)
    (hq₀ : InCircleBand (n - 1) q₀)
    (hq₁ : InCircleBand (n - 1) q₁)
    (domain originalRows₀ originalRows₁ jointRows₀ jointRows₁ : Finset Fˣ)
    (horiginal₀ : originalRows₀ ⊆ domain)
    (horiginal₁ : originalRows₁ ⊆ domain)
    (hjoint₀ : jointRows₀ ⊆ originalRows₀)
    (hjoint₁ : jointRows₁ ⊆ originalRows₁)
    (hoverlap : domain.card + 2 * n <
      originalRows₀.card + originalRows₁.card)
    (hmany₀ : 2 * n < jointRows₀.card)
    (hmany₁ : 2 * n < jointRows₁.card)
    (hsource₀ : ∀ t ∈ originalRows₀,
      eval₂ (RingHom.id F) t f₀ = source t)
    (hsource₁ : ∀ t ∈ originalRows₁,
      eval₂ (RingHom.id F) t f₁ = source t)
    (i₀ x₀₀ y₀₀ x₀₁ y₀₁ i₁ x₁₀ y₁₀ x₁₁ y₁₁ : F)
    (hi₀ : i₀ ^ 2 = -1) (hi₁ : i₁ ^ 2 = -1)
    (hden₀ : ∀ t ∈ jointRows₀,
      CircleVanishingLine.nativeLine x₀₀ y₀₀ x₀₁ y₀₁
        (fourierX t.val t⁻¹.val) (fourierY i₀ t.val t⁻¹.val) ≠ 0)
    (hden₁ : ∀ t ∈ jointRows₁,
      CircleVanishingLine.nativeLine x₁₀ y₁₀ x₁₁ y₁₁
        (fourierX t.val t⁻¹.val) (fourierY i₁ t.val t⁻¹.val) ≠ 0)
    (hown₀ : ∀ t ∈ jointRows₀,
      own₀ t = (source t - eval₂ (RingHom.id F) t interpolation₀) /
        CircleVanishingLine.nativeLine x₀₀ y₀₀ x₀₁ y₀₁
          (fourierX t.val t⁻¹.val) (fourierY i₀ t.val t⁻¹.val))
    (hown₁ : ∀ t ∈ jointRows₁,
      own₁ t = (source t - eval₂ (RingHom.id F) t interpolation₁) /
        CircleVanishingLine.nativeLine x₁₀ y₁₀ x₁₁ y₁₁
          (fourierX t.val t⁻¹.val) (fourierY i₁ t.val t⁻¹.val))
    (hquot₀ : ∀ t ∈ jointRows₀,
      eval₂ (RingHom.id F) t q₀ = own₀ t)
    (hquot₁ : ∀ t ∈ jointRows₁,
      eval₂ (RingHom.id F) t q₁ = own₁ t)
    (hroot₀ : eval₂ (algebraMap F E) z₀
      (nativeLineLaurent i₀ x₀₀ y₀₀ x₀₁ y₀₁) = 0)
    (hroot₁ : eval₂ (algebraMap F E) z₁
      (nativeLineLaurent i₁ x₁₀ y₁₀ x₁₁ y₁₁) = 0) :
    f₀ = f₁ ∧
      f₀ = interpolation₀ + nativeLineLaurent i₀ x₀₀ y₀₀ x₀₁ y₀₁ * q₀ ∧
      f₀ = interpolation₁ + nativeLineLaurent i₁ x₁₀ y₁₀ x₁₁ y₁₁ * q₁ ∧
      eval₂ (algebraMap F E) z₀ f₀ =
        eval₂ (algebraMap F E) z₀ interpolation₀ ∧
      eval₂ (algebraMap F E) z₁ f₀ =
        eval₂ (algebraMap F E) z₁ interpolation₁ := by
  have heq := same_source_large_overlap_forces_one_original n source f₀ f₁
    hf₀ hf₁ domain originalRows₀ originalRows₁ horiginal₀
    horiginal₁ hoverlap hsource₀ hsource₁
  have hsourceJoint₀ : ∀ t ∈ jointRows₀,
      eval₂ (RingHom.id F) t f₀ = source t := by
    intro t ht
    exact hsource₀ t (hjoint₀ ht)
  have hsourceJoint₁ : ∀ t ∈ jointRows₁,
      eval₂ (RingHom.id F) t f₁ = source t := by
    intro t ht
    exact hsource₁ t (hjoint₁ ht)
  have hrel₀ := two_point_joint_agreement_forces_relation
    i₀ x₀₀ y₀₀ x₀₁ y₀₁ hi₀ n hn f₀ q₀ interpolation₀
    hf₀ hinterpolation₀ hq₀ source own₀ jointRows₀
    hmany₀ hden₀ hsourceJoint₀ hown₀ hquot₀
  have hrel₁ := two_point_joint_agreement_forces_relation
    i₁ x₁₀ y₁₀ x₁₁ y₁₁ hi₁ n hn f₁ q₁ interpolation₁
    hf₁ hinterpolation₁ hq₁ source own₁ jointRows₁
    hmany₁ hden₁ hsourceJoint₁ hown₁ hquot₁
  refine ⟨heq, hrel₀, ?_, ?_, ?_⟩
  · exact heq.trans hrel₁
  · rw [hrel₀, map_add, map_mul, hroot₀, zero_mul, add_zero]
  · rw [heq, hrel₁, map_add, map_mul, hroot₁, zero_mul, add_zero]

end S31.Gadgets.PcsFri.SparseP05TwoQDegree
