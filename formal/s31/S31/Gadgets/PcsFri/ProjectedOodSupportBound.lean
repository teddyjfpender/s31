import S31.Gadgets.PcsFri.OodGuardFieldCount
import S31.Gadgets.PcsFri.CirclePowerEncoding
import Mathlib.Tactic

/-!
A conservative counting interface for the sparse Gate roster's projected OOD
guards. The raw successful circle image and the full circle are counted in
`OodGuardFieldCount` and `ConcreteCircleCount`. This file makes a separate,
explicit per-claim fiber bound an input; it does not assert that input for
the native doubling/shift map or model transcript randomness.
-/

namespace S31.Gadgets.PcsFri.ProjectedOodSupportBound

open ConcreteCircleCount CirclePowerEncoding

def q : ℕ := 2 ^ 31 - 1
def lowerSize : ℕ := q ^ 2
def rawSupport : ℕ := (lowerSize - 1) ^ 2
def zeroUpperYTargets : ℕ := 2 * (lowerSize - 1)

/-- There are four shifted h17 claims, 32 h11 claims, and 23 h5 claims in
the accepted sparse Gate roster. The bounds 1, 2⁶, and 2¹² are fiber caps
for their modeled maps; proving them for the native maps is separate. This
sum deliberately counts repeated claims. -/
def projectedExclusionBudget : ℕ :=
  (4 + 32 * 2 ^ 6 + 23 * 2 ^ 12) * zeroUpperYTargets

/-- Every nonzero-degree power equation over a field has at most its degree
many solutions. This is the algebraic fiber lemma needed after exhibiting
an injective `x+i*y` encoding of native circle points. -/
theorem power_equation_fiber_le {K : Type*} [Field K] [Fintype K]
    [DecidableEq K] (n : ℕ) (hn : 0 < n) (a : K) :
    ((Finset.univ : Finset K).filter (fun z => z ^ n = a)).card ≤ n := by
  let p : Polynomial K := Polynomial.X ^ n - Polynomial.C a
  have hp : p ≠ 0 := by
    dsimp [p]
    exact Polynomial.X_pow_sub_C_ne_zero hn a
  have hsub : ((Finset.univ : Finset K).filter (fun z => z ^ n = a)) ⊆
      p.roots.toFinset := by
    intro z hz
    have hz' : z ^ n = a := (Finset.mem_filter.mp hz).2
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots hp).mpr
    simp [Polynomial.IsRoot, p, hz']
  calc
    ((Finset.univ : Finset K).filter (fun z => z ^ n = a)).card ≤
        p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ p.roots.card := Multiset.toFinset_card_le _
    _ ≤ n := by simpa [p] using Polynomial.card_roots_X_pow_sub_C hn a

/-- Once native circle doubling is represented as powering under an
injective field encoding, every projected point has at most `n` source
points. The encoding and power law remain explicit hypotheses. -/
theorem encoded_projection_fiber_le {U K : Type*}
    [Fintype U] [DecidableEq U] [Field K] [Fintype K] [DecidableEq K]
    (encode : U → K) (henc : Function.Injective encode)
    (project : U → U) (n : ℕ) (hn : 0 < n)
    (hpower : ∀ u, encode (project u) = (encode u) ^ n)
    (target : U) :
    ((Finset.univ : Finset U).filter (fun u => project u = target)).card ≤ n := by
  let sources := (Finset.univ : Finset U).filter (fun u => project u = target)
  let roots := (Finset.univ : Finset K).filter
    (fun z => z ^ n = encode target)
  have himage : sources.image encode ⊆ roots := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    have hup : project u = target := (Finset.mem_filter.mp hu).2
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa [hup] using (hpower u).symm⟩
  calc
    sources.card = (sources.image encode).card :=
      (Finset.card_image_of_injective sources henc).symm
    _ ≤ roots.card := Finset.card_le_card himage
    _ ≤ n := power_equation_fiber_le n hn (encode target)

/-- The elementary preimage count needed for one projected line guard.
`bad` is the target-height set with conjugate-fixed `y`. -/
theorem encoded_projection_bad_le {U K : Type*}
    [Fintype U] [DecidableEq U] [Field K] [Fintype K] [DecidableEq K]
    (encode : U → K) (henc : Function.Injective encode)
    (project : U → U) (n : ℕ) (hn : 0 < n)
    (hpower : ∀ u, encode (project u) = (encode u) ^ n)
    (bad : Finset U) :
    ((Finset.univ : Finset U).filter (fun u => project u ∈ bad)).card ≤
      n * bad.card := by
  let fiber := fun t : U =>
    (Finset.univ : Finset U).filter (fun u => project u = t)
  have hcover :
      ((Finset.univ : Finset U).filter (fun u => project u ∈ bad)) ⊆
        bad.biUnion fiber := by
    intro u hu
    have hup : project u ∈ bad := (Finset.mem_filter.mp hu).2
    exact Finset.mem_biUnion.mpr ⟨project u, hup,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  calc
    ((Finset.univ : Finset U).filter (fun u => project u ∈ bad)).card ≤
        (bad.biUnion fiber).card := Finset.card_le_card hcover
    _ ≤ ∑ t ∈ bad, (fiber t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ bad, n := Finset.sum_le_sum
        (fun t _ => encoded_projection_fiber_le encode henc project n hn hpower t)
    _ = n * bad.card := by simp [mul_comm]

/-- A fixed injective circle translation after projection does not enlarge
the bad-set bound. This covers the periodicity form of the modeled quotient
samples without assuming that the native code implements the model. -/
theorem encoded_shifted_projection_bad_le {U K : Type*}
    [Fintype U] [DecidableEq U] [Field K] [Fintype K] [DecidableEq K]
    (encode : U → K) (henc : Function.Injective encode)
    (project : U → U) (n : ℕ) (hn : 0 < n)
    (hpower : ∀ u, encode (project u) = (encode u) ^ n)
    (shift : U → U) (hshift : Function.Injective shift)
    (bad : Finset U) :
    ((Finset.univ : Finset U).filter
      (fun u => shift (project u) ∈ bad)).card ≤ n * bad.card := by
  let pulled := (Finset.univ : Finset U).filter (fun t => shift t ∈ bad)
  have hpulled : pulled.card ≤ bad.card := by
    have himage : pulled.image shift ⊆ bad := by
      intro t ht
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
      exact (Finset.mem_filter.mp hu).2
    calc
      pulled.card = (pulled.image shift).card :=
        (Finset.card_image_of_injective pulled hshift).symm
      _ ≤ bad.card := Finset.card_le_card himage
  have hbound := encoded_projection_bad_le
    encode henc project n hn hpower pulled
  have hsubset : n * pulled.card ≤ n * bad.card :=
    Nat.mul_le_mul_left n hpulled
  simpa only [pulled, Finset.mem_filter, Finset.mem_univ,
    true_and] using (hbound.trans hsubset)

noncomputable def qm31BadPreimage (k : ℕ)
    (bad : Finset (Circle ConcreteCircleCount.QM31)) :
    Finset (Circle ConcreteCircleCount.QM31) := by
  classical
  exact (Finset.univ : Finset (Circle ConcreteCircleCount.QM31)).filter
    (fun p => (((CirclePowerEncoding.double
      (K := ConcreteCircleCount.QM31))^[k]) p) ∈ bad)

/-- The modeled QM31 repeated-doubling map has the claimed `2^k` fiber
budget for any target-height bad set. This uses the proved `x+i*y`
encoding; identifying `bad` with the native conjugate-fixed target set
and the Zig projection with this model are separate refinement steps. -/
theorem qm31_doubling_bad_le (k : ℕ)
    (bad : Finset (Circle ConcreteCircleCount.QM31)) :
    (qm31BadPreimage k bad).card ≤ 2 ^ k * bad.card := by
  classical
  unfold qm31BadPreimage
  exact encoded_projection_bad_le
    (CirclePowerEncoding.encode CirclePowerEncoding.qm31Imaginary)
    CirclePowerEncoding.qm31_encode_injective
    ((CirclePowerEncoding.double (K := ConcreteCircleCount.QM31))^[k])
    (2 ^ k) (by positivity)
    (fun p => CirclePowerEncoding.qm31_encode_iterated_double p k) bad

noncomputable def qm31ShiftedBadPreimage (k : ℕ)
    (shift : Circle ConcreteCircleCount.QM31)
    (bad : Finset (Circle ConcreteCircleCount.QM31)) :
    Finset (Circle ConcreteCircleCount.QM31) := by
  classical
  exact (Finset.univ : Finset (Circle ConcreteCircleCount.QM31)).filter
    (fun p => CirclePowerEncoding.translate shift
      (((CirclePowerEncoding.double
        (K := ConcreteCircleCount.QM31))^[k]) p) ∈ bad)

theorem qm31_shifted_doubling_bad_le (k : ℕ)
    (shift : Circle ConcreteCircleCount.QM31)
    (bad : Finset (Circle ConcreteCircleCount.QM31)) :
    (qm31ShiftedBadPreimage k shift bad).card ≤ 2 ^ k * bad.card := by
  classical
  unfold qm31ShiftedBadPreimage
  exact encoded_shifted_projection_bad_le
    (CirclePowerEncoding.encode CirclePowerEncoding.qm31Imaginary)
    CirclePowerEncoding.qm31_encode_injective
    ((CirclePowerEncoding.double (K := ConcreteCircleCount.QM31))^[k])
    (2 ^ k) (by positivity)
    (fun p => CirclePowerEncoding.qm31_encode_iterated_double p k)
    (CirclePowerEncoding.translate shift)
    (CirclePowerEncoding.qm31_translate_injective shift) bad

theorem raw_guard_complement_card_arithmetic :
    (q ^ 4 - 1) - rawSupport = zeroUpperYTargets := by
  norm_num [q, rawSupport, lowerSize, zeroUpperYTargets]

theorem exclusion_budget_lt_raw_support :
    projectedExclusionBudget < rawSupport := by
  norm_num [projectedExclusionBudget, zeroUpperYTargets,
    rawSupport, lowerSize, q]

/-- If every projected bad set has the stated cardinality cap, this
union bound leaves at least `rawSupport - projectedExclusionBudget` points.
The predicates can encode a shift and a height-specific projection. -/
theorem survivors_lower_bound {U : Type*} [DecidableEq U]
    (raw : Finset U)
    (bad17 : Fin 4 → Finset U)
    (bad11 : Fin 32 → Finset U) (bad5 : Fin 23 → Finset U)
    (hraw : raw.card = rawSupport)
    (h17 : ∀ i, (bad17 i).card ≤ zeroUpperYTargets)
    (h11 : ∀ i, (bad11 i).card ≤ 2 ^ 6 * zeroUpperYTargets)
    (h5 : ∀ i, (bad5 i).card ≤ 2 ^ 12 * zeroUpperYTargets) :
    rawSupport - projectedExclusionBudget ≤
      (raw \ (((Finset.univ : Finset (Fin 4)).biUnion bad17) ∪
        ((Finset.univ : Finset (Fin 32)).biUnion bad11) ∪
        ((Finset.univ : Finset (Fin 23)).biUnion bad5))).card := by
  let b17 := (Finset.univ : Finset (Fin 4)).biUnion bad17
  let b11 := (Finset.univ : Finset (Fin 32)).biUnion bad11
  let b5 := (Finset.univ : Finset (Fin 23)).biUnion bad5
  have hb17 : b17.card ≤ 4 * zeroUpperYTargets := by
    calc
      b17.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin 4)), (bad17 i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin 4)), zeroUpperYTargets :=
        Finset.sum_le_sum (fun i _ => h17 i)
      _ = 4 * zeroUpperYTargets := by simp
  have hb11 : b11.card ≤ 32 * (2 ^ 6 * zeroUpperYTargets) := by
    calc
      b11.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin 32)), (bad11 i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin 32)),
          2 ^ 6 * zeroUpperYTargets :=
        Finset.sum_le_sum (fun i _ => h11 i)
      _ = 32 * (2 ^ 6 * zeroUpperYTargets) := by simp
  have hb5 : b5.card ≤ 23 * (2 ^ 12 * zeroUpperYTargets) := by
    calc
      b5.card ≤ ∑ i ∈ (Finset.univ : Finset (Fin 23)), (bad5 i).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin 23)),
          2 ^ 12 * zeroUpperYTargets :=
        Finset.sum_le_sum (fun i _ => h5 i)
      _ = 23 * (2 ^ 12 * zeroUpperYTargets) := by simp
  have hbad : (b17 ∪ b11 ∪ b5).card ≤ projectedExclusionBudget := by
    calc
      (b17 ∪ b11 ∪ b5).card ≤ b17.card + b11.card + b5.card := by
        calc
          (b17 ∪ b11 ∪ b5).card ≤ (b17 ∪ b11).card + b5.card :=
            Finset.card_union_le _ _
          _ ≤ b17.card + b11.card + b5.card := by
            have hpair : (b17 ∪ b11).card ≤ b17.card + b11.card :=
              Finset.card_union_le _ _
            omega
      _ ≤ 4 * zeroUpperYTargets +
          32 * (2 ^ 6 * zeroUpperYTargets) +
          23 * (2 ^ 12 * zeroUpperYTargets) := by omega
      _ = projectedExclusionBudget := by
        unfold projectedExclusionBudget
        ring
  have hinter : (raw ∩ (b17 ∪ b11 ∪ b5)).card ≤
      (b17 ∪ b11 ∪ b5).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hpartition := Finset.card_sdiff_add_card_inter raw
    (b17 ∪ b11 ∪ b5)
  change rawSupport - projectedExclusionBudget ≤
    (raw \ (b17 ∪ b11 ∪ b5)).card
  omega

/-- Pure arithmetic for a draw already uniform on the raw-good circle set,
conditioned further on all explicit-claim guards. This ratio is not the
full-circle conditioning ratio or an additive attack-success bound, and it
does not apply until every native fiber cap is discharged. -/
theorem ideal_conditioning_factor_lt :
    (rawSupport : ℚ) /
        ((rawSupport - projectedExclusionBudget : ℕ) : ℚ) <
      1 + (1 : ℚ) / 2 ^ 40 := by
  norm_num [rawSupport, projectedExclusionBudget,
    zeroUpperYTargets, lowerSize, q]

end S31.Gadgets.PcsFri.ProjectedOodSupportBound
