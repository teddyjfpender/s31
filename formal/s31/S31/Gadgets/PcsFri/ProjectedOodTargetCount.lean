import S31.Gadgets.PcsFri.ProjectedOodSupportBound
import Mathlib.Tactic

/-!
Exact target-circle count for a conjugate-fixed `y` coordinate. This counts
algebraic points, not the distribution of native Fiat–Shamir seeds.
-/

namespace S31.Gadgets.PcsFri.ProjectedOodTargetCount

open ConcreteCircleCount ProjectedOodSupportBound

abbrev QM31 := ConcreteCircleCount.QM31

def goodSet : Set (Circle QM31) :=
  { p | p.1.2.c1 ≠ 0 }

def badSet : Set (Circle QM31) :=
  { p | p.1.2.c1 = 0 }

theorem good_set_card : goodSet.ncard = rawSupport := by
  have h := OodGuardFieldCount.card_guarded_circle_image
  rw [GuardedCircleImage.guarded_image_eq_upper_y_circle] at h
  simpa only [goodSet, rawSupport, lowerSize, q] using h

theorem bad_set_card : badSet.ncard = zeroUpperYTargets := by
  have hgood : goodSet.Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hbad : badSet.Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hdisjoint : Disjoint goodSet badSet := by
    apply Set.disjoint_left.mpr
    intro p hp hbp
    exact hp hbp
  have hunion : goodSet ∪ badSet = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    by_cases hp : p.1.2.c1 = 0
    · exact Or.inr hp
    · exact Or.inl hp
  have hpartition := Set.ncard_union_eq hdisjoint hgood hbad
  rw [hunion, Set.ncard_univ,
    Nat.card_eq_fintype_card,
    ConcreteCircleCount.card_circle_qm31,
    good_set_card] at hpartition
  have harith : 2147483647 ^ 4 - 1 =
      rawSupport + zeroUpperYTargets := by
    norm_num [zeroUpperYTargets, lowerSize, q, rawSupport]
  omega

noncomputable def badTarget : Finset (Circle QM31) := by
  classical
  exact badSet.toFinite.toFinset

theorem bad_target_card : badTarget.card = zeroUpperYTargets := by
  rw [← bad_set_card]
  exact (Set.ncard_eq_toFinset_card badSet).symm

/-- Exact target count combined with the modeled circle power-map fiber
bound. For each positive fold count this is a conservative upper bound; it
does not assume an exact coset distribution. -/
theorem projected_base_bad_le (k : ℕ) :
    (qm31BadPreimage k badTarget).card ≤
      2 ^ k * zeroUpperYTargets := by
  calc
    (qm31BadPreimage k badTarget).card ≤
        2 ^ k * badTarget.card := qm31_doubling_bad_le k badTarget
    _ = 2 ^ k * zeroUpperYTargets := by rw [bad_target_card]

theorem projected_h11_base_bad_le :
    (qm31BadPreimage 6 badTarget).card ≤
      2 ^ 6 * zeroUpperYTargets := projected_base_bad_le 6

theorem projected_h5_base_bad_le :
    (qm31BadPreimage 12 badTarget).card ≤
      2 ^ 12 * zeroUpperYTargets := projected_base_bad_le 12

noncomputable def rawGood : Finset (Circle QM31) := by
  classical
  exact goodSet.toFinite.toFinset

theorem raw_good_card : rawGood.card = rawSupport := by
  rw [← good_set_card]
  exact (Set.ncard_eq_toFinset_card goodSet).symm

noncomputable def baseSurvivors : Finset (Circle QM31) := by
  classical
  exact rawGood \ (qm31BadPreimage 6 badTarget ∪
    qm31BadPreimage 12 badTarget)

theorem base_survivors_lower_bound :
    rawSupport - (2 ^ 6 + 2 ^ 12) * zeroUpperYTargets ≤
      baseSurvivors.card := by
  classical
  let bad := qm31BadPreimage 6 badTarget ∪
    qm31BadPreimage 12 badTarget
  have hbad : bad.card ≤
      (2 ^ 6 + 2 ^ 12) * zeroUpperYTargets := by
    calc
      bad.card ≤ (qm31BadPreimage 6 badTarget).card +
          (qm31BadPreimage 12 badTarget).card :=
        Finset.card_union_le _ _
      _ ≤ 2 ^ 6 * zeroUpperYTargets +
          2 ^ 12 * zeroUpperYTargets :=
        Nat.add_le_add projected_h11_base_bad_le
          projected_h5_base_bad_le
      _ = (2 ^ 6 + 2 ^ 12) * zeroUpperYTargets := by ring
  have hinter : (rawGood ∩ bad).card ≤ bad.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hpartition := Finset.card_sdiff_add_card_inter rawGood bad
  change rawSupport - (2 ^ 6 + 2 ^ 12) * zeroUpperYTargets ≤
    (rawGood \ bad).card
  rw [raw_good_card] at hpartition
  omega

theorem base_survivors_positive : 0 < baseSurvivors.card := by
  have h := base_survivors_lower_bound
  have hpositive :
      0 < rawSupport - (2 ^ 6 + 2 ^ 12) * zeroUpperYTargets := by
    norm_num [rawSupport, zeroUpperYTargets, lowerSize, q]
  omega

end S31.Gadgets.PcsFri.ProjectedOodTargetCount
