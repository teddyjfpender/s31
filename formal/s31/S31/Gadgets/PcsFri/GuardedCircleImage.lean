import S31.Gadgets.PcsFri.ConcreteCircleCount
import Mathlib.Tactic

/-!
The CAS05 OOD point is the rational map of one QM31 transcript seed. The
native experimental verifier rejects a singular map and rejects `y.c1 = 0`.
This module identifies the algebraic image of precisely those successful
guards. It does not formalize the channel draw or a soundness probability.
-/

namespace S31.Gadgets.PcsFri.GuardedCircleImage

set_option maxHeartbeats 1000000

open OodRationalMap ConcreteCircleCount

abbrev CM31 := ConcreteCircleCount.CM31
abbrev QM31 := ConcreteCircleCount.QM31

def guardedSeed := { t : QM31 // regular t ∧ (y t).c1 ≠ 0 }
def guardedCircle := { p : Circle QM31 // p.1.2.c1 ≠ 0 }

/-- The successful algebraic seed map has exactly the QM31 circle points
whose y coordinate has a nonzero upper CM31 coefficient as its image. -/
noncomputable def seedToGuardedCircle (t : guardedSeed) : guardedCircle :=
  ⟨⟨(x t.1, y t.1), on_circle t.1 t.2.1⟩, t.2.2⟩

theorem guarded_y_excludes_omitted_point (p : guardedCircle) :
    1 + p.1.1.1 ≠ 0 := by
  intro hx
  have hy := (omitted_circle_point p.1.1.1 p.1.1.2 p.1.2 hx).2
  exact p.2 (by rw [hy]; rfl)

theorem seed_to_guarded_circle_bijective :
    Function.Bijective seedToGuardedCircle := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact injective_on_regular a.1 b.1 a.2.1 b.2.1
      (congrArg (fun p : guardedCircle => p.1.1.1) hab)
      (congrArg (fun p : guardedCircle => p.1.1.2) hab)
  · intro p
    obtain ⟨t, ht, hx, hy⟩ := circle_point_has_preimage
      p.1.1.1 p.1.1.2 p.1.2 (guarded_y_excludes_omitted_point p)
    refine ⟨⟨t, ht, ?_⟩, ?_⟩
    · rw [hy]
      exact p.2
    · apply Subtype.ext
      apply Subtype.ext
      change (x t, y t) = p.1.1
      exact Prod.ext hx hy

noncomputable def guardedSeedCircleEquiv : guardedSeed ≃ guardedCircle :=
  Equiv.ofBijective seedToGuardedCircle seed_to_guarded_circle_bijective

/-- This is a set identity for the full successful rational-map image;
there is no hidden exclusion beyond the upper-y guard. -/
theorem guarded_image_eq_upper_y_circle :
    Set.range (fun t : guardedSeed => (seedToGuardedCircle t).1) =
      { p : Circle QM31 | p.1.2.c1 ≠ 0 } := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact (seedToGuardedCircle t).2
  · intro hp
    obtain ⟨t, ht⟩ := seed_to_guarded_circle_bijective.2 ⟨p, hp⟩
    exact ⟨t, congrArg Subtype.val ht⟩

/-- Every accepted point is outside the entire embedded CM31 circle, not
merely outside one chosen evaluation domain. -/
theorem guarded_circle_outside_cm31 (p : guardedCircle) :
    p.1 ∉ Set.range lowerCircle := by
  rintro ⟨lower, heq⟩
  have hy := congrArg (fun q : Circle QM31 => q.1.2.c1) heq
  exact p.2 (by simpa [lowerCircle, embedCM] using hy.symm)

theorem guarded_seed_outside_cm31 (t : guardedSeed) :
    (seedToGuardedCircle t).1 ∉ Set.range lowerCircle :=
  guarded_circle_outside_cm31 (seedToGuardedCircle t)

theorem guarded_image_subset_two_point_universe :
    Set.range (fun t : guardedSeed => (seedToGuardedCircle t).1) ⊆
      (Set.range lowerCircle)ᶜ := by
  rintro p ⟨t, rfl⟩
  exact guarded_seed_outside_cm31 t

theorem guarded_image_ncard :
    (Set.range (fun t : guardedSeed => (seedToGuardedCircle t).1)).ncard =
      Nat.card guardedSeed := by
  rw [Set.ncard_range_of_injective]
  intro a b h
  exact seed_to_guarded_circle_bijective.1 (Subtype.ext h)

end S31.Gadgets.PcsFri.GuardedCircleImage
