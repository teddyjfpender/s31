import S31.Gadgets.PcsFri.BiasedOodSeed
import S31.Gadgets.PcsFri.ConcreteCircleCount
import Mathlib.Tactic

/-!
Coordinate bridge from the four-residue OOD seed counting model to the
finite QM31 circle model. This is pure field arithmetic; native transcript
and implementation refinement remain separate.
-/

namespace S31.Gadgets.PcsFri.BiasedOodSeedCircle

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

open OodRationalMap

abbrev Seed := BiasedOodSeed.Seed
abbrev QM31 := ConcreteCircleCount.QM31

/-- Native c0.a/c0.b/c1.a/c1.b order. -/
def seedQM (seed : Seed) : QM31 :=
  ⟨⟨(seed 0).val, (seed 1).val⟩,
    ⟨(seed 2).val, (seed 3).val⟩⟩

private theorem fin_cast_injective
    (a b : Fin BiasedLookupPair.modulus)
    (h : ((a.val : Nat) : S31.Field.F) = (b.val : S31.Field.F)) :
    a = b := by
  apply Fin.ext
  have hv := congrArg ZMod.val h
  change a.val % 2147483647 = b.val % 2147483647 at hv
  have ha : a.val < 2147483647 := a.isLt
  have hb : b.val < 2147483647 := b.isLt
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hv

theorem seedQM_injective : Function.Injective seedQM := by
  intro a b hab
  funext j
  fin_cases j
  · exact fin_cast_injective (a 0) (b 0)
      (congrArg (fun z : QM31 => z.c0.a) hab)
  · exact fin_cast_injective (a 1) (b 1)
      (congrArg (fun z : QM31 => z.c0.b) hab)
  · exact fin_cast_injective (a 2) (b 2)
      (congrArg (fun z : QM31 => z.c1.a) hab)
  · exact fin_cast_injective (a 3) (b 3)
      (congrArg (fun z : QM31 => z.c1.b) hab)

/-- A total map for event counting. Only its restriction to explicitly
admitted regular seeds is used; the singular branch is a fixed circle point. -/
noncomputable def seedPoint (seed : Seed) :
    ConcreteCircleCount.Circle QM31 :=
  if h : regular (seedQM seed) then
    ⟨(x (seedQM seed), y (seedQM seed)), on_circle _ h⟩
  else
    ⟨(-1, 0), by norm_num⟩

theorem seedPoint_regular (seed : Seed) (h : regular (seedQM seed)) :
    (seedPoint seed).1 = (x (seedQM seed), y (seedQM seed)) := by
  simp only [seedPoint, dif_pos h]

theorem seedPoint_injective_on_regular
    (admitted : Finset Seed)
    (hregular : ∀ seed ∈ admitted, regular (seedQM seed)) :
    ∀ a ∈ admitted, ∀ b ∈ admitted,
      seedPoint a = seedPoint b → a = b := by
  intro a ha b hb hab
  have hra : regular (seedQM a) := hregular a ha
  have hrb : regular (seedQM b) := hregular b hb
  have hx : x (seedQM a) = x (seedQM b) := by
    have hcoord := congrArg
      (fun p : ConcreteCircleCount.Circle QM31 => p.1.1) hab
    simpa only [seedPoint_regular a hra, seedPoint_regular b hrb] using hcoord
  have hy : y (seedQM a) = y (seedQM b) := by
    have hcoord := congrArg
      (fun p : ConcreteCircleCount.Circle QM31 => p.1.2) hab
    simpa only [seedPoint_regular a hra, seedPoint_regular b hrb] using hcoord
  apply seedQM_injective
  exact injective_on_regular (seedQM a) (seedQM b)
    hra hrb hx hy

/-- The exact finite-field rational map gives at most one admitted seed per
circle point. This bounds the joint, unconditioned event of admission and a
bad point; a conditional probability needs a lower bound on admission mass.
The numerator is still a fixed-input raw-word model. -/
noncomputable def circleBadEvent
    (admitted : Finset Seed)
    (bad : Finset (ConcreteCircleCount.Circle QM31)) : Finset Seed := by
  classical
  exact admitted.filter (fun seed => seedPoint seed ∈ bad)

theorem circle_bad_probability_le
    (admitted : Finset Seed)
    (hregular : ∀ seed ∈ admitted, regular (seedQM seed))
    (bad : Finset (ConcreteCircleCount.Circle QM31)) :
    BiasedOodSeed.nativeProbability
      (circleBadEvent admitted bad) ≤
      ((3 ^ 4 * bad.card : Nat) : ℚ) /
        (BiasedLookupPair.wordSpace ^ 4 : Nat) := by
  classical
  unfold circleBadEvent
  exact BiasedOodSeed.admitted_bad_probability_le admitted seedPoint
    (seedPoint_injective_on_regular admitted hregular) bad

end S31.Gadgets.PcsFri.BiasedOodSeedCircle
