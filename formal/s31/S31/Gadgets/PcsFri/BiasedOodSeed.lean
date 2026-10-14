import S31.Gadgets.PcsFri.BiasedLookupPair
import Mathlib.Tactic

/-!
One native OOD seed is four M31 residues obtained by reducing four raw
BLAKE2s words. This is a finite counting model conditional on independent
uniform raw words at one fixed transcript input. It does not assert that
concrete BLAKE2s is a random oracle or that an adaptive prover supplies a
uniform fixed-prefix draw.
-/

namespace S31.Gadgets.PcsFri.BiasedOodSeed

open BiasedLookupPair

abbrev Seed := Fin 4 → Fin modulus
abbrev RawWords := Fin 4 → Nat

def seedWeight (seed : Seed) : Nat :=
  ∏ i : Fin 4, fiberSize (seed i)

def rawSeedFiber (seed : Seed) : Finset RawWords :=
  Fintype.piFinset (fun i => rawFiber (seed i))

theorem raw_seed_fiber_card (seed : Seed) :
    (rawSeedFiber seed).card = seedWeight seed := by
  simp [rawSeedFiber, seedWeight, rawFiber_card]

theorem seed_weight_le (seed : Seed) : seedWeight seed ≤ 3 ^ 4 := by
  unfold seedWeight
  calc
    (∏ i : Fin 4, fiberSize (seed i)) ≤ ∏ _i : Fin 4, (3 : Nat) := by
      apply Finset.prod_le_prod
      · intro i hi; omega
      · intro i hi; exact fiberSize_le_three (seed i)
    _ = 3 ^ 4 := by simp

def eventWeight (event : Finset Seed) : Nat :=
  ∑ seed ∈ event, seedWeight seed

def eventRawFiber (event : Finset Seed) : Finset RawWords :=
  event.biUnion rawSeedFiber

theorem event_raw_fiber_card (event : Finset Seed) :
    (eventRawFiber event).card = eventWeight event := by
  have hdisjoint : ∀ a ∈ event, ∀ b ∈ event, a ≠ b →
      Disjoint (rawSeedFiber a) (rawSeedFiber b) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro words hwa hwb
    apply hab
    funext i
    apply Fin.ext
    have hma := (Fintype.mem_piFinset.mp hwa i)
    have hmb := (Fintype.mem_piFinset.mp hwb i)
    exact ((mem_rawFiber_iff (a i) (words i)).mp hma).2.symm.trans
      ((mem_rawFiber_iff (b i) (words i)).mp hmb).2
  simp only [eventRawFiber, eventWeight]
  rw [Finset.card_biUnion hdisjoint]
  simp [raw_seed_fiber_card]

theorem event_weight_le (event : Finset Seed) :
    eventWeight event ≤ 3 ^ 4 * event.card := by
  unfold eventWeight
  calc
    (∑ seed ∈ event, seedWeight seed) ≤
        ∑ _seed ∈ event, 3 ^ 4 := by
      apply Finset.sum_le_sum
      intro seed hs
      exact seed_weight_le seed
    _ = 3 ^ 4 * event.card := by simp [mul_comm]

def nativeProbability (event : Finset Seed) : ℚ :=
  (eventWeight event : ℚ) / (wordSpace ^ 4 : Nat)

def uniformProbability (event : Finset Seed) : ℚ :=
  (event.card : ℚ) / (modulus ^ 4 : Nat)

def maxDensityRatio : ℚ :=
  ((3 * modulus) ^ 4 : Nat) / (wordSpace ^ 4 : Nat)

/-- The exact four-word maximum likelihood ratio against uniform M31⁴. -/
theorem native_probability_le_ratio_uniform
    (event : Finset Seed) :
    nativeProbability event ≤ maxDensityRatio * uniformProbability event := by
  have h : (eventWeight event : ℚ) ≤ (3 ^ 4 * event.card : Nat) := by
    exact_mod_cast event_weight_le event
  have hp : (modulus : ℚ) ≠ 0 := by norm_num [modulus]
  have hw : (wordSpace ^ 4 : ℚ) > 0 := by norm_num [wordSpace]
  have hid : maxDensityRatio * uniformProbability event =
      ((3 ^ 4 * event.card : Nat) : ℚ) / (wordSpace ^ 4 : Nat) := by
    dsimp [maxDensityRatio, uniformProbability]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
    field_simp [hp]
    ring
  rw [hid]
  exact div_le_div_of_nonneg_right h (le_of_lt hw)

/-- Numerator form for using a separately proved event-cardinality bound. -/
theorem native_probability_le_card (event : Finset Seed) :
    nativeProbability event ≤
      ((3 ^ 4 * event.card : Nat) : ℚ) / (wordSpace ^ 4 : Nat) := by
  have h : (eventWeight event : ℚ) ≤ (3 ^ 4 * event.card : Nat) := by
    exact_mod_cast event_weight_le event
  exact div_le_div_of_nonneg_right h
    (by norm_num [wordSpace] : (0 : ℚ) ≤ (wordSpace ^ 4 : Nat))

/-- Interface for transporting a circle bad-set bound through any seed map
that is injective on the regular/admitted seed set. The selected rational
map has such a model-level inverse, but its native transcript law is not
established here. -/
theorem admitted_bad_event_le {U : Type*} [DecidableEq U]
    (admitted : Finset Seed) (point : Seed → U)
    (hinj : ∀ a ∈ admitted, ∀ b ∈ admitted,
      point a = point b → a = b)
    (bad : Finset U) :
    ((admitted.filter (fun seed => point seed ∈ bad))).card ≤
      bad.card := by
  let event := admitted.filter (fun seed => point seed ∈ bad)
  have heventInj : Set.InjOn point event := by
    intro a ha b hb hpoint
    exact hinj a (Finset.mem_filter.mp ha).1 b
      (Finset.mem_filter.mp hb).1 hpoint
  have himage : event.image point ⊆ bad := by
    intro p hp
    obtain ⟨seed, hs, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_filter.mp hs).2
  calc
    event.card = (event.image point).card :=
      (Finset.card_image_of_injOn heventInj).symm
    _ ≤ bad.card := Finset.card_le_card himage

theorem admitted_bad_probability_le {U : Type*} [DecidableEq U]
    (admitted : Finset Seed) (point : Seed → U)
    (hinj : ∀ a ∈ admitted, ∀ b ∈ admitted,
      point a = point b → a = b)
    (bad : Finset U) :
    nativeProbability (admitted.filter (fun seed => point seed ∈ bad)) ≤
      ((3 ^ 4 * bad.card : Nat) : ℚ) / (wordSpace ^ 4 : Nat) := by
  have hcard := admitted_bad_event_le admitted point hinj bad
  have hnat : 3 ^ 4 *
      (admitted.filter (fun seed => point seed ∈ bad)).card ≤
      3 ^ 4 * bad.card := Nat.mul_le_mul_left _ hcard
  have hq :
      ((3 ^ 4 *
        (admitted.filter (fun seed => point seed ∈ bad)).card : Nat) : ℚ) ≤
      ((3 ^ 4 * bad.card : Nat) : ℚ) := by exact_mod_cast hnat
  exact (native_probability_le_card _).trans
    (div_le_div_of_nonneg_right hq
      (by norm_num [wordSpace] : (0 : ℚ) ≤ (wordSpace ^ 4 : Nat)))

theorem zero_seed_weight :
    seedWeight (fun _ : Fin 4 => (⟨0, by decide⟩ : Fin modulus)) =
      3 ^ 4 := by
  simp [seedWeight, fiberSize]

end S31.Gadgets.PcsFri.BiasedOodSeed
