import Mathlib.Tactic

/-!
The selected Blake2sM31 lookup draw takes two QM31 values from one reduced
eight-word digest. This is a finite counting model, conditional on the eight
*raw* 32-bit words of one fixed-prefix draw being independent uniform words.
It does not assert that a BLAKE2s transcript, an adversarially selected nonce,
or an adaptive BCS execution satisfies that premise.
-/

namespace S31.Gadgets.PcsFri.BiasedLookupPair

def modulus : Nat := 2 ^ 31 - 1
def wordSpace : Nat := 2 ^ 32

theorem wordSpace_eq : wordSpace = 2 * modulus + 2 := by decide

/-- Every 32-bit word reducing to `r` is one of two usual preimages, plus a
third preimage precisely for the residues zero and one. -/
theorem raw_preimages (r x : Nat) (hr : r < modulus) :
    (x < wordSpace ∧ x % modulus = r) ↔
      x = r ∨ x = r + modulus ∨
        ((r = 0 ∨ r = 1) ∧ x = r + 2 * modulus) := by
  have hmod := Nat.mod_add_div x modulus
  unfold modulus wordSpace at *
  constructor
  · rintro ⟨hx, hrem⟩
    have hq : x / (2 ^ 31 - 1) ≤ 2 := by omega
    have hz : x / (2 ^ 31 - 1) = 0 ∨ 0 < x / (2 ^ 31 - 1) := by omega
    rcases hz with hz | hpos
    · left; omega
    have hq' : x / (2 ^ 31 - 1) = 1 ∨ x / (2 ^ 31 - 1) = 2 := by omega
    rcases hq' with h1 | h2
    · right; left; omega
    · right; right; constructor
      · omega
      · omega
  · rintro (h | h | ⟨hsmall, h⟩) <;> subst x
    · constructor <;> omega
    · constructor <;> omega
    · constructor <;> omega

/-- The number of raw preimages of one canonical M31 residue. -/
def fiberSize (r : Fin modulus) : Nat :=
  if r.val = 0 ∨ r.val = 1 then 3 else 2

/-- A small explicit representation of the raw 32-bit modulo fiber. -/
def rawFiber (r : Fin modulus) : Finset Nat :=
  if r.val = 0 ∨ r.val = 1 then
    {r.val, r.val + modulus, r.val + 2 * modulus}
  else
    {r.val, r.val + modulus}

theorem mem_rawFiber_iff (r : Fin modulus) (x : Nat) :
    x ∈ rawFiber r ↔ x < wordSpace ∧ x % modulus = r.val := by
  rw [raw_preimages r.val x r.isLt]
  by_cases h : r.val = 0 ∨ r.val = 1
  · simp [rawFiber, h]
  · simp [rawFiber, h]

theorem rawFiber_card (r : Fin modulus) :
    (rawFiber r).card = fiberSize r := by
  have hp : 0 < modulus := by norm_num [modulus]
  by_cases h : r.val = 0 ∨ r.val = 1
  · have ha : r.val ∉ ({r.val + modulus, r.val + 2 * modulus} : Finset Nat) := by
      simp; omega
    have hb : r.val + modulus ∉ ({r.val + 2 * modulus} : Finset Nat) := by
      simp; omega
    simp only [rawFiber, fiberSize, if_pos h]
    rw [Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb]
    simp
  · have ha : r.val ∉ ({r.val + modulus} : Finset Nat) := by
      simp; omega
    simp only [rawFiber, fiberSize, if_neg h]
    rw [Finset.card_insert_of_notMem ha]
    simp

theorem fiberSize_le_three (r : Fin modulus) : fiberSize r ≤ 3 := by
  simp only [fiberSize]
  split_ifs <;> omega

theorem fiberSize_zero : fiberSize ⟨0, by decide⟩ = 3 := by
  simp [fiberSize]

/-- The eight coordinates are `z[0..4]` followed by `alpha[0..4]`. -/
def pairWeight (pair : Fin 8 → Fin modulus) : Nat :=
  ∏ i : Fin 8, fiberSize (pair i)

theorem pairWeight_eq_raw_fiber_product (pair : Fin 8 → Fin modulus) :
    pairWeight pair = ∏ i : Fin 8, (rawFiber (pair i)).card := by
  simp [pairWeight, rawFiber_card]

/-- The finite inverse image of one eight-coordinate reduced output. -/
def rawTupleFiber (pair : Fin 8 → Fin modulus) : Finset (Fin 8 → Nat) :=
  Fintype.piFinset (fun i => rawFiber (pair i))

theorem mem_rawTupleFiber_iff (pair : Fin 8 → Fin modulus)
    (words : Fin 8 → Nat) :
    words ∈ rawTupleFiber pair ↔
      ∀ i, words i < wordSpace ∧ words i % modulus = (pair i).val := by
  simp only [rawTupleFiber, Fintype.mem_piFinset, mem_rawFiber_iff]

/-- This identifies the model weight with the exact preimage count of the
eight-word reduction map, rather than merely defining it to be a product. -/
theorem rawTupleFiber_card (pair : Fin 8 → Fin modulus) :
    (rawTupleFiber pair).card = pairWeight pair := by
  simp [rawTupleFiber, pairWeight, rawFiber_card]

theorem pairWeight_le (pair : Fin 8 → Fin modulus) :
    pairWeight pair ≤ 3 ^ 8 := by
  unfold pairWeight
  calc
    (∏ i : Fin 8, fiberSize (pair i)) ≤ ∏ _i : Fin 8, (3 : Nat) := by
      apply Finset.prod_le_prod
      · intro i hi; omega
      · intro i hi; exact fiberSize_le_three (pair i)
    _ = 3 ^ 8 := by simp

/-- An event can be any subset of the two-QM31 output space. -/
def eventWeight (event : Finset (Fin 8 → Fin modulus)) : Nat :=
  ∑ pair ∈ event, pairWeight pair

/-- The raw-word tuples that reduce into an arbitrary output event. -/
def eventRawFiber (event : Finset (Fin 8 → Fin modulus)) :
    Finset (Fin 8 → Nat) :=
  event.biUnion rawTupleFiber

theorem eventRawFiber_card (event : Finset (Fin 8 → Fin modulus)) :
    (eventRawFiber event).card = eventWeight event := by
  have hdisjoint : ∀ a ∈ event, ∀ b ∈ event, a ≠ b →
      Disjoint (rawTupleFiber a) (rawTupleFiber b) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro words hwa hwb
    apply hab
    funext i
    apply Fin.ext
    exact ((mem_rawTupleFiber_iff a words).mp hwa i).2.symm.trans
      ((mem_rawTupleFiber_iff b words).mp hwb i).2
  simp only [eventRawFiber, eventWeight]
  rw [Finset.card_biUnion hdisjoint]
  simp [rawTupleFiber_card]

theorem eventWeight_le (event : Finset (Fin 8 → Fin modulus)) :
    eventWeight event ≤ 3 ^ 8 * event.card := by
  unfold eventWeight
  calc
    (∑ pair ∈ event, pairWeight pair) ≤ ∑ _pair ∈ event, 3 ^ 8 := by
      apply Finset.sum_le_sum
      intro pair hp
      exact pairWeight_le pair
    _ = 3 ^ 8 * event.card := by simp [mul_comm]

/-- Exact numerator inequality for the arbitrary-event density ratio:
`Pr_native(E) = eventWeight(E) / wordSpace^8` and
`Pr_uniform(E) = |E| / modulus^8`. -/
theorem event_density_ratio_numerator
    (event : Finset (Fin 8 → Fin modulus)) :
    eventWeight event * modulus ^ 8 ≤
      event.card * (3 * modulus) ^ 8 := by
  have h := eventWeight_le event
  nlinarith [Nat.zero_le (modulus ^ 8)]

/-- The conditional distribution of the pair for independent, uniform raw
32-bit words, with one fixed draw input. -/
def nativeProbability (event : Finset (Fin 8 → Fin modulus)) : ℚ :=
  (eventWeight event : ℚ) / (wordSpace ^ 8 : Nat)

def uniformProbability (event : Finset (Fin 8 → Fin modulus)) : ℚ :=
  (event.card : ℚ) / (modulus ^ 8 : Nat)

def maxDensityRatio : ℚ :=
  ((3 * modulus) ^ 8 : Nat) / (wordSpace ^ 8 : Nat)

/-- The exact, sharp likelihood-ratio bound for an arbitrary output event.
The factor is `(3p / 2^32)^8`, with `p = 2^31 - 1`. -/
theorem nativeProbability_le_ratio_uniform
    (event : Finset (Fin 8 → Fin modulus)) :
    nativeProbability event ≤ maxDensityRatio * uniformProbability event := by
  have h : (eventWeight event : ℚ) ≤ (3 ^ 8 * event.card : Nat) := by
    exact_mod_cast eventWeight_le event
  have hp : (modulus : ℚ) ≠ 0 := by norm_num [modulus]
  have hw : (wordSpace ^ 8 : ℚ) > 0 := by norm_num [wordSpace]
  have hid : maxDensityRatio * uniformProbability event =
      ((3 ^ 8 * event.card : Nat) : ℚ) / (wordSpace ^ 8 : Nat) := by
    dsimp [maxDensityRatio, uniformProbability]
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_pow]
    field_simp [hp]
    ring
  rw [hid]
  exact div_le_div_of_nonneg_right h (le_of_lt hw)

/-- The factor `(3p / 2^32)^8` is optimal for arbitrary events. -/
theorem all_zero_pair_weight :
    pairWeight (fun _ : Fin 8 => (⟨0, by decide⟩ : Fin modulus)) = 3 ^ 8 := by
  simp [pairWeight, fiberSize]

end S31.Gadgets.PcsFri.BiasedLookupPair
