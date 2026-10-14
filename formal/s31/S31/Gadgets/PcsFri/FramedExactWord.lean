import Mathlib.Tactic

/-!
Arithmetic of one raw word in the proposed `S31NAT9F` framed sampler.
The native sampler rejects `w >= 2p` before reducing by at most one `p`.
This proves the exact preimage count. It does not model BLAKE2s, random-oracle
independence, block-cap failure, or a selected verifier.
-/

namespace S31.Gadgets.PcsFri.FramedExactWord

def p : Nat := 2 ^ 31 - 1
def rawSize : Nat := 2 ^ 32

def canonical (word : Nat) : Option Nat :=
  if word < 2 * p then
    some (if word < p then word else word - p)
  else none

theorem accepted_canonical (word residue : Nat)
    (hresidue : residue < p) :
    canonical word = some residue ↔ word = residue ∨ word = residue + p := by
  unfold canonical
  split_ifs with haccepted hlow
  · simp only [Option.some.injEq]
    omega
  · simp only [Option.some.injEq]
    omega
  · simp
    omega

theorem accepted_has_two_distinct_preimages (residue : Nat)
    (hresidue : residue < p) :
    residue < rawSize ∧ residue + p < rawSize ∧
      residue ≠ residue + p ∧
      canonical residue = some residue ∧
      canonical (residue + p) = some residue := by
  have hp : 0 < p := by norm_num [p]
  have hsize : 2 * p ≤ rawSize := by norm_num [p, rawSize]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · simp [canonical]
    omega
  · simp [canonical]
    omega

/-- Over the complete native `u32` input space, an accepted residue has
exactly two raw preimages. This is the counting fact required for a uniform
conditional distribution under an independent uniform raw-word oracle. -/
def preimages (residue : Nat) : Finset (Fin rawSize) :=
  Finset.univ.filter (fun word => canonical word.val = some residue)

theorem preimages_eq_pair (residue : Nat) (hresidue : residue < p) :
    preimages residue =
      {⟨residue, (accepted_has_two_distinct_preimages residue hresidue).1⟩,
       ⟨residue + p,
         (accepted_has_two_distinct_preimages residue hresidue).2.1⟩} := by
  ext word
  simp only [preimages, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  rw [accepted_canonical word.val residue hresidue]
  simp only [Fin.ext_iff]

theorem preimages_card_two (residue : Nat) (hresidue : residue < p) :
    (preimages residue).card = 2 := by
  rw [preimages_eq_pair residue hresidue]
  have hdistinct := (accepted_has_two_distinct_preimages residue hresidue).2.2.1
  have hne :
      (⟨residue, (accepted_has_two_distinct_preimages residue hresidue).1⟩ : Fin rawSize) ≠
      ⟨residue + p, (accepted_has_two_distinct_preimages residue hresidue).2.1⟩ := by
    intro h
    exact hdistinct (congrArg Fin.val h)
  simp [hne]

theorem excluded_words :
    canonical (2 * p) = none ∧ canonical (2 * p + 1) = none ∧
      rawSize = 2 * p + 2 := by
  norm_num [canonical, p, rawSize]

theorem rejected_raw_words (word : Nat) (hword : word < rawSize) :
    canonical word = none ↔ word = 2 * p ∨ word = 2 * p + 1 := by
  have hsize : rawSize = 2 * p + 2 := excluded_words.2.2
  unfold canonical
  split_ifs with haccepted
  · simp
    omega
  · simp
    omega

end S31.Gadgets.PcsFri.FramedExactWord
