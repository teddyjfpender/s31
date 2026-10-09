import S31.Gadgets.Air.GateLookup
import S31.Gadgets.Air.SimdChunks

namespace S31.Gadgets.Air.EqRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup

/-- The Eq component contributes two Gate uses carrying one shared trace word.
There is no separate Eq polynomial: its force comes from the global lookup. -/
structure EqRow where
  leftAddress : Nat
  rightAddress : Nat
  value : Quad

def EqRow.uses (r : EqRow) : List Event :=
  [(r.leftAddress, r.value), (r.rightAddress, r.value)]

def balancedEq (rows : List EqRow) (externalUses produced : List Event) : Prop :=
  (rows.flatMap EqRow.uses ++ externalUses).Perm produced

theorem eq_row_sound (rows : List EqRow)
    (externalUses produced : List Event)
    (r : EqRow) (hr : r ∈ rows)
    (hbalance : balancedEq rows externalUses produced)
    (hunique : uniqueProduced produced)
    (left right : Quad)
    (hl : (r.leftAddress, left) ∈ produced)
    (hright : (r.rightAddress, right) ∈ produced) :
    left = right := by
  have hreadLeft : (r.leftAddress, r.value) ∈
      rows.flatMap EqRow.uses ++ externalUses := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨r, hr, by simp [EqRow.uses]⟩
  have hreadRight : (r.rightAddress, r.value) ∈
      rows.flatMap EqRow.uses ++ externalUses := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨r, hr, by simp [EqRow.uses]⟩
  have hleft : r.value = left :=
    hunique r.leftAddress r.value left (hbalance.mem_iff.mp hreadLeft) hl
  have hright : r.value = right :=
    hunique r.rightAddress r.value right (hbalance.mem_iff.mp hreadRight) hright
  exact hleft.symm.trans hright

/-- The short final SIMD equality path emits subtraction, a pointwise active
mask and an Eq row. The Eq row's lookup has to bind `masked` to zero. -/
def acceptsPartialEq (active : Nat) (left right : Quad) : Prop :=
  ∃ difference masked : Quad,
    accepts (encode .sub) left right difference ∧
    accepts (encode .pointwiseMul) difference (mask active) masked ∧
    masked = base 0

theorem coord_subtract (left right : Quad) (i : Fin 4) :
    coord (subtract left right) i = coord left i - coord right i := by
  fin_cases i <;> rfl

theorem acceptsPartialEq_iff (active : Nat) (left right : Quad) :
    acceptsPartialEq active left right ↔
      ∀ i : Fin 4, i.val < active → coord left i = coord right i := by
  constructor
  · rintro ⟨difference, masked, hd, hm, hz⟩ i hi
    have hd' := (accepts_encoded .sub left right difference).mp hd
    have hm' := (accepts_encoded .pointwiseMul difference (mask active) masked).mp hm
    have hcoord := congrArg (fun q => coord q i) hz
    rw [hm', hd'] at hcoord
    simp [evaluate, coord_pointwise, coord_mask, hi,
      coord_subtract, base] at hcoord
    have hzero : coord (⟨0, 0, 0, 0⟩ : Quad) i = 0 := by
      fin_cases i <;> rfl
    rw [hzero] at hcoord
    exact sub_eq_zero.mp hcoord
  · intro h
    let difference := subtract left right
    let masked := Packed.pointwise difference (mask active)
    refine ⟨difference, masked,
      (accepts_encoded .sub _ _ _).mpr rfl,
      (accepts_encoded .pointwiseMul _ _ _).mpr rfl, ?_⟩
    have hcoord : ∀ i : Fin 4, coord masked i = 0 := by
      intro i
      simp only [masked, coord_pointwise, coord_mask]
      by_cases hi : i.val < active
      · simp [hi, difference, coord_subtract, h i hi]
      · simp [hi]
    apply Quad.ext
    · simpa [coord, base] using hcoord ⟨0, by decide⟩
    · simpa [coord, base] using hcoord ⟨1, by decide⟩
    · simpa [coord, base] using hcoord ⟨2, by decide⟩
    · simpa [coord, base] using hcoord ⟨3, by decide⟩

/-- Combine the final short-word arithmetic rows with the Eq component's
two Gate uses. Exact lookup closure supplies the zero assertion. -/
theorem partial_eq_sound_of_lookup
    (active : Nat) (left right difference masked : Quad)
    (hsub : accepts (encode .sub) left right difference)
    (hmask : accepts (encode .pointwiseMul)
      difference (mask active) masked)
    (rows : List EqRow) (externalUses produced : List Event)
    (r : EqRow) (hr : r ∈ rows)
    (hbalance : balancedEq rows externalUses produced)
    (hunique : uniqueProduced produced)
    (hmasked : (r.leftAddress, masked) ∈ produced)
    (hzero : (r.rightAddress, base 0) ∈ produced) :
    ∀ i : Fin 4, i.val < active → coord left i = coord right i := by
  have heq := eq_row_sound rows externalUses produced r hr hbalance
    hunique masked (base 0) hmasked hzero
  exact (acceptsPartialEq_iff active left right).mp
    ⟨difference, masked, hsub, hmask, heq⟩

/-- Post-lookup meaning of a compiler equality chunk. Full words use one Eq
row whose value is joined by Gate; short words use the masked schedule. -/
def acceptsEqChunk (active : Nat) (left right : Quad) : Prop :=
  if active = 4 then left = right else acceptsPartialEq active left right

theorem acceptsEqChunk_iff (active : Nat) (hactive : active ≤ 4)
    (left right : Quad) :
    acceptsEqChunk active left right ↔
      ∀ i : Fin 4, i.val < active → coord left i = coord right i := by
  by_cases hfull : active = 4
  · subst active
    simp only [acceptsEqChunk, ↓reduceIte]
    constructor
    · intro heq i _; rw [heq]
    · intro h
      apply Quad.ext
      · simpa [coord] using h ⟨0, by decide⟩ (by decide)
      · simpa [coord] using h ⟨1, by decide⟩ (by decide)
      · simpa [coord] using h ⟨2, by decide⟩ (by decide)
      · simpa [coord] using h ⟨3, by decide⟩ (by decide)
  · simp only [acceptsEqChunk, hfull, ↓reduceIte]
    exact acceptsPartialEq_iff active left right

def packedEqRows {n : Nat} (left right : Fin n → S31.M31)
    (tailLeft tailRight : Nat → Fin 4 → S31.M31) : Prop :=
  ∀ block : Fin ((n + 3) / 4),
    acceptsEqChunk (min 4 (n - 4 * block.val))
      (packM31 (SimdChunks.chunk4 left block.val (tailLeft block.val)))
      (packM31 (SimdChunks.chunk4 right block.val (tailRight block.val)))

theorem packedEqRows_iff {n : Nat} (left right : Fin n → S31.M31)
    (tailLeft tailRight : Nat → Fin 4 → S31.M31) :
    packedEqRows left right tailLeft tailRight ↔
      ∀ j : Fin n, left j = right j := by
  constructor
  · intro hrows j
    have hblock : j.val / 4 < (n + 3) / 4 := by omega
    let block : Fin ((n + 3) / 4) := ⟨j.val / 4, hblock⟩
    have hlimb : j.val % 4 < 4 := by omega
    let limb : Fin 4 := ⟨j.val % 4, hlimb⟩
    have hindex : block.val * 4 + limb.val < n := by
      dsimp [block, limb]
      omega
    have hactive : limb.val < min 4 (n - 4 * block.val) := by
      dsimp [block, limb]
      omega
    have hcoord := (acceptsEqChunk_iff
      (min 4 (n - 4 * block.val)) (Nat.min_le_left _ _)
      _ _).mp (hrows block) limb hactive
    rw [coord_packM31, coord_packM31,
      SimdChunks.chunk4_active left block.val (tailLeft block.val) limb hindex,
      SimdChunks.chunk4_active right block.val (tailRight block.val) limb hindex]
      at hcoord
    have hsame :
        (⟨block.val * 4 + limb.val, hindex⟩ : Fin n) = j := by
      apply Fin.ext
      dsimp [block, limb]
      omega
    rw [hsame] at hcoord
    exact S31.Field.toZMod_injective hcoord
  · intro h block
    apply (acceptsEqChunk_iff
      (min 4 (n - 4 * block.val)) (Nat.min_le_left _ _) _ _).mpr
    intro i hi
    have hindex : block.val * 4 + i.val < n := by omega
    rw [coord_packM31, coord_packM31,
      SimdChunks.chunk4_active left block.val (tailLeft block.val) i hindex,
      SimdChunks.chunk4_active right block.val (tailRight block.val) i hindex]
    exact congrArg S31.Field.toZMod (h ⟨block.val * 4 + i.val, hindex⟩)

theorem two_lane_honest :
    acceptsPartialEq 2 ⟨2, 3, 71, 99⟩ ⟨2, 3, 5, 6⟩ := by
  rw [acceptsPartialEq_iff]
  intro i hi
  fin_cases i <;> simp_all [coord]

theorem two_lane_forged_rejected :
    ¬ acceptsPartialEq 2 ⟨2, 3, 71, 99⟩ ⟨2, 4, 5, 6⟩ := by
  intro h
  have hv := (acceptsPartialEq_iff _ _ _).mp h ⟨1, by decide⟩ (by decide)
  have hbad : (3 : F) = 4 := by simpa [coord] using hv
  exact (by decide : (3 : F) ≠ 4) hbad

theorem honest_eq_balanced :
    balancedEq [⟨7, 8, base 5⟩] []
      [(7, base 5), (8, base 5)] := by
  exact List.Perm.refl _

theorem forged_eq_unbalanced :
    ¬ balancedEq [⟨7, 8, base 5⟩] []
      [(7, base 5), (8, base 6)] := by
  intro h
  have huse : (8, base 5) ∈
      [⟨7, 8, base 5⟩].flatMap EqRow.uses ++ ([] : List Event) := by
    decide
  have hnot : (8, base 5) ∉
      ([(7, base 5), (8, base 6)] : List Event) := by decide
  exact hnot (h.mem_iff.mp huse)

end S31.Gadgets.Air.EqRows
