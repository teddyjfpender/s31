import S31.Gadgets.Air.BitRows
import S31.Gadgets.Air.SimdChunks

namespace S31.Gadgets.Air.InverseRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

/-- `inverseLanes` emits a pointwise multiply, a subtraction from the
active-lane mask, and an anchor zero assertion for each packed word. -/
def acceptsInverse (active : Nat) (input inverse : Quad) : Prop :=
  ∃ product difference : Quad,
    accepts (encode .pointwiseMul) input inverse product ∧
    accepts (encode .sub) product (mask active) difference ∧
    BitRows.acceptsZero difference

theorem acceptsInverse_iff (active : Nat) (input inverse : Quad) :
    acceptsInverse active input inverse ↔
      inverseConstraint active input inverse := by
  constructor
  · rintro ⟨product, difference, hp, hd, hz⟩
    have hp' := (accepts_encoded .pointwiseMul input inverse product).mp hp
    have hd' := (accepts_encoded .sub product (mask active) difference).mp hd
    have hz' := (BitRows.acceptsZero_iff difference).mp hz
    rw [hd', hp'] at hz'
    unfold inverseConstraint
    apply Quad.ext
    · exact sub_eq_zero.mp
        (by simpa [evaluate, subtract, base] using congrArg Quad.a hz')
    · exact sub_eq_zero.mp
        (by simpa [evaluate, subtract, base] using congrArg Quad.b hz')
    · exact sub_eq_zero.mp
        (by simpa [evaluate, subtract, base] using congrArg Quad.c hz')
    · exact sub_eq_zero.mp
        (by simpa [evaluate, subtract, base] using congrArg Quad.d hz')
  · intro hconstraint
    let product := evaluate .pointwiseMul input inverse
    let difference := evaluate .sub product (mask active)
    refine ⟨product, difference,
      honest_row _ _ _, honest_row _ _ _, ?_⟩
    apply (BitRows.acceptsZero_iff difference).mpr
    simp [difference, product, evaluate, subtract,
      inverseConstraint] at hconstraint ⊢
    rw [hconstraint]
    ext <;> simp [base]

/-- Every active M31 lane is nonzero and the claimed inverse is unique,
even when the row's auxiliary wires are adversarially chosen. -/
theorem acceptsInverse_active_sound (active : Nat)
    (input inverse : Quad) (i : Fin 4) (hi : i.val < active)
    (h : acceptsInverse active input inverse) :
    coord input i ≠ 0 ∧
      coord inverse i = (coord input i)⁻¹ :=
  inverse_active_sound active input inverse i hi
    ((acceptsInverse_iff active input inverse).mp h)

theorem acceptsInverse_complete (active : Nat) (input : Quad)
    (h : ∀ i : Fin 4, i.val < active → coord input i ≠ 0) :
    acceptsInverse active input (honestInverse active input) :=
  (acceptsInverse_iff active input _).mpr
    (inverse_active_complete active input h)

theorem zero_active_lane_rejected (input inverse : Quad)
    (hz : input.a = 0) :
    ¬ acceptsInverse 1 input inverse := by
  intro h
  have hnonzero := (acceptsInverse_active_sound 1 input inverse
    ⟨0, by decide⟩ (by decide) h).1
  exact hnonzero (by simpa [coord] using hz)

/-- One constrained inverse word for each four-lane source chunk. Inactive
input padding is arbitrary but its product with the witness is forced zero. -/
def packedInverseRows {n : Nat}
    (source claimed : Fin n → S31.M31)
    (tail : Nat → Fin 4 → S31.M31) : Prop :=
  ∀ block : Fin ((n + 3) / 4), ∃ inverse : Quad,
    acceptsInverse (min 4 (n - 4 * block.val))
      (packM31 (SimdChunks.chunk4 source block.val (tail block.val)))
      inverse ∧
    ∀ (i : Fin 4) (hi : block.val * 4 + i.val < n),
      coord inverse i =
        S31.Field.toZMod (claimed ⟨block.val * 4 + i.val, hi⟩)

theorem packedInverseRows_sound {n : Nat}
    (source claimed : Fin n → S31.M31)
    (tail : Nat → Fin 4 → S31.M31)
    (hrows : packedInverseRows source claimed tail) :
    ∀ j : Fin n, source j ≠ 0 ∧
      claimed j = S31.Field.inverse (source j) := by
  intro j
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
  obtain ⟨inverse, hrow, hclaim⟩ := hrows block
  have hvalue := acceptsInverse_active_sound
    (min 4 (n - 4 * block.val))
    (packM31 (SimdChunks.chunk4 source block.val
      (tail block.val))) inverse limb hactive hrow
  have hsource : coord
      (packM31 (SimdChunks.chunk4 source block.val
        (tail block.val))) limb =
      S31.Field.toZMod
        (source ⟨block.val * 4 + limb.val, hindex⟩) := by
    rw [coord_packM31]
    exact congrArg S31.Field.toZMod
      (SimdChunks.chunk4_active source block.val
        (tail block.val) limb hindex)
  have hsame :
      (⟨block.val * 4 + limb.val, hindex⟩ : Fin n) = j := by
    apply Fin.ext
    dsimp [block, limb]
    omega
  have hnz : source j ≠ 0 := by
    intro hz
    apply hvalue.1
    simp [hsource, hsame, hz, S31.Field.toZMod_zero]
  have hfield : S31.Field.toZMod (S31.Field.inverse (source j)) =
      (S31.Field.toZMod (source j))⁻¹ := by
    simp [S31.Field.inverse, S31.Field.to_from]
  have heq : S31.Field.toZMod (claimed j) =
      S31.Field.toZMod (S31.Field.inverse (source j)) := by
    rw [hfield, ← hsame, ← hclaim limb hindex,
      hvalue.2, hsource]
  exact ⟨hnz, S31.Field.toZMod_injective heq⟩

theorem packedInverseRows_complete {n : Nat}
    (source claimed : Fin n → S31.M31)
    (tail : Nat → Fin 4 → S31.M31)
    (h : ∀ j : Fin n, source j ≠ 0 ∧
      claimed j = S31.Field.inverse (source j)) :
    packedInverseRows source claimed tail := by
  intro block
  let input := packM31
    (SimdChunks.chunk4 source block.val (tail block.val))
  let active := min 4 (n - 4 * block.val)
  have hnonzero : ∀ i : Fin 4, i.val < active →
      coord input i ≠ 0 := by
    intro i hi
    have hindex : block.val * 4 + i.val < n := by
      dsimp [active] at hi
      omega
    have hc : coord input i =
        S31.Field.toZMod
          (source ⟨block.val * 4 + i.val, hindex⟩) := by
      rw [coord_packM31]
      exact congrArg S31.Field.toZMod
        (SimdChunks.chunk4_active source block.val
          (tail block.val) i hindex)
    rw [hc]
    intro hzero
    have hsource : source ⟨block.val * 4 + i.val, hindex⟩ = 0 :=
      S31.Field.toZMod_injective
        (by simpa [S31.Field.toZMod_zero] using hzero)
    exact (h _).1 hsource
  let inverse := honestInverse active input
  have hrow : acceptsInverse active input inverse :=
    acceptsInverse_complete active input hnonzero
  refine ⟨inverse, hrow, ?_⟩
  intro i hi
  have hactive : i.val < active := by
    dsimp [active]
    omega
  have hvalue := (acceptsInverse_active_sound active input inverse
    i hactive hrow).2
  have hinput : coord input i =
      S31.Field.toZMod
        (source ⟨block.val * 4 + i.val, hi⟩) := by
    rw [coord_packM31]
    exact congrArg S31.Field.toZMod
      (SimdChunks.chunk4_active source block.val
        (tail block.val) i hi)
  calc
    coord inverse i = (coord input i)⁻¹ := hvalue
    _ = (S31.Field.toZMod
      (source ⟨block.val * 4 + i.val, hi⟩))⁻¹ := by rw [hinput]
    _ = S31.Field.toZMod
      (claimed ⟨block.val * 4 + i.val, hi⟩) := by
        rw [(h _).2]
        simp [S31.Field.inverse, S31.Field.to_from]

theorem packedInverseRows_iff {n : Nat}
    (source claimed : Fin n → S31.M31)
    (tail : Nat → Fin 4 → S31.M31) :
    packedInverseRows source claimed tail ↔
      ∀ j : Fin n, source j ≠ 0 ∧
        claimed j = S31.Field.inverse (source j) :=
  ⟨packedInverseRows_sound source claimed tail,
   packedInverseRows_complete source claimed tail⟩

end S31.Gadgets.Air.InverseRows
