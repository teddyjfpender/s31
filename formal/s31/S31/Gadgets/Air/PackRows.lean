import S31.Gadgets.Air.Qm31Ops

/-!
The six local QM31 operation rows used by SIMD `pack` for exactly four M31
lanes: three extension-basis products and three additions. All six outputs
are arbitrary proof witnesses. The scalar input wires and basis constants
are explicit premises when this theorem is applied to a native circuit.
-/

namespace S31.Gadgets.Air.PackRows

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

def acceptsPack (input : Fin 4 → M31)
    (term1 term2 term3 sum1 sum2 packed : Quad) : Prop :=
  accepts (encode .mul) (unit ⟨1, by decide⟩)
    (base (Field.toZMod (input ⟨1, by decide⟩))) term1 ∧
  accepts (encode .mul) (unit ⟨2, by decide⟩)
    (base (Field.toZMod (input ⟨2, by decide⟩))) term2 ∧
  accepts (encode .mul) (unit ⟨3, by decide⟩)
    (base (Field.toZMod (input ⟨3, by decide⟩))) term3 ∧
  accepts (encode .add)
    (base (Field.toZMod (input ⟨0, by decide⟩))) term1 sum1 ∧
  accepts (encode .add) sum1 term2 sum2 ∧
  accepts (encode .add) sum2 term3 packed

theorem acceptsPack_sound (input : Fin 4 → M31)
    (term1 term2 term3 sum1 sum2 packed : Quad)
    (h : acceptsPack input term1 term2 term3 sum1 sum2 packed) :
    packed = packM31 input := by
  rcases h with ⟨hterm1, hterm2, hterm3, hsum1, hsum2, hpacked⟩
  have ht1 := (accepts_encoded .mul _ _ _).mp hterm1
  have ht2 := (accepts_encoded .mul _ _ _).mp hterm2
  have ht3 := (accepts_encoded .mul _ _ _).mp hterm3
  have hs1 := (accepts_encoded .add _ _ _).mp hsum1
  have hs2 := (accepts_encoded .add _ _ _).mp hsum2
  have hp := (accepts_encoded .add _ _ _).mp hpacked
  rw [hp, hs2, hs1, ht1, ht2, ht3]
  apply Quad.ext <;>
    simp [evaluate, Packed.mul, Packed.add, base, unit, packM31]

/-- Honest intermediary values are accepted by all six rows. -/
theorem acceptsPack_honest (input : Fin 4 → M31) :
    ∃ term1 term2 term3 sum1 sum2,
      acceptsPack input term1 term2 term3 sum1 sum2 (packM31 input) := by
  let t1 := evaluate .mul (unit ⟨1, by decide⟩)
    (base (Field.toZMod (input ⟨1, by decide⟩)))
  let t2 := evaluate .mul (unit ⟨2, by decide⟩)
    (base (Field.toZMod (input ⟨2, by decide⟩)))
  let t3 := evaluate .mul (unit ⟨3, by decide⟩)
    (base (Field.toZMod (input ⟨3, by decide⟩)))
  let s1 := evaluate .add
    (base (Field.toZMod (input ⟨0, by decide⟩))) t1
  let s2 := evaluate .add s1 t2
  refine ⟨t1, t2, t3, s1, s2, ?_⟩
  refine ⟨honest_row _ _ _, honest_row _ _ _, honest_row _ _ _,
    honest_row _ _ _, honest_row _ _ _, ?_⟩
  apply (accepts_encoded .add _ _ _).mpr
  exact (acceptsPack_sound input t1 t2 t3 s1 s2
    (evaluate .add s2 t3)
    ⟨honest_row _ _ _, honest_row _ _ _, honest_row _ _ _,
      honest_row _ _ _, honest_row _ _ _, honest_row _ _ _⟩).symm

end S31.Gadgets.Air.PackRows
