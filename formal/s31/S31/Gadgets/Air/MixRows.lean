import S31.Gadgets.Air.SumRows

namespace S31.Gadgets.Air.MixRows

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

def broadcastFactor : Quad := ⟨1, 1, 1, 1⟩

theorem mul_base_broadcast (value : F) :
    Packed.mul (base value) broadcastFactor =
      ⟨value, value, value, value⟩ := by
  ext <;> simp [Packed.mul, base, broadcastFactor]

theorem coord_add_broadcast (values : Fin 4 → S31.M31)
    (value : F) (i : Fin 4) :
    coord (Packed.add (packM31 values)
      ⟨value, value, value, value⟩) i =
      S31.Field.toZMod (values i) + value := by
  fin_cases i <;> rfl

/-- The compiler's four-lane `mix4`: sumLanes, QM31 broadcast multiplication,
and one packed addition. Intermediate values are arbitrary row witnesses. -/
def mix4Rows (input claimed : Fin 4 → S31.M31) : Prop :=
  ∃ total : S31.M31,
    SumRows.sumLanesRows (List.ofFn input) total ∧
    ∃ broadcast output : Quad,
      accepts (encode .mul)
        (base (S31.Field.toZMod total)) broadcastFactor broadcast ∧
      accepts (encode .add) (packM31 input) broadcast output ∧
      ∀ i : Fin 4,
        coord output i = S31.Field.toZMod (claimed i)

theorem mix4Rows_iff (input claimed : Fin 4 → S31.M31) :
    mix4Rows input claimed ↔
      ∀ i : Fin 4,
        claimed i = input i + (List.ofFn input).foldl (· + ·) 0 := by
  constructor
  · rintro ⟨total, hsum, broadcast, output, hb, ho, hclaim⟩
    have hne : List.ofFn input ≠ [] := by simp
    have hsum' := (SumRows.sumLanesRows_iff (List.ofFn input)
      total hne).mp hsum
    rw [SumRows.fieldSumList_eq_foldl] at hsum'
    have htotal : total = (List.ofFn input).foldl (· + ·) 0 :=
      S31.Field.toZMod_injective hsum'
    have hb' := (accepts_encoded .mul
      (base (S31.Field.toZMod total)) broadcastFactor broadcast).mp hb
    have ho' := (accepts_encoded .add
      (packM31 input) broadcast output).mp ho
    intro i
    have hvalue : S31.Field.toZMod (claimed i) =
        S31.Field.toZMod (input i) + S31.Field.toZMod total := by
      rw [← hclaim i, ho', hb']
      simpa [evaluate, mul_base_broadcast] using
        coord_add_broadcast input (S31.Field.toZMod total) i
    have hsource : claimed i = input i + total :=
      S31.Field.toZMod_injective (by
        rw [S31.Field.toZMod_add]
        exact hvalue)
    simpa [htotal] using hsource
  · intro h
    let total := (List.ofFn input).foldl (· + ·) 0
    have hne : List.ofFn input ≠ [] := by simp
    have hsum : SumRows.sumLanesRows (List.ofFn input) total := by
      apply (SumRows.sumLanesRows_iff (List.ofFn input)
        total hne).mpr
      exact (SumRows.fieldSumList_eq_foldl _).symm
    let broadcast := evaluate .mul
      (base (S31.Field.toZMod total)) broadcastFactor
    let output := evaluate .add (packM31 input) broadcast
    refine ⟨total, hsum, broadcast, output,
      honest_row _ _ _, honest_row _ _ _, ?_⟩
    intro i
    have hclaim : S31.Field.toZMod (claimed i) =
        S31.Field.toZMod (input i) + S31.Field.toZMod total := by
      rw [h i, S31.Field.toZMod_add]
    rw [hclaim]
    simpa [output, broadcast, evaluate, mul_base_broadcast] using
      coord_add_broadcast input (S31.Field.toZMod total) i

/-- The circuit rows implement the executable `mix4` step used inside
normalized repeat bodies. -/
theorem mix4Rows_iff_applyStep (input claimed : Fin 4 → S31.M31) :
    mix4Rows input claimed ↔
      S31.applyStep (List.ofFn input) .mix4 = List.ofFn claimed := by
  rw [mix4Rows_iff]
  simp only [S31.applyStep]
  simp
  constructor
  · intro h
    exact ⟨(h ⟨0, by decide⟩).symm,
      (h ⟨1, by decide⟩).symm,
      (h ⟨2, by decide⟩).symm,
      (h ⟨3, by decide⟩).symm⟩
  · rintro ⟨h0, h1, h2, h3⟩ i
    fin_cases i
    · simpa using h0.symm
    · simpa using h1.symm
    · simpa using h2.symm
    · simpa using h3.symm

end S31.Gadgets.Air.MixRows
