import S31.Gadgets.Functional.Correspondence.ControlGadgetAir

/-!
Value-level completeness for the zero-test, selection and packed inverse
fragment. This constructs honest local witnesses for every defined source
evaluation; the native graph, lookup closure and proof authentication are
separate obligations.
-/

namespace S31.Functional.Correspondence.ControlGadgetCompleteness

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

private theorem scalar_zero_test_complete (x : F) :
    let z := if x = 0 then (1 : F) else 0
    let hint := if x = 0 then (0 : F) else x⁻¹
    S31.Gadgets.Packed.mul (base x) (base hint) = subtract (base 1) (base z) ∧
      S31.Gadgets.Packed.mul (base x) (base z) = base 0 := by
  have h := S31.Gadgets.is_zero_complete x
  rcases h with ⟨hzero, hinverse⟩
  constructor
  · apply Quad.ext <;> simp [S31.Gadgets.Packed.mul, base, subtract, hinverse]
  · apply Quad.ext <;> simp [S31.Gadgets.Packed.mul, base, hzero]

private theorem scalar_select_complete (bit : F) (a b : Quad)
    (hbit : bit = 0 ∨ bit = 1) :
    S31.Gadgets.Packed.add
      (S31.Gadgets.Packed.mul a (subtract (base 1) (base bit)))
      (S31.Gadgets.Packed.mul b (base bit)) =
      if bit = 0 then a else b := by
  rcases hbit with hb | hb
  · subst bit
    ext <;> simp [S31.Gadgets.Packed.add, S31.Gadgets.Packed.mul, base, subtract]
  · subst bit
    ext <;> simp [S31.Gadgets.Packed.add, S31.Gadgets.Packed.mul, base, subtract]

/-- For every source input whose selected four lanes are nonzero, there are
concrete local witnesses satisfying the emitted zero-test, packed selection,
and full active inverse equations. This is independent of the compiler's
address/row schedule and the STARK proof system. -/
theorem control_equations_complete (x : F) (a b : Quad)
    (hselected : ∀ i : Fin 4,
      coord (if x = 0 then b else a) i ≠ 0) :
    ∃ (zeroHint z selected inverse : Quad),
      S31.Gadgets.Packed.mul (base x) zeroHint = subtract (base 1) z ∧
      S31.Gadgets.Packed.mul (base x) z = base 0 ∧
      selected = S31.Gadgets.Packed.add
        (S31.Gadgets.Packed.mul a (subtract (base 1) z))
        (S31.Gadgets.Packed.mul b z) ∧
      selected = (if x = 0 then b else a) ∧
      pointwise selected inverse = mask 4 := by
  let bit : F := if x = 0 then 1 else 0
  let z := base bit
  let selected := if x = 0 then b else a
  let inverse := honestInverse 4 selected
  refine ⟨base (if x = 0 then 0 else x⁻¹), z, selected, inverse, ?_, ?_, ?_, rfl, ?_⟩
  · exact (scalar_zero_test_complete x).1
  · exact (scalar_zero_test_complete x).2
  · have hbit : bit = 0 ∨ bit = 1 := by
      unfold bit
      split_ifs <;> simp
    have h := scalar_select_complete bit a b hbit
    simpa [bit, z, selected] using h.symm
  · apply inverse_active_complete 4 selected
    intro i _
    exact hselected i

/-- The local equations have a witness exactly when the source inversion is
defined on the selected branch. The converse quantifies over *all* possible
zero hints and inverse hints; it does not assume the honest witness builder. -/
theorem control_equations_iff_defined (x : F) (a b : Quad) :
    (∃ (zeroHint z selected inverse : Quad),
      S31.Gadgets.Packed.mul (base x) zeroHint = subtract (base 1) z ∧
      S31.Gadgets.Packed.mul (base x) z = base 0 ∧
      selected = S31.Gadgets.Packed.add
        (S31.Gadgets.Packed.mul a (subtract (base 1) z))
        (S31.Gadgets.Packed.mul b z) ∧
      pointwise selected inverse = mask 4) ↔
      ∀ i : Fin 4, coord (if x = 0 then b else a) i ≠ 0 := by
  constructor
  · rintro ⟨zeroHint, z, selected, inverse, hproduct, hzero, hselect, hinverse⟩ i
    have hz := ControlGadgetAir.zero_equations x zeroHint z hproduct hzero
    let bit : F := if x = 0 then 1 else 0
    have hcomp : subtract (base 1) z = base (1 - bit) := by
      rw [hz]
      ext <;> simp [bit, subtract, base]
    have hbit : bit = 0 ∨ bit = 1 := by
      unfold bit
      split_ifs <;> simp
    have hs : selected = if bit = 0 then a else b := by
      apply ControlGadgetAir.select_equation bit a b selected hbit
      simpa [bit, hz, hcomp] using hselect
    have htarget : (if bit = 0 then a else b) = if x = 0 then b else a := by
      by_cases hx : x = 0 <;> simp [bit, hx]
    have hactive : i.val < 4 := i.isLt
    have hnonzero := (inverse_active_sound 4 selected inverse i hactive hinverse).1
    simpa [hs, htarget] using hnonzero
  · intro h
    obtain ⟨zeroHint, z, selected, inverse, hproduct, hzero, hselect, _, hinverse⟩ :=
      control_equations_complete x a b h
    exact ⟨zeroHint, z, selected, inverse, hproduct, hzero, hselect, hinverse⟩

end S31.Functional.Correspondence.ControlGadgetCompleteness
