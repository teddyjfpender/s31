import S31.Gadgets.PcsFri.CM31FieldInstance

/-!
Checked inverse algebra for the two quadratic towers used by native OOD
sampling. The Zig source guard pins the denominator and conjugate formulas.
This file proves the formulas are true inverses under the explicit nonsquare
tower assumption and nonzero input; it does not interpret Zig execution.
-/

namespace S31.Gadgets.PcsFri.NativeTowerInverse

open PairedTowerCircle

variable {K : Type*} [Field K]

omit [Field K] in
@[ext] theorem pair_ext {x y : Pair K}
    (h0 : x.c0 = y.c0) (h1 : x.c1 = y.c1) : x = y := by
  cases x with
  | mk x0 x1 =>
    cases y with
    | mk y0 y1 =>
      cases h0
      cases h1
      rfl

def norm (d : K) (x : Pair K) : K := x.c0 ^ 2 - d * x.c1 ^ 2

def mul (d : K) (x y : Pair K) : Pair K :=
  ⟨x.c0 * y.c0 + d * x.c1 * y.c1,
    x.c0 * y.c1 + x.c1 * y.c0⟩

/-- The checked native inverse path first rejects zero, then divides the
quadratic conjugate by its norm. -/
def inverse (d : K) (x : Pair K) : Pair K :=
  ⟨x.c0 * (norm d x)⁻¹, -x.c1 * (norm d x)⁻¹⟩

theorem norm_ne_zero (d : K) (hd : ∀ t : K, t ^ 2 ≠ d)
    (x : Pair K) (hx : x.c0 ≠ 0 ∨ x.c1 ≠ 0) : norm d x ≠ 0 := by
  intro hn
  rcases hx with h0 | h1
  · by_cases h1 : x.c1 = 0
    · have hsq : x.c0 ^ 2 = 0 := by simpa [norm, h1] using hn
      exact h0 (eq_zero_of_pow_eq_zero hsq)
    · have hsq : (x.c0 / x.c1) ^ 2 = d := by
        dsimp [norm] at hn
        field_simp [h1]
        linear_combination hn
      exact hd _ hsq
  · have hsq : (x.c0 / x.c1) ^ 2 = d := by
      dsimp [norm] at hn
      field_simp [h1]
      linear_combination hn
    exact hd _ hsq

theorem mul_inverse_eq_one (d : K) (x : Pair K)
    (hn : norm d x ≠ 0) :
    mul d x (inverse d x) = (one : Pair K) := by
  change x.c0 ^ 2 - d * x.c1 ^ 2 ≠ 0 at hn
  apply pair_ext
  · change x.c0 * (x.c0 * (x.c0 ^ 2 - d * x.c1 ^ 2)⁻¹) +
        d * x.c1 * (-x.c1 * (x.c0 ^ 2 - d * x.c1 ^ 2)⁻¹) = 1
    field_simp [hn]
    ring
  · change x.c0 * (-x.c1 * (x.c0 ^ 2 - d * x.c1 ^ 2)⁻¹) +
        x.c1 * (x.c0 * (x.c0 ^ 2 - d * x.c1 ^ 2)⁻¹) = 0
    ring

theorem inverse_mul_eq_one (d : K) (x : Pair K)
    (hn : norm d x ≠ 0) :
    mul d (inverse d x) x = (one : Pair K) := by
  change x.c0 ^ 2 - d * x.c1 ^ 2 ≠ 0 at hn
  apply pair_ext
  · change (x.c0 * (x.c0 ^ 2 - d * x.c1 ^ 2)⁻¹) * x.c0 +
        d * (-x.c1 * (x.c0 ^ 2 - d * x.c1 ^ 2)⁻¹) * x.c1 = 1
    field_simp [hn]
    ring
  · change (x.c0 * (x.c0 ^ 2 - d * x.c1 ^ 2)⁻¹) * x.c1 +
        (-x.c1 * (x.c0 ^ 2 - d * x.c1 ^ 2)⁻¹) * x.c0 = 0
    ring

/-- The native `CM31.inv` denominator is the `d=-1` norm. -/
theorem cm31_norm_formula (a b : S31.Field.F) :
    norm (-1 : S31.Field.F) (⟨a, b⟩ : Pair S31.Field.F) =
      a ^ 2 + b ^ 2 := by
  simp [norm]

theorem cm31_inverse_valid (a b : S31.Field.F)
    (h : a ≠ 0 ∨ b ≠ 0) :
    norm (-1 : S31.Field.F) (⟨a, b⟩ : Pair S31.Field.F) ≠ 0 := by
  apply norm_ne_zero (-1) ?_ ⟨a, b⟩ h
  intro t ht
  exact S31.Gadgets.Air.QuadField.neg_one_nonsquare t
    (by simpa [pow_two] using ht)

theorem cm31_inverse_product (a b : S31.Field.F)
    (h : a ≠ 0 ∨ b ≠ 0) :
    mul (-1 : S31.Field.F) (⟨a, b⟩ : Pair S31.Field.F)
      (inverse (-1) ⟨a, b⟩) = PairedTowerCircle.one :=
  mul_inverse_eq_one (-1) ⟨a, b⟩ (cm31_inverse_valid a b h)

/-- The same inverse formula applies to the native QM31 tower over the
modeled CM31 field, with `d=2+i`. -/
theorem qm31_inverse_valid
    (x : Pair CM31FieldInstance.CM31)
    (h : x.c0 ≠ 0 ∨ x.c1 ≠ 0) :
    norm (NativeTowerFormulas.r : CM31FieldInstance.CM31) x ≠ 0 :=
  norm_ne_zero NativeTowerFormulas.r
    CM31FieldInstance.r_nonsquare x h

theorem qm31_inverse_product
    (x : Pair CM31FieldInstance.CM31)
    (h : x.c0 ≠ 0 ∨ x.c1 ≠ 0) :
    mul (NativeTowerFormulas.r : CM31FieldInstance.CM31) x
      (inverse NativeTowerFormulas.r x) = PairedTowerCircle.one :=
  mul_inverse_eq_one NativeTowerFormulas.r x (qm31_inverse_valid x h)

end S31.Gadgets.PcsFri.NativeTowerInverse
