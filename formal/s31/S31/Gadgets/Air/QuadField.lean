import S31.Gadgets.Packed
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

/-!
Finite-field facts needed to turn an untrusted QM31 self-product row into
a Boolean selector statement. The tower extension proof is built from
explicit nonsquare obligations in M31, not from witness hints.
-/

namespace S31.Gadgets.Air.QuadField

open S31.Gadgets.Packed

/-- Five is not a square in M31, by quadratic reciprocity with five. -/
theorem five_nonsquare (x : F) : x * x ≠ 5 := by
  intro h
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hrec := legendreSym.quadratic_reciprocity_one_mod_four
    (p := 5) (q := 2147483647) (by decide) (by decide)
  have hsmall : legendreSym 5 2147483647 = -1 := by decide
  have hsymbol : legendreSym 2147483647 (5 : ℤ) = -1 :=
    hrec.trans hsmall
  have hnot : ¬IsSquare (5 : F) :=
    (legendreSym.eq_neg_one_iff (p := 2147483647) (a := (5 : ℤ))).mp hsymbol
  apply hnot
  exact (isSquare_iff_exists_sq (5 : F)).mpr
    ⟨x, by simpa [pow_two] using h.symm⟩

/-- Since M31 has cardinality three modulo four, minus one is not a square. -/
theorem neg_one_nonsquare (x : F) : x * x ≠ -1 := by
  intro h
  have hmod := ZMod.mod_four_ne_three_of_sq_eq_neg_one
    (p := 2147483647) (by simpa [pow_two] using h)
  exact hmod (by decide)

abbrev CM := QuadraticAlgebra F (-1) 0

theorem cm_irreducible : Fact (∀ r : F, r ^ 2 ≠ -1 + 0 * r) :=
  ⟨by intro r; simpa [pow_two] using neg_one_nonsquare r⟩

attribute [instance] cm_irreducible

def twoPlusI : CM := ⟨2, 1⟩

theorem twoPlusI_norm : QuadraticAlgebra.norm twoPlusI = (5 : F) := by
  simp [QuadraticAlgebra.norm_def, twoPlusI]
  ring

theorem twoPlusI_nonsquare (x : CM) : x * x ≠ twoPlusI := by
  intro h
  have hnorm := congrArg (QuadraticAlgebra.norm : CM →* F) h
  have hfive : (QuadraticAlgebra.norm x) *
      (QuadraticAlgebra.norm x) = (5 : F) := by
    simpa [twoPlusI_norm] using hnorm
  exact five_nonsquare _ hfive

abbrev QM := QuadraticAlgebra CM twoPlusI 0

theorem qm_irreducible :
    Fact (∀ r : CM, r ^ 2 ≠ twoPlusI + 0 * r) :=
  ⟨by intro r; simpa [pow_two] using twoPlusI_nonsquare r⟩

attribute [instance] qm_irreducible

/-- The AIR's four coordinate multiplication is the nested quadratic field
multiplication in the `(1,i,u,iu)` basis. -/
def toQM (x : Quad) : QM :=
  ⟨(⟨x.a, x.b⟩ : CM), (⟨x.c, x.d⟩ : CM)⟩

theorem toQM_injective : Function.Injective toQM := by
  intro x y h
  apply Quad.ext
  · simpa [toQM] using congrArg (fun q : QM => q.re.re) h
  · simpa [toQM] using congrArg (fun q : QM => q.re.im) h
  · simpa [toQM] using congrArg (fun q : QM => q.im.re) h
  · simpa [toQM] using congrArg (fun q : QM => q.im.im) h

theorem toQM_base_zero : toQM (base 0) = 0 := by
  ext <;> simp [toQM, base]

theorem toQM_base_one : toQM (base 1) = 1 := by
  rfl

theorem toQM_mul (x y : Quad) :
    toQM (Packed.mul x y) = toQM x * toQM y := by
  ext <;>
    dsimp [toQM, Packed.mul, twoPlusI,
      QuadraticAlgebra.instMul] <;>
    ring

/-- A satisfying QM31 self-product row has exactly the two Boolean values,
even for an arbitrary untrusted four-coordinate witness. -/
theorem self_product_iff (x : Quad) :
    Packed.mul x x = x ↔ x = base 0 ∨ x = base 1 := by
  constructor
  · intro h
    have hbit : S31.Gadgets.bit (toQM x) := by
      unfold S31.Gadgets.bit
      rw [← toQM_mul]
      exact congrArg toQM h
    rcases (S31.Gadgets.bit_sound_complete (toQM x)).mp hbit with hz | ho
    · exact Or.inl (toQM_injective (by simpa [toQM_base_zero] using hz))
    · exact Or.inr (toQM_injective (by simpa [toQM_base_one] using ho))
  · rintro (rfl | rfl) <;> simp [Packed.mul, base]

end S31.Gadgets.Air.QuadField
