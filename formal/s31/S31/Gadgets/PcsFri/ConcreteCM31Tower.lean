import S31.Gadgets.PcsFri.NativeTowerFormulas
import S31.Gadgets.PcsFri.PairedDenominator

/-!
Concrete coefficient bridge for the M31-sized CM31 pair representation.
The modeled pair has exactly `p²` elements, and no pair squares to `2+i`.
This discharges two explicit assumptions of the guarded OOD counting and
quotient-denominator lemmas at the level of the algebraic pair model. It does
not identify this model with Zig's compiled CM31 operations.
-/

namespace S31.Gadgets.PcsFri.ConcreteCM31Tower

open NativeTowerFormulas

variable {K : Type*}

def cmEquiv (K : Type*) : CM K ≃ K × K where
  toFun x := (x.a, x.b)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by intro x; cases x; rfl
  right_inv := by intro p; cases p; rfl

noncomputable instance [Fintype K] : Fintype (CM K) :=
  Fintype.ofEquiv (K × K) (cmEquiv K).symm

theorem card_cm [Fintype K] :
    Fintype.card (CM K) = Fintype.card K ^ 2 := by
  rw [Fintype.card_congr (cmEquiv K), Fintype.card_prod, pow_two]

theorem card_cm31 :
    Fintype.card (CM S31.Field.F) = 2147483647 ^ 2 := by
  simpa [S31.Field.F] using (card_cm (K := S31.Field.F)).trans
    (congrArg (· ^ 2) (ZMod.card 2147483647))

theorem imaginary_unit_square [CommRing K] :
    cmSquare (⟨0, 1⟩ : CM K) = (⟨-1, 0⟩ : CM K) := by
  ext <;> simp [cmSquare]

/-- The actual M31 modulus and `i²=-1` coefficient formula rule out a
square root of `R=2+i` in the modeled CM31 pair. -/
theorem r_nonsquare_cm31 (x : CM S31.Field.F) :
    cmSquare x ≠ (r : CM S31.Field.F) := by
  intro h
  have hreal := congrArg CM.a h
  have himag := congrArg CM.b h
  simp only [cmSquare, r] at hreal himag
  have htwo : (2 : S31.Field.F) * x.a * x.b = 1 := by
    linear_combination himag
  exact PairedDenominator.tower_parameter_no_pair_square_root
    ⟨x.a, x.b, hreal, htwo⟩

end S31.Gadgets.PcsFri.ConcreteCM31Tower
