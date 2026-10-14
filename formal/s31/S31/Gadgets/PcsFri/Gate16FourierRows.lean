import S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
import S31.Gadgets.PcsFri.NativeTowerFormulas
import S31.Gadgets.PcsFri.CM31FieldInstance
import S31.Gadgets.PcsFri.CircleLaurentUniqueness
import Mathlib.Tactic

/-!
The exact sixteen storage rows in Gate's smallest source domain. The index
calculation is a transcription of `CanonicCoset.new(4).circleDomain()` followed
by `bitReverseIndex(row, 4)`; it does not assume generator-order correctness.
-/

namespace S31.Gadgets.PcsFri.Gate16FourierRows

open S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
open S31.Gadgets.PcsFri.CircleLaurentDegree
open S31.Gadgets.PcsFri.CircleLaurentUniqueness
open LaurentPolynomial

def rowIndex (row : Fin 16) : CircleIndex :=
  canonicalStorageIndex 4 row.val

theorem rowIndex_injective : Function.Injective rowIndex := by
  decide

def reducedExponent (row : Fin 16) : Nat := (rowIndex row).val / 2 ^ 26

/-- Every canonical row index lies in the subgroup of indices divisible by
2^26. The reduced exponents are odd residues modulo 32. -/
theorem rowIndex_eq_reduced (row : Fin 16) :
    (rowIndex row).val = 2 ^ 26 * reducedExponent row := by
  fin_cases row <;> decide

theorem reducedExponent_lt (row : Fin 16) : reducedExponent row < 32 := by
  have h := (rowIndex row).val_lt
  rw [rowIndex_eq_reduced] at h
  omega

abbrev M31 := S31.Field.F
abbrev Point := M31 × M31

/-- Point certificate for all sixteen native rows, indexed in the exact
bit-reversed storage order. The accompanying native test compares these
constants with `CirclePointIndex.toPoint` and CM31's `x + i*y` encoding at the
pinned stwo-zig submodule commit. This table alone does not refine Zig. -/
def expectedPoint (row : Fin 16) : Point :=
  match row.val with
  | 0 => (1179735656, 1241207368)
  | 1 => (1179735656, 906276279)
  | 2 => (967747991, 906276279)
  | 3 => (967747991, 1241207368)
  | 4 => (1241207368, 967747991)
  | 5 => (1241207368, 1179735656)
  | 6 => (906276279, 1179735656)
  | 7 => (906276279, 967747991)
  | 8 => (1415090252, 2112881577)
  | 9 => (1415090252, 34602070)
  | 10 => (732393395, 34602070)
  | 11 => (732393395, 2112881577)
  | 12 => (2112881577, 732393395)
  | 13 => (2112881577, 1415090252)
  | 14 => (34602070, 1415090252)
  | 15 => (34602070, 732393395)
  | _ => (0, 0)

theorem expectedPoint_injective : Function.Injective expectedPoint := by
  decide

/-- The exact remaining compiler-to-native premise is a per-row equality,
not a global generator-order postulate. -/
theorem nativePoint_injective (nativePoint : CircleIndex → Point)
    (hrows : ∀ row : Fin 16,
      nativePoint (rowIndex row) = expectedPoint row) :
    Function.Injective (fun row : Fin 16 => nativePoint (rowIndex row)) := by
  intro a b hab
  apply expectedPoint_injective
  rw [← hrows a, ← hrows b]
  exact hab

def expectedFourier (row : Fin 16) : NativeTowerFormulas.CM M31 :=
  ⟨(expectedPoint row).1, (expectedPoint row).2⟩

theorem expectedFourier_injective : Function.Injective expectedFourier := by
  intro a b hab
  apply expectedPoint_injective
  exact Prod.ext (congrArg NativeTowerFormulas.CM.a hab)
    (congrArg NativeTowerFormulas.CM.b hab)

theorem expectedPoint_x_ne_zero (row : Fin 16) :
    (expectedPoint row).1 ≠ 0 := by
  fin_cases row <;> decide

theorem expectedFourier_ne_zero (row : Fin 16) :
    expectedFourier row ≠ 0 := by
  intro h
  have ha := congrArg NativeTowerFormulas.CM.a h
  exact expectedPoint_x_ne_zero row (by simpa [expectedFourier] using ha)

noncomputable def expectedFourierUnit (row : Fin 16) :
    (NativeTowerFormulas.CM M31)ˣ :=
  Units.mk0 (expectedFourier row) (expectedFourier_ne_zero row)

theorem expectedFourierUnit_injective :
    Function.Injective expectedFourierUnit := by
  intro a b hab
  apply expectedFourier_injective
  exact congrArg Units.val hab

theorem nativeFourier_injective
    (nativeFourier : Fin 16 → NativeTowerFormulas.CM M31)
    (hrows : ∀ row, nativeFourier row = expectedFourier row) :
    Function.Injective nativeFourier := by
  intro a b hab
  apply expectedFourier_injective
  rw [← hrows a, ← hrows b]
  exact hab

/-- This is the row-to-`Fˣ` premise needed by the P05 finite Laurent
uniqueness theorem, conditional only on exact native Fourier row equality. -/
theorem nativeFourierUnit_injective
    (nativeFourier : Fin 16 → (NativeTowerFormulas.CM M31)ˣ)
    (hrows : ∀ row, nativeFourier row = expectedFourierUnit row) :
    Function.Injective nativeFourier := by
  intro a b hab
  apply expectedFourierUnit_injective
  rw [← hrows a, ← hrows b]
  exact hab


/-- The first four native circle-basis slots are determined by two
conjugate row pairs with distinct x coordinates. This is an exact inverse
certificate for the four-slot evaluation map, independent of an FFT. -/
theorem four_block_zero_of_two_conjugate_pairs
    {F : Type*} [Field F] (xₐ xᵦ y : F)
    (hx : xₐ ≠ xᵦ) (hy : y ≠ 0) (htwo : (2 : F) ≠ 0)
    (c₀ c₁ c₂ c₃ : F)
    (h₀ : nativeFourBlock c₀ c₁ c₂ c₃ xₐ y = 0)
    (h₁ : nativeFourBlock c₀ c₁ c₂ c₃ xₐ (-y) = 0)
    (h₂ : nativeFourBlock c₀ c₁ c₂ c₃ xᵦ y = 0)
    (h₃ : nativeFourBlock c₀ c₁ c₂ c₃ xᵦ (-y) = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ c₃ = 0 := by
  simp only [nativeFourBlock] at h₀ h₁ h₂ h₃
  have ha₀ : c₀ + c₂ * xₐ = 0 := by
    have h : (2 : F) * (c₀ + c₂ * xₐ) = 0 := by
      linear_combination h₀ + h₁
    exact (mul_eq_zero.mp h).resolve_left htwo
  have hb₀ : c₀ + c₂ * xᵦ = 0 := by
    have h : (2 : F) * (c₀ + c₂ * xᵦ) = 0 := by
      linear_combination h₂ + h₃
    exact (mul_eq_zero.mp h).resolve_left htwo
  have ha₁ : c₁ + c₃ * xₐ = 0 := by
    have h : ((2 : F) * y) * (c₁ + c₃ * xₐ) = 0 := by
      linear_combination h₀ - h₁
    have h2y : (2 : F) * y ≠ 0 := mul_ne_zero htwo hy
    exact (mul_eq_zero.mp h).resolve_left h2y
  have hb₁ : c₁ + c₃ * xᵦ = 0 := by
    have h : ((2 : F) * y) * (c₁ + c₃ * xᵦ) = 0 := by
      linear_combination h₂ - h₃
    have h2y : (2 : F) * y ≠ 0 := mul_ne_zero htwo hy
    exact (mul_eq_zero.mp h).resolve_left h2y
  have hxdiff : xₐ - xᵦ ≠ 0 := sub_ne_zero.mpr hx
  have hc₂ : c₂ = 0 := by
    have h : c₂ * (xₐ - xᵦ) = 0 := by
      linear_combination ha₀ - hb₀
    exact (mul_eq_zero.mp h).resolve_right hxdiff
  have hc₃ : c₃ = 0 := by
    have h : c₃ * (xₐ - xᵦ) = 0 := by
      linear_combination ha₁ - hb₁
    exact (mul_eq_zero.mp h).resolve_right hxdiff
  simp_all

/-- Four row equalities imply equality of all four circle coefficients.
Rows 0/1 and 3/2 are conjugate pairs, so the second pair is reversed. -/
theorem four_block_injective_of_two_conjugate_pairs
    {F : Type*} [Field F] (xₐ xᵦ y : F)
    (hx : xₐ ≠ xᵦ) (hy : y ≠ 0) (htwo : (2 : F) ≠ 0)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : F)
    (h₀ : nativeFourBlock a₀ a₁ a₂ a₃ xₐ y =
      nativeFourBlock b₀ b₁ b₂ b₃ xₐ y)
    (h₁ : nativeFourBlock a₀ a₁ a₂ a₃ xₐ (-y) =
      nativeFourBlock b₀ b₁ b₂ b₃ xₐ (-y))
    (h₂ : nativeFourBlock a₀ a₁ a₂ a₃ xᵦ y =
      nativeFourBlock b₀ b₁ b₂ b₃ xᵦ y)
    (h₃ : nativeFourBlock a₀ a₁ a₂ a₃ xᵦ (-y) =
      nativeFourBlock b₀ b₁ b₂ b₃ xᵦ (-y)) :
    a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  simp only [nativeFourBlock] at h₀ h₁ h₂ h₃
  have hz₀ : nativeFourBlock (a₀ - b₀) (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) xₐ y = 0 := by
    dsimp [nativeFourBlock]
    linear_combination h₀
  have hz₁ : nativeFourBlock (a₀ - b₀) (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) xₐ (-y) = 0 := by
    dsimp [nativeFourBlock]
    linear_combination h₁
  have hz₂ : nativeFourBlock (a₀ - b₀) (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) xᵦ y = 0 := by
    dsimp [nativeFourBlock]
    linear_combination h₂
  have hz₃ : nativeFourBlock (a₀ - b₀) (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) xᵦ (-y) = 0 := by
    dsimp [nativeFourBlock]
    linear_combination h₃
  obtain ⟨h₀', h₁', h₂', h₃'⟩ :=
    four_block_zero_of_two_conjugate_pairs xₐ xᵦ y hx hy htwo
      (a₀ - b₀) (a₁ - b₁) (a₂ - b₂) (a₃ - b₃) hz₀ hz₁ hz₂ hz₃
  exact ⟨sub_eq_zero.mp h₀', sub_eq_zero.mp h₁',
    sub_eq_zero.mp h₂', sub_eq_zero.mp h₃'⟩

/-- The concrete rows use native bit-reversed storage order, not natural
circle order. -/
def fourBlockAtExpectedRow (c₀ c₁ c₂ c₃ : M31) (row : Fin 16) : M31 :=
  nativeFourBlock c₀ c₁ c₂ c₃
    (expectedPoint row).1 (expectedPoint row).2

/-- Four authenticated canonical rows determine the entire first circle
coefficient block. This is the exact Gate log-4 finite-table inverse boundary;
the native FFT still needs its own operational refinement. -/
theorem expected_four_row_block_injective
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : M31)
    (h₀ : fourBlockAtExpectedRow a₀ a₁ a₂ a₃ 0 =
      fourBlockAtExpectedRow b₀ b₁ b₂ b₃ 0)
    (h₁ : fourBlockAtExpectedRow a₀ a₁ a₂ a₃ 1 =
      fourBlockAtExpectedRow b₀ b₁ b₂ b₃ 1)
    (h₂ : fourBlockAtExpectedRow a₀ a₁ a₂ a₃ 2 =
      fourBlockAtExpectedRow b₀ b₁ b₂ b₃ 2)
    (h₃ : fourBlockAtExpectedRow a₀ a₁ a₂ a₃ 3 =
      fourBlockAtExpectedRow b₀ b₁ b₂ b₃ 3) :
    a₀ = b₀ ∧ a₁ = b₁ ∧ a₂ = b₂ ∧ a₃ = b₃ := by
  have hx : (1179735656 : M31) ≠ 967747991 := by decide
  have hy : (1241207368 : M31) ≠ 0 := by decide
  have htwo : (2 : M31) ≠ 0 := by decide
  have hneg : -(1241207368 : M31) = 906276279 := by decide
  apply four_block_injective_of_two_conjugate_pairs
    (1179735656 : M31) 967747991 1241207368 hx hy htwo
    a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃
  · simpa [fourBlockAtExpectedRow, expectedPoint] using h₀
  · simpa [fourBlockAtExpectedRow, expectedPoint, hneg] using h₁
  · simpa [fourBlockAtExpectedRow, expectedPoint] using h₃
  · simpa [fourBlockAtExpectedRow, expectedPoint, hneg] using h₂

/-- If two radius-two circle words agree on the other fifteen native Gate
rows, they also agree at the remaining row. This proves the algebraic reason
why a one-row edit cannot pass a four-slot degree check. It assumes the two
candidate words are already degree-bounded; sparse verifier acceptance is a
separate question. -/
theorem one_row_edit_not_in_radius_two
    (f g : CirclePoly (NativeTowerFormulas.CM M31))
    (hf : InCircleBand 2 f) (hg : InCircleBand 2 g)
    (target : Fin 16)
    (hothers : ∀ row : Fin 16, row ≠ target →
      eval₂ (RingHom.id _) (expectedFourierUnit row) f =
        eval₂ (RingHom.id _) (expectedFourierUnit row) g) :
    eval₂ (RingHom.id _) (expectedFourierUnit target) f =
      eval₂ (RingHom.id _) (expectedFourierUnit target) g := by
  classical
  let rows : Finset (Fin 16) := Finset.univ.erase target
  let samples := rows.image expectedFourierUnit
  have hcard : samples.card = 15 := by
    rw [Finset.card_image_iff.mpr (fun _ _ _ _ hab =>
      expectedFourierUnit_injective hab)]
    simp [rows]
  have hmany : 2 * 2 < samples.card := by omega
  have hfg : f = g := by
    apply band_eq_of_agreement f g 2 hf hg samples hmany
    intro t ht
    obtain ⟨row, hr, rfl⟩ := Finset.mem_image.mp ht
    have hn : row ≠ target := by simpa [rows] using hr
    exact hothers row hn
  rw [hfg]

end S31.Gadgets.PcsFri.Gate16FourierRows
