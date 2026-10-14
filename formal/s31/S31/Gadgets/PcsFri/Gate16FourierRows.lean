import S31.Gadgets.PcsFri.CanonicalCircleLaurentRows
import S31.Gadgets.PcsFri.NativeTowerFormulas
import S31.Gadgets.PcsFri.CM31FieldInstance
import Mathlib.Tactic

/-!
The exact sixteen storage rows in Gate's smallest source domain. The index
calculation is a transcription of `CanonicCoset.new(4).circleDomain()` followed
by `bitReverseIndex(row, 4)`; it does not assume generator-order correctness.
-/

namespace S31.Gadgets.PcsFri.Gate16FourierRows

open S31.Gadgets.PcsFri.CanonicalCircleLaurentRows

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


end S31.Gadgets.PcsFri.Gate16FourierRows
