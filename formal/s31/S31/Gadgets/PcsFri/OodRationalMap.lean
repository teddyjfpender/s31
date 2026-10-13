import Mathlib.Tactic

/-!
The algebraic core of the native OOD seed-to-circle map. A nonexceptional
seed has a recoverable rational inverse, so the map is injective on its
defined domain. This is a field-level theorem, not a proof that the native
Fiat–Shamir seed is uniform or that the Zig implementation refines it.
-/

namespace S31.Gadgets.PcsFri.OodRationalMap

variable {F : Type*} [Field F]

def regular (t : F) : Prop := 1 + t ^ 2 ≠ 0

def x (t : F) : F := (1 - t ^ 2) / (1 + t ^ 2)
def y (t : F) : F := (2 * t) / (1 + t ^ 2)

theorem on_circle (t : F) (h : regular t) :
    x t ^ 2 + y t ^ 2 = 1 := by
  unfold x y regular at *
  field_simp [h]
  ring

theorem one_add_x (t : F) (h : regular t) :
    1 + x t = 2 / (1 + t ^ 2) := by
  unfold x regular at *
  field_simp [h]
  ring

theorem inverse [NeZero (2 : F)] (t : F) (h : regular t) :
    y t / (1 + x t) = t := by
  rw [one_add_x t h]
  unfold y regular at *
  field_simp [h, NeZero.ne (2 : F)]

theorem one_add_x_ne_zero [NeZero (2 : F)] (t : F)
    (h : regular t) : 1 + x t ≠ 0 := by
  rw [one_add_x t h]
  exact div_ne_zero (NeZero.ne (2 : F)) h

theorem injective_on_regular [NeZero (2 : F)] (a b : F) (ha : regular a)
    (hb : regular b) (hx : x a = x b) (hy : y a = y b) : a = b := by
  calc
    a = y a / (1 + x a) := (inverse a ha).symm
    _ = y b / (1 + x b) := by rw [hx, hy]
    _ = b := inverse b hb

/-- The rational map preserves every embedded subfield. In particular, a
seed from the quadratic subfield produces both circle coordinates there.
This theorem does not say how often the native transcript draws such a seed. -/
theorem map_coordinates {K : Type*} [Field K] (embed : K →+* F)
    (t : K) :
    x (embed t) = embed (x t) ∧ y (embed t) = embed (y t) := by
  constructor <;> simp [x, y, map_ofNat]

end S31.Gadgets.PcsFri.OodRationalMap
