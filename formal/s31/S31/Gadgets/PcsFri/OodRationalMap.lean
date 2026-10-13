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

/-- Every circle point other than `(-1, 0)` has a rational preimage. This
identifies the exact image of the seed map, independently of any sampler. -/
theorem circle_point_has_preimage [NeZero (2 : F)] (px py : F)
    (hcircle : px ^ 2 + py ^ 2 = 1) (hnotminus : 1 + px ≠ 0) :
    ∃ t : F, regular t ∧ x t = px ∧ y t = py := by
  let t := py / (1 + px)
  have hden : 1 + t ^ 2 = 2 / (1 + px) := by
    dsimp [t]
    field_simp [hnotminus]
    linear_combination hcircle
  have hregular : regular t := by
    rw [regular, hden]
    exact div_ne_zero (NeZero.ne (2 : F)) hnotminus
  refine ⟨t, hregular, ?_, ?_⟩
  · rw [x, hden]
    dsimp [t]
    field_simp [hnotminus, NeZero.ne (2 : F)]
    linear_combination -hcircle
  · rw [y, hden]
    dsimp [t]
    field_simp [hnotminus, NeZero.ne (2 : F)]

/-- The regular seed-to-circle map is a bijection onto circle points with
`1+x ≠ 0`; the explicit inverse is `y/(1+x)`. -/
theorem circle_point_unique_preimage [NeZero (2 : F)] (px py t : F)
    (ht : regular t) (hx : x t = px) (hy : y t = py) :
    t = py / (1 + px) := by
  rw [← hx, ← hy]
  exact (inverse t ht).symm

/-- On the circle, the excluded `1+x=0` locus consists of one point. -/
theorem omitted_circle_point (px py : F)
    (hcircle : px ^ 2 + py ^ 2 = 1) (hexcluded : 1 + px = 0) :
    px = -1 ∧ py = 0 := by
  have hx : px = -1 := by
    calc
      px = (1 + px) - 1 := by ring
      _ = -1 := by rw [hexcluded]; ring
  subst px
  have hsq : py ^ 2 = 0 := by simpa using hcircle
  exact ⟨rfl, (mul_eq_zero.mp (by simpa [pow_two] using hsq)).elim id id⟩

/-- The image excludes precisely the circle point with first coordinate
`-1`. This subtype makes the native sampler's support explicit. -/
def seedToCirclePoint [NeZero (2 : F)] (seed : { t : F // regular t }) :
    { point : F × F // point.1 ^ 2 + point.2 ^ 2 = 1 ∧ 1 + point.1 ≠ 0 } :=
  ⟨(x seed.1, y seed.1), on_circle seed.1 seed.2,
    one_add_x_ne_zero seed.1 seed.2⟩

/-- At the algebraic level, regular seeds and the nonexceptional circle
points are in one-to-one correspondence. In a finite field, a uniform seed
conditioned on regularity therefore gives a uniform point on exactly this
image, not on the entire circle. -/
noncomputable def rationalCircleEquiv [NeZero (2 : F)] :
    { t : F // regular t } ≃
      { point : F × F // point.1 ^ 2 + point.2 ^ 2 = 1 ∧ 1 + point.1 ≠ 0 } := by
  apply Equiv.ofBijective seedToCirclePoint
  constructor
  · intro a b hab
    apply Subtype.ext
    have hx : x a.1 = x b.1 := congrArg (fun point => point.1.1) hab
    have hy : y a.1 = y b.1 := congrArg (fun point => point.1.2) hab
    exact injective_on_regular a.1 b.1 a.2 b.2 hx hy
  · intro point
    obtain ⟨t, ht, hx, hy⟩ :=
      circle_point_has_preimage point.1.1 point.1.2 point.2.1 point.2.2
    refine ⟨⟨t, ht⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext hx hy

/-- The rational map preserves every embedded subfield. In particular, a
seed from the quadratic subfield produces both circle coordinates there.
This theorem does not say how often the native transcript draws such a seed. -/
theorem map_coordinates {K : Type*} [Field K] (embed : K →+* F)
    (t : K) :
    x (embed t) = embed (x t) ∧ y (embed t) = embed (y t) := by
  constructor <;> simp [x, y, map_ofNat]

end S31.Gadgets.PcsFri.OodRationalMap
