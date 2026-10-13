import S31.Gadgets.PcsFri.PairedTowerCircle
import Mathlib.Tactic

/-!
The actual CAS05 own-quotient denominator is a *line on the circle*, not the
quadratic divisor in `TwoPointDegreeCorrection`. This module proves its
intersection geometry using the native `c0 + u*c1` coordinate equations.

The native verifier commits evaluation rows and does not construct a circle
polynomial coefficient object. Accordingly these results do not infer that
an arbitrary residual admits a quotient **polynomial**, nor that such a
quotient loses one degree in a particular circle basis. Those require an
explicit coordinate-ring/division refinement and a degree filtration theorem.
-/

namespace S31.Gadgets.PcsFri.CircleVanishingLine

variable {K : Type*} [Field K]

/-- CAS05's denominator at a row `(a,b)`, in the order used by
`transposed_paired_sparse.zig`. -/
def nativeLine (x₀ y₀ x₁ y₁ a b : K) : K :=
  (x₀ - a) * y₁ - (y₀ - b) * x₁

/-- Parametrization of the line through the two quadratic conjugates. -/
def linePoint (x₀ y₀ x₁ y₁ t : K) : K × K :=
  (x₀ + t * x₁, y₀ + t * y₁)

theorem nativeLine_linePoint (x₀ y₀ x₁ y₁ t : K) :
    nativeLine x₀ y₀ x₁ y₁ (linePoint x₀ y₀ x₁ y₁ t).1
      (linePoint x₀ y₀ x₁ y₁ t).2 = 0 := by
  simp [nativeLine, linePoint]
  ring

/-- The native `y.c1 != 0` guard gives a unique line parameter. -/
theorem line_zero_iff_parameter (x₀ y₀ x₁ y₁ a b : K)
    (hy : y₁ ≠ 0) :
    nativeLine x₀ y₀ x₁ y₁ a b = 0 ↔
      linePoint x₀ y₀ x₁ y₁ ((b - y₀) / y₁) = (a, b) := by
  constructor
  · intro h
    have hfield : ((b - y₀) / y₁) * y₁ = b - y₀ := by field_simp [hy]
    have hx : x₀ + ((b - y₀) / y₁) * x₁ = a := by
      have hmul : (x₀ + ((b - y₀) / y₁) * x₁ - a) * y₁ = 0 := by
        calc
          _ = (x₀ - a) * y₁ + (((b - y₀) / y₁) * y₁) * x₁ := by ring
          _ = (x₀ - a) * y₁ + (b - y₀) * x₁ := by rw [hfield]
          _ = 0 := by convert h using 1; simp [nativeLine]; ring
      exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hy)
    have hb : y₀ + ((b - y₀) / y₁) * y₁ = b := by rw [hfield]; ring
    apply Prod.ext
    · exact hx
    · exact hb
  · intro h
    have he := congrArg (fun p : K × K => nativeLine x₀ y₀ x₁ y₁ p.1 p.2) h
    change nativeLine x₀ y₀ x₁ y₁ (linePoint x₀ y₀ x₁ y₁ _).1
      (linePoint x₀ y₀ x₁ y₁ _).2 = nativeLine x₀ y₀ x₁ y₁ a b at he
    exact he.symm.trans (nativeLine_linePoint x₀ y₀ x₁ y₁ _)

/-- The circle equation restricted to the native line is exactly the tower
minimal polynomial times the upper-coordinate norm. -/
theorem circle_restriction (d x₀ y₀ x₁ y₁ t : K)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0) :
    (linePoint x₀ y₀ x₁ y₁ t).1 ^ 2 +
        (linePoint x₀ y₀ x₁ y₁ t).2 ^ 2 - 1 =
      (t ^ 2 - d) * (x₁ ^ 2 + y₁ ^ 2) := by
  dsimp [linePoint]
  calc
    (x₀ + t * x₁) ^ 2 + (y₀ + t * y₁) ^ 2 - 1 =
        (x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) - 1) +
        2 * t * (x₀ * x₁ + y₀ * y₁) +
        (t ^ 2 - d) * (x₁ ^ 2 + y₁ ^ 2) := by ring
    _ = (t ^ 2 - d) * (x₁ ^ 2 + y₁ ^ 2) := by rw [h₀, h₁]; ring

/-- An isotropic upper coordinate would force the lower coordinate to have
norm zero, contradicting the tower circle equation. This is the extra
nondegeneracy needed for both ends of a Fourier/Laurent circle basis. -/
theorem upper_norm_ne_zero (d x₀ y₀ x₁ y₁ : K)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0) : x₁ ^ 2 + y₁ ^ 2 ≠ 0 := by
  intro hn
  have hbase : x₀ ^ 2 + y₀ ^ 2 = 1 := by rw [hn] at h₀; simpa using h₀
  have hsq : (x₀ * x₁) ^ 2 = (y₀ * y₁) ^ 2 := by
    have hdot : x₀ * x₁ = -(y₀ * y₁) := eq_neg_of_add_eq_zero_left h₁
    rw [hdot]
    ring
  have hy_sq : y₁ ^ 2 = 0 := by
    calc
      y₁ ^ 2 = (x₀ ^ 2 + y₀ ^ 2) * y₁ ^ 2 := by rw [hbase]; ring
      _ = x₀ ^ 2 * y₁ ^ 2 + (y₀ * y₁) ^ 2 := by ring
      _ = x₀ ^ 2 * (x₁ ^ 2 + y₁ ^ 2) := by rw [← hsq]; ring
      _ = 0 := by rw [hn]; ring
  exact hy (eq_zero_of_pow_eq_zero hy_sq)

/-- The only circle intersections of the native line have parameter roots
of the tower polynomial. This is a geometric point-removal statement; it is
not a claim about divisibility in a circle-polynomial ring. -/
theorem line_circle_intersection (d x₀ y₀ x₁ y₁ a b : K)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hline : nativeLine x₀ y₀ x₁ y₁ a b = 0)
    (hcircle : a ^ 2 + b ^ 2 = 1) :
    ((b - y₀) / y₁) ^ 2 = d := by
  have hpoint := (line_zero_iff_parameter x₀ y₀ x₁ y₁ a b hy).mp hline
  have hrestriction := circle_restriction d x₀ y₀ x₁ y₁
    ((b - y₀) / y₁) h₀ h₁
  rw [hpoint] at hrestriction
  have hproduct : (((b - y₀) / y₁) ^ 2 - d) *
      (x₁ ^ 2 + y₁ ^ 2) = 0 := by simpa [hcircle] using hrestriction.symm
  exact sub_eq_zero.mp ((mul_eq_zero.mp hproduct).resolve_right
    (upper_norm_ne_zero d x₀ y₀ x₁ y₁ h₀ h₁ hy))

/-- With a nonsquare tower parameter, the native line cannot vanish on the
base circle. This is the precise denominator-inversion condition for a
verified base-field row. -/
theorem line_ne_zero_on_base_circle (d x₀ y₀ x₁ y₁ a b : K)
    (hd : ∀ t : K, t ^ 2 ≠ d)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hcircle : a ^ 2 + b ^ 2 = 1) :
    nativeLine x₀ y₀ x₁ y₁ a b ≠ 0 := by
  intro hline
  exact hd _ (line_circle_intersection d x₀ y₀ x₁ y₁ a b
    h₀ h₁ hy hline hcircle)

/-- The pair-valued OOD circle equation used by the native QM31 model
supplies the two coefficient equations needed by point removal. -/
theorem intersection_of_pair_circle [NeZero (2 : K)]
    (d : K) (x y : PairedTowerCircle.Pair K) (a b : K)
    (hcircle : PairedTowerCircle.add
      (PairedTowerCircle.square d x) (PairedTowerCircle.square d y) =
        PairedTowerCircle.one)
    (hy : y.c1 ≠ 0)
    (hline : nativeLine x.c0 y.c0 x.c1 y.c1 a b = 0)
    (hbase : a ^ 2 + b ^ 2 = 1) :
    ((b - y.c0) / y.c1) ^ 2 = d := by
  obtain ⟨h₀, h₁⟩ := PairedTowerCircle.circle_coefficients d x y hcircle
  exact line_circle_intersection d x.c0 y.c0 x.c1 y.c1 a b h₀ h₁ hy hline hbase

/-- Both quadratic-conjugate points lie on the native line and circle when
the extension generator satisfies `u²=d`. -/
theorem conjugate_points_are_on_circle (d u x₀ y₀ x₁ y₁ : K)
    (hu : u ^ 2 = d)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0) :
    (linePoint x₀ y₀ x₁ y₁ u).1 ^ 2 +
        (linePoint x₀ y₀ x₁ y₁ u).2 ^ 2 = 1 ∧
      (linePoint x₀ y₀ x₁ y₁ (-u)).1 ^ 2 +
        (linePoint x₀ y₀ x₁ y₁ (-u)).2 ^ 2 = 1 := by
  constructor
  · have h := circle_restriction d x₀ y₀ x₁ y₁ u h₀ h₁
    rw [hu] at h
    exact sub_eq_zero.mp (by simpa using h)
  · have h := circle_restriction d x₀ y₀ x₁ y₁ (-u) h₀ h₁
    rw [neg_sq, hu] at h
    exact sub_eq_zero.mp (by simpa using h)

/-- Over a field containing a square root `u` of `d`, the two conjugate
points are precisely the circle intersections. Without an odd-characteristic
and nonzero-`u` assumption they may coincide. -/
theorem line_circle_two_points (d u x₀ y₀ x₁ y₁ a b : K)
    (hu : u ^ 2 = d)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0)
    (hline : nativeLine x₀ y₀ x₁ y₁ a b = 0)
    (hcircle : a ^ 2 + b ^ 2 = 1) :
    (a, b) = linePoint x₀ y₀ x₁ y₁ u ∨
      (a, b) = linePoint x₀ y₀ x₁ y₁ (-u) := by
  let t := (b - y₀) / y₁
  have ht : t ^ 2 = u ^ 2 := by
    dsimp [t]
    rw [line_circle_intersection d x₀ y₀ x₁ y₁ a b h₀ h₁ hy hline hcircle,
      hu]
  have hpoint : linePoint x₀ y₀ x₁ y₁ t = (a, b) :=
    (line_zero_iff_parameter x₀ y₀ x₁ y₁ a b hy).mp hline
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ht with h | h
  · left; rw [← hpoint, h]
  · right; rw [← hpoint, h]

/-- The native line has two nonzero Laurent/Fourier edge coefficients when
`i²=-1`. A full degree law additionally needs a circle-polynomial model and
proof that its filtration is this Laurent support filtration. -/
theorem fourier_edges_ne_zero [NeZero (2 : K)] (d i x₀ y₀ x₁ y₁ : K)
    (hi : i ^ 2 = -1)
    (h₀ : x₀ ^ 2 + y₀ ^ 2 + d * (x₁ ^ 2 + y₁ ^ 2) = 1)
    (h₁ : x₀ * x₁ + y₀ * y₁ = 0)
    (hy : y₁ ≠ 0) :
    (-y₁ - i * x₁) / 2 ≠ 0 ∧ (-y₁ + i * x₁) / 2 ≠ 0 := by
  have hn := upper_norm_ne_zero d x₀ y₀ x₁ y₁ h₀ h₁ hy
  have hproduct : (-y₁ - i * x₁) * (-y₁ + i * x₁) =
      x₁ ^ 2 + y₁ ^ 2 := by
    calc
      _ = y₁ ^ 2 - i ^ 2 * x₁ ^ 2 := by ring
      _ = x₁ ^ 2 + y₁ ^ 2 := by rw [hi]; ring
  constructor <;> intro hz
  · have he : -y₁ - i * x₁ = 0 := (div_eq_zero_iff).mp hz |>.resolve_right
      (NeZero.ne (2 : K))
    exact hn (hproduct ▸ by rw [he]; ring)
  · have he : -y₁ + i * x₁ = 0 := (div_eq_zero_iff).mp hz |>.resolve_right
      (NeZero.ne (2 : K))
    exact hn (hproduct ▸ by rw [he]; ring)

end S31.Gadgets.PcsFri.CircleVanishingLine
