import S31.Gadgets.Air.DirectGateCompositionOpening

/-!
Pure QM31 account of the native OODS seed-to-circle-point map and repeated
doubling. This proves the composition chunk factor as a polynomial recurrence
in the sampled seed. It does not model how the channel draws that seed or
prove that the Zig field/circle implementation refines these definitions.
-/

namespace S31.Gadgets.Air.DirectGateCircleFactor

open S31.Gadgets.Air.DirectGateOodsArithmetic

structure Point where
  x : QM
  y : QM

def onCircle (point : Point) : Prop :=
  point.x * point.x + point.y * point.y = 1

/-- Native rational map. It requires `1 + seed² ≠ 0` to be defined. -/
def fromSeed (seed : QM) : Point :=
  ⟨(1 - seed * seed) * (1 + seed * seed)⁻¹,
    (seed + seed) * (1 + seed * seed)⁻¹⟩

theorem from_seed_on_circle (seed : QM)
    (hden : 1 + seed * seed ≠ 0) :
    onCircle (fromSeed seed) := by
  dsimp [onCircle, fromSeed]
  have hunit : (1 + seed * seed) * (1 + seed * seed)⁻¹ = 1 := by
    exact mul_inv_cancel₀ hden
  calc
    ((1 - seed * seed) * (1 + seed * seed)⁻¹) *
        ((1 - seed * seed) * (1 + seed * seed)⁻¹) +
      ((seed + seed) * (1 + seed * seed)⁻¹) *
        ((seed + seed) * (1 + seed * seed)⁻¹) =
      ((1 + seed * seed) * (1 + seed * seed)⁻¹) ^ 2 := by ring
    _ = 1 := by rw [hunit]; ring

/-- Native circle addition of a point to itself. -/
def double (point : Point) : Point :=
  ⟨point.x * point.x - point.y * point.y,
    point.x * point.y + point.y * point.x⟩

theorem double_on_circle (point : Point) (h : onCircle point) :
    onCircle (double point) := by
  have hsq : (point.x * point.x + point.y * point.y) ^ 2 = 1 := by
    rw [h]
    ring
  dsimp [onCircle, double]
  calc
    (point.x * point.x - point.y * point.y) *
        (point.x * point.x - point.y * point.y) +
      (point.x * point.y + point.y * point.x) *
        (point.x * point.y + point.y * point.x) =
      (point.x * point.x + point.y * point.y) ^ 2 := by ring
    _ = 1 := hsq

def doubleX (x : QM) : QM := 2 * x * x - 1

theorem double_x (point : Point) (h : onCircle point) :
    (double point).x = doubleX point.x := by
  dsimp [double, doubleX, onCircle] at *
  linear_combination -h

/-- `n` native `point.double()` operations, with an equivalent recursive
definition for induction. -/
def repeatedDouble : Nat → Point → Point
  | 0, point => point
  | n + 1, point => double (repeatedDouble n point)

def xAfter : Nat → QM → QM
  | 0, x => x
  | n + 1, x => doubleX (xAfter n x)

theorem repeated_double_on_circle (point : Point) (h : onCircle point) :
    ∀ n, onCircle (repeatedDouble n point) := by
  intro n
  induction n with
  | zero => exact h
  | succ n ih => exact double_on_circle _ ih

theorem repeated_double_x (point : Point) (h : onCircle point) :
    ∀ n, (repeatedDouble n point).x = xAfter n point.x := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [repeatedDouble, double_x _ (repeated_double_on_circle point h n), ih]
      rfl

/-- The exact factor used by split-one composition reconstruction when the
core verifier supplies `composition_log_size`. -/
def factor (seed : QM) (compositionLogSize : Nat) : QM :=
  xAfter (compositionLogSize - 2) (fromSeed seed).x

theorem factor_eq_repeated_double (seed : QM)
    (hden : 1 + seed * seed ≠ 0) (compositionLogSize : Nat) :
    factor seed compositionLogSize =
      (repeatedDouble (compositionLogSize - 2) (fromSeed seed)).x := by
  exact (repeated_double_x (fromSeed seed) (from_seed_on_circle seed hden)
    (compositionLogSize - 2)).symm

end S31.Gadgets.Air.DirectGateCircleFactor
