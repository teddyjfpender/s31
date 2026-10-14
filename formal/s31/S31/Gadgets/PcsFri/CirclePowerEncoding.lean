import S31.Gadgets.PcsFri.ConcreteCircleCount
import Mathlib.Tactic

/-!
The algebraic circle-to-field encoding for bounding repeated-doubling
fibers. This module models the native circle formulas; a separate native
refinement must identify its `CirclePointQM31.repeatedDouble` implementation
with these formulas at the proof boundary.
-/

namespace S31.Gadgets.PcsFri.CirclePowerEncoding

open ConcreteCircleCount

variable {K : Type*} [Field K] [NeZero (2 : K)]

def encode (i : K) (p : Circle K) : K := p.1.1 + i * p.1.2

def opposite (i : K) (p : Circle K) : K := p.1.1 - i * p.1.2

omit [NeZero (2 : K)] in
theorem encode_mul_opposite (i : K) (hi : i ^ 2 = -1)
    (p : Circle K) : encode i p * opposite i p = 1 := by
  unfold encode opposite
  calc
    (p.1.1 + i * p.1.2) * (p.1.1 - i * p.1.2) =
        p.1.1 ^ 2 - i ^ 2 * p.1.2 ^ 2 := by ring
    _ = p.1.1 ^ 2 + p.1.2 ^ 2 := by rw [hi]; ring
    _ = 1 := p.2

theorem encode_injective (i : K) (hi : i ^ 2 = -1) :
    Function.Injective (encode i) := by
  intro p q hpq
  have hop : opposite i p = opposite i q := by
    calc
      opposite i p = (encode i p)⁻¹ :=
        eq_inv_of_mul_eq_one_right (encode_mul_opposite i hi p)
      _ = (encode i q)⁻¹ := by rw [hpq]
      _ = opposite i q :=
        (eq_inv_of_mul_eq_one_right (encode_mul_opposite i hi q)).symm
  have h2x : (2 : K) * p.1.1 = 2 * q.1.1 := by
    unfold encode at hpq
    unfold opposite at hop
    linear_combination hpq + hop
  have hx : p.1.1 = q.1.1 :=
    mul_left_cancel₀ (NeZero.ne (2 : K)) h2x
  have h2iy : (2 * i) * p.1.2 = (2 * i) * q.1.2 := by
    unfold encode at hpq
    unfold opposite at hop
    linear_combination hpq - hop
  have hi0 : i ≠ 0 := by
    intro h
    simp [h] at hi
  have hy : p.1.2 = q.1.2 :=
    mul_left_cancel₀ (mul_ne_zero (NeZero.ne (2 : K)) hi0) h2iy
  apply Subtype.ext
  exact Prod.ext hx hy

def double (p : Circle K) : Circle K := by
  refine ⟨(p.1.1 ^ 2 - p.1.2 ^ 2,
      2 * p.1.1 * p.1.2), ?_⟩
  calc
    (p.1.1 ^ 2 - p.1.2 ^ 2) ^ 2 +
        (2 * p.1.1 * p.1.2) ^ 2 =
        (p.1.1 ^ 2 + p.1.2 ^ 2) ^ 2 := by ring
    _ = 1 := by rw [p.2]; ring

omit [NeZero (2 : K)] in
theorem encode_double (i : K) (hi : i ^ 2 = -1)
    (p : Circle K) : encode i (double p) = (encode i p) ^ 2 := by
  unfold encode double
  dsimp
  calc
    p.1.1 ^ 2 - p.1.2 ^ 2 + i * (2 * p.1.1 * p.1.2) =
        p.1.1 ^ 2 + i ^ 2 * p.1.2 ^ 2 +
          i * (2 * p.1.1 * p.1.2) := by rw [hi]; ring
    _ = (p.1.1 + i * p.1.2) ^ 2 := by ring

omit [NeZero (2 : K)] in
/-- Repeated circle doubling becomes field powering with exponent `2^k`. -/
theorem encode_iterated_double (i : K) (hi : i ^ 2 = -1)
    (p : Circle K) (k : ℕ) :
    encode i (((double (K := K))^[k]) p) = (encode i p) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', encode_double i hi, ih]
      calc
        (encode i p ^ 2 ^ k) ^ 2 =
            (encode i p) ^ (2 ^ k * 2) := (pow_mul _ _ _).symm
        _ = (encode i p) ^ (2 ^ (k + 1)) := by rw [pow_succ]

abbrev QM31 := ConcreteCircleCount.QM31

def qm31Imaginary : QM31 := ⟨⟨0, 1⟩, ⟨0, 0⟩⟩

theorem qm31_imaginary_square : qm31Imaginary ^ 2 = -1 :=
  ConcreteCircleCount.qm_imaginary_square

theorem qm31_encode_injective :
    Function.Injective (encode qm31Imaginary : Circle QM31 → QM31) :=
  encode_injective qm31Imaginary qm31_imaginary_square

theorem qm31_encode_iterated_double (p : Circle QM31) (k : ℕ) :
    encode qm31Imaginary (((double (K := QM31))^[k]) p) =
      (encode qm31Imaginary p) ^ (2 ^ k) :=
  encode_iterated_double qm31Imaginary qm31_imaginary_square p k

end S31.Gadgets.PcsFri.CirclePowerEncoding
