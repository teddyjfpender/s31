import S31.Gadgets.PcsFri.PairedDenominator

/-!
A small quadratic-tower model for the CAS05 OOD point. Native QM31 stores
`c0 + u*c1` over CM31, with `u² = 2+i`. The pair operations below spell the
coefficient equations; they do not assert that Zig's concrete field methods
implement them. In particular, this bridge eliminates free circle-coefficient
premises from the denominator theorem, leaving a source refinement of field
arithmetic, the sampled guard, and Merkle/transcript semantics.
-/

namespace S31.Gadgets.PcsFri.PairedTowerCircle

variable {K : Type*} [Field K] [NeZero (2 : K)]

structure Pair (K : Type*) where
  c0 : K
  c1 : K
  deriving DecidableEq

def add (x y : Pair K) : Pair K :=
  ⟨x.c0 + y.c0, x.c1 + y.c1⟩

def square (d : K) (x : Pair K) : Pair K :=
  ⟨x.c0 ^ 2 + d * x.c1 ^ 2, 2 * x.c0 * x.c1⟩

def one : Pair K := ⟨1, 0⟩

/-- A pair-valued circle equation gives the two coefficient equations used
by the abstract all-row quotient-denominator theorem. -/
theorem circle_coefficients (d : K) (x y : Pair K)
    (hcircle : add (square d x) (square d y) = (one : Pair K)) :
    x.c0 ^ 2 + y.c0 ^ 2 + d * (x.c1 ^ 2 + y.c1 ^ 2) = 1 ∧
    x.c0 * x.c1 + y.c0 * y.c1 = 0 := by
  have h0 := congrArg Pair.c0 hcircle
  have h1 := congrArg Pair.c1 hcircle
  simp only [add, square, one] at h0 h1
  constructor
  · linear_combination h0
  · have h2 : (2 : K) * (x.c0 * x.c1 + y.c0 * y.c1) = 0 := by
      linear_combination h1
    exact (mul_eq_zero.mp h2).resolve_left (NeZero.ne (2 : K))

/-- For every base-circle row, the CAS05 denominator is nonzero directly
from the pair-valued OOD circle equation, nonsquare tower parameter, and
`y.c1` guard. -/
theorem denominator_ne_zero_of_pair_circle
    (d : K) (x y : Pair K) (a b : K)
    (hd : ∀ t : K, t ^ 2 ≠ d)
    (hcircle : add (square d x) (square d y) = (one : Pair K))
    (hbase : a ^ 2 + b ^ 2 = 1)
    (hguard : y.c1 ≠ 0) :
    (x.c0 - a) * y.c1 - (y.c0 - b) * x.c1 ≠ 0 := by
  obtain ⟨h0, h1⟩ := circle_coefficients d x y hcircle
  exact PairedDenominator.circle_denominator_ne_zero d x.c0 y.c0 x.c1 y.c1
    a b hd h0 h1 hbase hguard

end S31.Gadgets.PcsFri.PairedTowerCircle
