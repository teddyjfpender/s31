import S31.Gadgets.PcsFri.SparseP05TwoQDegree
import S31.Gadgets.PcsFri.CircleRecursiveBasisDegree

/-!
# Factor vectors at projected sparse Gate OOD points

The accepted verifier claim records a raw top-domain point. The native
sampled-coefficient plan first doubles it `17 - h` times for a source column
at extended log height `h`, then emits `y, x, doubleX(x), ...` for its
`h - 1` coefficient factors. This file proves that the source-shaped point
loop and factor loop agree with the circle-basis factor function for *any*
field and length. Equality to actual Zig bytes is checked separately.
-/

namespace S31.Gadgets.PcsFri.CircleProjectedFactorVector

open SparseP05TwoQDegree
open CircleRecursiveBasisDegree

variable {E : Type*} [Field E]

/-- The field-level shape of `fillEvalFactorsForPoint`, before truncation to
the requested coefficient log. -/
def pointFactor (point : E × E) : Nat → E
  | 0 => point.2
  | r + 1 => ((circleDouble^[r]) point).1

/-- Repeated point doubling and the standalone `doubleX` recurrence produce
the same x-coordinate at every index. No circle membership is needed for the
recurrence itself. -/
theorem repeatedDouble_x_eq_xFactorValue (point : E × E) (r : Nat) :
    ((circleDouble^[r]) point).1 = xFactorValue point.1 r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply']
      simp only [circleDouble, xFactorValue, ih]

theorem pointFactor_eq_nativeFactorValue (point : E × E) (r : Nat) :
    pointFactor point r = nativeFactorValue point.1 point.2 r := by
  cases r with
  | zero => rfl
  | succ r =>
      exact repeatedDouble_x_eq_xFactorValue point r

/-- The vector used for a raw claim at source height `h`: normalize the
point once, then take exactly `h-1` native circle-basis factors. -/
def projectedFactors (raw : E × E) (h : Nat) :
    Fin (h - 1) → E :=
  fun r => pointFactor (projectedPoint h raw) r

theorem projectedFactors_eq_nativeBasis (raw : E × E) (h : Nat)
    (r : Fin (h - 1)) :
    projectedFactors raw h r =
      nativeFactorValue (projectedPoint h raw).1
        (projectedPoint h raw).2 r := by
  exact pointFactor_eq_nativeFactorValue (projectedPoint h raw) r

theorem projectedFactors_zero (raw : E × E) (h : Nat)
    (hh : 0 < h - 1) :
    projectedFactors raw h ⟨0, hh⟩ = (projectedPoint h raw).2 := by
  rfl

theorem projectedFactors_succ (raw : E × E) (h r : Nat)
    (hr : r + 1 < h - 1) :
    projectedFactors raw h ⟨r + 1, hr⟩ =
      ((circleDouble^[r]) (projectedPoint h raw)).1 := by
  rfl

/-- The accepted source-height roster sets the three exact factor-vector
lengths and top-point fold counts. This is arithmetic only; source ownership
of the raw point and actual factor bytes remain native obligations. -/
theorem accepted_source_factor_geometry :
    (17 - 17 = 0 ∧ 17 - 1 = 16) ∧
    (17 - 11 = 6 ∧ 11 - 1 = 10) ∧
    (17 - 5 = 12 ∧ 5 - 1 = 4) := by
  decide

end S31.Gadgets.PcsFri.CircleProjectedFactorVector
