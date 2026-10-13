import Mathlib.Tactic

/-!
Algebraic specification of the coefficient formulas used by native
`cm31.zig` and `qm31.zig`. The definitions deliberately spell out the
Karatsuba products and optimized squares in those files. This proves their
formulas equal schoolbook arithmetic over any commutative ring. A separate
source guard pins the Zig function bodies. Neither component interprets Zig
execution or proves the M31 machine arithmetic correct.
-/

namespace S31.Gadgets.PcsFri.NativeTowerFormulas

variable {K : Type*} [CommRing K]

@[ext] structure CM (K : Type*) where
  a : K
  b : K

def cmAdd (x y : CM K) : CM K := ⟨x.a + y.a, x.b + y.b⟩

/-- Zig's three-product Karatsuba implementation. -/
def cmMul (x y : CM K) : CM K :=
  let ac := x.a * y.a
  let bd := x.b * y.b
  let cross := (x.a + x.b) * (y.a + y.b)
  ⟨ac - bd, cross - ac - bd⟩

def cmSchoolbook (x y : CM K) : CM K :=
  ⟨x.a * y.a - x.b * y.b, x.a * y.b + x.b * y.a⟩

theorem cm_mul_eq_schoolbook (x y : CM K) :
    cmMul x y = cmSchoolbook x y := by
  ext <;> simp [cmMul, cmSchoolbook] <;> ring

/-- Zig's dedicated CM31 square. -/
def cmSquare (x : CM K) : CM K :=
  ⟨x.a ^ 2 - x.b ^ 2, x.a * x.b + x.a * x.b⟩

theorem cm_square_eq_mul (x : CM K) :
    cmSquare x = cmMul x x := by
  rw [cm_mul_eq_schoolbook]
  ext <;> simp [cmSquare, cmSchoolbook] <;> ring

def r : CM K := ⟨2, 1⟩

/-- Zig's `mulByR` with `R = 2+i`. -/
def cmMulByR (x : CM K) : CM K :=
  ⟨(x.a + x.a) - x.b, x.a + (x.b + x.b)⟩

theorem cm_mul_by_r (x : CM K) :
    cmMulByR x = cmMul x (r : CM K) := by
  rw [cm_mul_eq_schoolbook]
  ext <;> simp [cmMulByR, cmSchoolbook, r] <;> ring

@[ext] structure QM (K : Type*) where
  c0 : CM K
  c1 : CM K

def qmAdd (x y : QM K) : QM K :=
  ⟨cmAdd x.c0 y.c0, cmAdd x.c1 y.c1⟩

def qmOne : QM K := ⟨⟨1, 0⟩, ⟨0, 0⟩⟩

def qmFromBase (a : K) : QM K := ⟨⟨a, 0⟩, ⟨0, 0⟩⟩

/-- Zig's general `QM31.square` branch. The base-field fast path is checked
separately below. -/
def qmSquare (x : QM K) : QM K :=
  ⟨cmAdd (cmSquare x.c0) (cmMulByR (cmSquare x.c1)),
    cmAdd (cmMul x.c0 x.c1) (cmMul x.c0 x.c1)⟩

def qmSchoolbookSquare (x : QM K) : QM K :=
  ⟨cmAdd (cmSchoolbook x.c0 x.c0)
      (cmSchoolbook (r : CM K) (cmSchoolbook x.c1 x.c1)),
    cmAdd (cmSchoolbook x.c0 x.c1) (cmSchoolbook x.c0 x.c1)⟩

theorem qm_square_eq_schoolbook (x : QM K) :
    qmSquare x = qmSchoolbookSquare x := by
  ext <;> simp [qmSquare, qmSchoolbookSquare, cmAdd, cmSquare,
    cmMulByR, cmMul, cmSchoolbook, r] <;> ring

/-- The native `isBase` fast path in `QM31.square` agrees with the generic
square formula whenever all non-base coefficients vanish. -/
theorem qm_base_square_eq_schoolbook (a : K) :
    qmFromBase (a ^ 2) = qmSchoolbookSquare (qmFromBase a) := by
  ext <;> simp [qmFromBase, qmSchoolbookSquare, cmAdd, cmSchoolbook, r] <;> ring

/-- One native-shaped circle equation entails both CM31 coefficient
equations, and therefore all four base-field coefficient equations. -/
theorem circle_coefficient_equations (x y : QM K)
    (hcircle : qmAdd (qmSquare x) (qmSquare y) = (qmOne : QM K)) :
    (qmSquare x).c0.a + (qmSquare y).c0.a = 1 ∧
    (qmSquare x).c0.b + (qmSquare y).c0.b = 0 ∧
    (qmSquare x).c1.a + (qmSquare y).c1.a = 0 ∧
    (qmSquare x).c1.b + (qmSquare y).c1.b = 0 := by
  have h0 := congrArg (fun p : QM K => p.c0.a) hcircle
  have h1 := congrArg (fun p : QM K => p.c0.b) hcircle
  have h2 := congrArg (fun p : QM K => p.c1.a) hcircle
  have h3 := congrArg (fun p : QM K => p.c1.b) hcircle
  exact ⟨by simpa [qmAdd, cmAdd, qmOne] using h0,
    by simpa [qmAdd, cmAdd, qmOne] using h1,
    by simpa [qmAdd, cmAdd, qmOne] using h2,
    by simpa [qmAdd, cmAdd, qmOne] using h3⟩

end S31.Gadgets.PcsFri.NativeTowerFormulas
