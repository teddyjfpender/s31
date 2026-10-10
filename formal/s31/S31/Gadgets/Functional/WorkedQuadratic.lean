import S31.Gadgets.Functional.MathLibrary
import S31.Gadgets.Functional.Arrays

/-!
The typed-core analogue of `functional_poly4.s31`: a captured coefficient,
one higher-order call, and four independent Horner lanes. The source example
is checked against its direct form by the Python docs and native acceptance
gates. This Lean theorem is about the typed core and strict field graph, not
an unproved general correspondence with the Python parser or Zig compiler.
-/

namespace S31.Functional

open Graph

private def two : M31 := RiscvRefinement.M31.reduce 2
private def three : M31 := RiscvRefinement.M31.reduce 3
private def seven : M31 := RiscvRefinement.M31.reduce 7

/-- Direct Horner form `(2*x+3)*x+7`. -/
def workedQuadraticDirect : Expr [.array 4] (.array 4) :=
  .arrayAdd
    (.arrayMul
      (.arrayAdd
        (.arrayMul (.arraySplat (.literal two)) (.var .here))
        (.arraySplat (.literal three)))
      (.var .here))
    (.arraySplat (.literal seven))

/-- `let constant = 7; let f = fun v => (2*v+3)*v+constant;
    f(x)`. The two source bindings and the closure disappear statically. -/
def workedQuadraticFunctional : Expr [.array 4] (.array 4) :=
  .letValue (.arraySplat (.literal seven))
    (.letValue
      (.lambda
        (.arrayAdd
          (.arrayMul
            (.arrayAdd
              (.arrayMul (.arraySplat (.literal two)) (.var .here))
              (.arraySplat (.literal three)))
            (.var .here))
          (.var (.there .here))))
      (.apply (.var .here) (.var (.there (.there .here)))))

/-- For every residual input, closure specialization emits precisely the
same four first-order polynomial expressions as the direct source. -/
theorem workedQuadratic_zero_cost {n : Nat} (x : Fin 4 → Poly n) :
    specialize workedQuadraticFunctional (.cons x .nil) =
      specialize workedQuadraticDirect (.cons x .nil) := rfl

def workedQuadraticCode : Code M31 FieldOp :=
  arrayCode workedQuadraticFunctional

theorem workedQuadraticCode_eq_direct :
    workedQuadraticCode = arrayCode workedQuadraticDirect := rfl

theorem workedQuadraticCode_valid :
    workedQuadraticCode.WellFormedFor fieldArity 4 :=
  arrayCode_valid workedQuadraticFunctional

private def quadratic (x : M31) : M31 :=
  (two * x + three) * x + seven

/-- All four claimed output words are fixed by arbitrary satisfying strict
graph witnesses. Conversely every input has an honest graph witness. -/
theorem workedQuadraticCode_accepts (a b c d : M31)
    (output : List M31) :
    workedQuadraticCode.strictAccepts fieldArity
      Gadgets.Hash.fieldPrimitive [a, b, c, d] output ↔
      output = [quadratic a, quadratic b, quadratic c, quadratic d] := by
  simpa [workedQuadraticCode, workedQuadraticFunctional,
    arrayInputSource, denote, Env.get, quadratic, two, three, seven]
    using (arrayCode_accepts workedQuadraticFunctional
      [a, b, c, d] output rfl)

end S31.Functional
