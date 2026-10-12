import S31.Gadgets.Functional.Graph

/-!
A typed scalar model of `named_square4.s31`. A named source function is
represented as a static binding of a function value. Passing and applying it
erases before the strict first-order graph is checked. This theorem does not
claim that Python's parser or Zig's AIR compiler implements the model.
-/

namespace S31.Functional

open Graph

def namedSquareValue : Expr [.field] .field :=
  .letValue
    (.lambda (.mul (.var .here) (.var .here)))
    (.apply (.var .here) (.var (.there .here)))

def directSquareValue : Expr [.field] .field :=
  .mul (.var .here) (.var .here)

/-- The static binding, first-class value, and application leave one multiply. -/
theorem namedSquareValue_zero_cost {n : Nat} (x : Poly n) :
    specialize namedSquareValue (.cons x .nil) =
      specialize directSquareValue (.cons x .nil) := rfl

def namedSquareValueCode : Code M31 FieldOp :=
  (specialize namedSquareValue (inputResidual [(0 : Fin 1)])).code

theorem namedSquareValueCode_shape :
    namedSquareValueCode = ⟨[.apply .mul [0, 0]], [1]⟩ := rfl

theorem namedSquareValueCode_valid :
    namedSquareValueCode.WellFormedFor fieldArity 1 :=
  Poly.code_valid _

/-- Every accepted claim equals the square, and the honest claim is accepted. -/
theorem namedSquareValueCode_accepts (x : M31) (output : List M31) :
    namedSquareValueCode.strictAccepts fieldArity
      Gadgets.Hash.fieldPrimitive [x] output ↔
      output = [x * x] := by
  simpa [namedSquareValueCode, namedSquareValue, inputSource, denote, Env.get]
    using (program_graph_accepts [(0 : Fin 1)] namedSquareValue [x] output rfl)

end S31.Functional
