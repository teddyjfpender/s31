import S31.Gadgets.Functional.Graph

/-!
A typed scalar analogue of `curried_sum.s31`. A function returns a function,
both applications specialize statically, and the residual graph contains one
addition. The Python parser and native Zig lowering are checked separately.
-/

namespace S31.Functional

open Graph

def curriedAddition : Expr [.field, .field] .field :=
  .apply
    (.apply
      (.lambda (.lambda (.add (.var (.there .here)) (.var .here))))
      (.var .here))
    (.var (.there .here))

def directAddition : Expr [.field, .field] .field :=
  .add (.var .here) (.var (.there .here))

/-- Beta reduction removes both function applications for every residual
environment, retaining exactly the direct addition expression. -/
theorem curriedAddition_zero_cost {n : Nat} (a b : Poly n) :
    specialize curriedAddition (.cons a (.cons b .nil)) =
      specialize directAddition (.cons a (.cons b .nil)) := rfl

def curriedAdditionCode : Code M31 FieldOp :=
  (specialize curriedAddition
    (inputResidual [(0 : Fin 2), (1 : Fin 2)])).code

theorem curriedAdditionCode_shape :
    curriedAdditionCode =
      ⟨[.apply .add [0, 1]], [2]⟩ := rfl

theorem curriedAdditionCode_valid :
    curriedAdditionCode.WellFormedFor fieldArity 2 :=
  Poly.code_valid _

/-- No satisfying intermediate gate assignment can make the public result
anything other than the modular sum; an honest witness always exists. -/
theorem curriedAdditionCode_accepts (a b : M31) (output : List M31) :
    curriedAdditionCode.strictAccepts fieldArity
      Gadgets.Hash.fieldPrimitive [a, b] output ↔
      output = [a + b] := by
  simpa [curriedAdditionCode, curriedAddition, inputSource, denote, Env.get]
    using (program_graph_accepts [(0 : Fin 2), (1 : Fin 2)]
      curriedAddition [a, b] output rfl)

end S31.Functional
