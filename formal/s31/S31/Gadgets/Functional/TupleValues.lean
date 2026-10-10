import S31.Gadgets.Functional.Graph

/-!
Typed model of `tuple_square_sum.s31`, one M31 lane at a time. The source
product and its projections disappear during specialization. The strict
constraint theorem quantifies over any accepted intermediate witness; it does
not assert that the Python parser or Zig AIR compiler implements this model.
-/

namespace S31.Functional

def tupleSquareSum : Expr [.field] .field :=
  .letValue
    (.pair (.mul (.var .here) (.var .here))
           (.add (.var .here) (.var .here)))
    (.add (.fst (.var .here)) (.snd (.var .here)))

def directSquareSum : Expr [.field] .field :=
  .add (.mul (.var .here) (.var .here))
       (.add (.var .here) (.var .here))

/-- Product construction and projections create no residual polynomial node. -/
theorem tupleSquareSum_zero_cost {n : Nat} (x : Poly n) :
    specialize tupleSquareSum (.cons x .nil) =
      specialize directSquareSum (.cons x .nil) := rfl

/-- A strict graph accepts exactly the claimed square plus two copies of x. -/
theorem tupleSquareSum_accepts (x output : M31) :
    Poly.Accepts (fun _ : Fin 1 => x)
      (specialize tupleSquareSum (inputResidual [0])) output ↔
      output = x * x + (x + x) := by
  simpa [tupleSquareSum, inputSource, inputResidual, denote] using
    (program_accepts_iff [0] tupleSquareSum (fun _ : Fin 1 => x) output)

end S31.Functional
