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

/-- Nested destructuring lowers to projections of one static binding. -/
def nestedTupleSum : Expr [.field] .field :=
  .letValue
    (.pair
      (.pair (.mul (.var .here) (.var .here))
             (.add (.var .here) (.var .here)))
      (.var .here))
    (.add
      (.add (.fst (.fst (.var .here)))
            (.snd (.fst (.var .here))))
      (.snd (.var .here)))

def directNestedTupleSum : Expr [.field] .field :=
  .add
    (.add (.mul (.var .here) (.var .here))
          (.add (.var .here) (.var .here)))
    (.var .here)

theorem nestedTupleSum_zero_cost {n : Nat} (x : Poly n) :
    specialize nestedTupleSum (.cons x .nil) =
      specialize directNestedTupleSum (.cons x .nil) := rfl

theorem nestedTupleSum_accepts (x output : M31) :
    Poly.Accepts (fun _ : Fin 1 => x)
      (specialize nestedTupleSum (inputResidual [0])) output ↔
      output = x * x + (x + x) + x := by
  simpa [nestedTupleSum, inputSource, inputResidual, denote] using
    (program_accepts_iff [0] nestedTupleSum (fun _ : Fin 1 => x) output)

/- A model of `fn weighted((a,b): (M31,M31)) { a*b+a }` after the
   parser's parameter-pattern expansion. The product and function application
   disappear; this does not assert that the Python parser implements the model. -/
def patternedPairWeighted : Expr [.field, .field] .field :=
  .apply
    (.lambda
      (.add (.mul (.fst (.var .here)) (.snd (.var .here)))
            (.fst (.var .here))))
    (.pair (.var .here) (.var (.there .here)))

def directPairWeighted : Expr [.field, .field] .field :=
  .add (.mul (.var .here) (.var (.there .here))) (.var .here)

theorem patternedPairWeighted_zero_cost {n : Nat} (x y : Poly n) :
    specialize patternedPairWeighted (.cons x (.cons y .nil)) =
      specialize directPairWeighted (.cons x (.cons y .nil)) := rfl

end S31.Functional
