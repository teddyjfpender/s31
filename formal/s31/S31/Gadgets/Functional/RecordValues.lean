import S31.Gadgets.Functional.Graph

/-!
Named fields elaborate to a typed product before residual polynomial lowering.
The field labels and nominal source identity are checked by the Python frontend;
this file models the post-typecheck erasure. It does not prove the parser or
production Zig gate emitter correct, nor model effects of unused fields.
-/

namespace S31.Functional.RecordValues

abbrev PowersType : Ty := .prod .field .field

def makePowers {Γ : List Ty} (square doubled : Expr Γ .field) :
    Expr Γ PowersType := .pair square doubled

def square {Γ : List Ty} (value : Expr Γ PowersType) : Expr Γ .field :=
  .fst value

def doubled {Γ : List Ty} (value : Expr Γ PowersType) : Expr Γ .field :=
  .snd value

def recordSquareSum : Expr [.field] .field :=
  .letValue
    (makePowers (.mul (.var .here) (.var .here))
                (.add (.var .here) (.var .here)))
    (.add (square (.var .here)) (doubled (.var .here)))

def directSquareSum : Expr [.field] .field :=
  .add (.mul (.var .here) (.var .here))
       (.add (.var .here) (.var .here))

/-- Constructing a named product and selecting its fields leaves exactly the
same residual polynomial as writing the arithmetic directly. -/
theorem recordSquareSum_zero_cost {n : Nat} (x : Poly n) :
    specialize recordSquareSum (.cons x .nil) =
      specialize directSquareSum (.cons x .nil) := rfl

/-- Every accepted graph witness binds the public result to the field
expression, including the input at seven and a claimed output of 64. -/
theorem recordSquareSum_accepts (x output : M31) :
    Poly.Accepts (fun _ : Fin 1 => x)
      (specialize recordSquareSum (inputResidual [0])) output ↔
      output = x * x + (x + x) := by
  simpa [recordSquareSum, makePowers, square, doubled, inputSource,
    inputResidual, denote] using
    (program_accepts_iff [0] recordSquareSum (fun _ : Fin 1 => x) output)

end S31.Functional.RecordValues
