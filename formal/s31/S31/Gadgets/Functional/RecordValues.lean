import S31.Gadgets.Functional.Graph

/-!
Named fields elaborate to a typed product before residual polynomial lowering.
The field labels and nominal source identity are checked by the Python frontend;
this file models the post-typecheck erasure. It does not prove the parser or
production Zig gate emitter correct. A separate generic Except model below
states the eager failure rule for unused fields.
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

/-- A typed record argument models the result of source pattern desugaring:
field names are resolved before this product reaches specialization. -/
def recordSquareSumPattern : Expr [.field] .field :=
  .apply
    (.lambda (.add (.fst (.var .here)) (.snd (.var .here))))
    (makePowers (.mul (.var .here) (.var .here))
                (.add (.var .here) (.var .here)))

/-- Constructing a named product and selecting its fields leaves exactly the
same residual polynomial as writing the arithmetic directly. -/
theorem recordSquareSum_zero_cost {n : Nat} (x : Poly n) :
    specialize recordSquareSum (.cons x .nil) =
      specialize directSquareSum (.cons x .nil) := rfl

/-- Destructuring the typed product also leaves the residual expression
unchanged; eager effects are handled by the separate compiler effect pass. -/
theorem recordSquareSumPattern_zero_cost {n : Nat} (x : Poly n) :
    specialize recordSquareSumPattern (.cons x .nil) =
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

/-- Source record construction evaluates fields in declaration order, including
fields that a later projection will not read. This is an effect model, separate
from the total polynomial core above. -/
def eagerPair {ε α β : Type} (first : Except ε α) (second : Except ε β) :
    Except ε (α × β) :=
  match first with
  | .error reason => .error reason
  | .ok a =>
      match second with
      | .error reason => .error reason
      | .ok b => .ok (a, b)

def eagerFirst {ε α β : Type} (pair : Except ε (α × β)) : Except ε α :=
  match pair with
  | .error reason => .error reason
  | .ok (a, _) => .ok a

/-- An unused second field cannot hide a failure in the source-stage record. -/
theorem eagerFirst_ok_iff {ε α β : Type} (first : Except ε α)
    (second : Except ε β) :
    (∃ a, eagerFirst (eagerPair first second) = .ok a) ↔
      (∃ a, first = .ok a) ∧ (∃ b, second = .ok b) := by
  cases first <;> cases second <;> simp [eagerFirst, eagerPair]

/-- If both field computations fail, the first declared field reports its
failure. Source literal spelling order does not alter this order. -/
theorem eagerPair_first_error {ε α β : Type} (first second : ε) :
    eagerPair (.error first : Except ε α) (.error second : Except ε β) =
      .error first := rfl

end S31.Functional.RecordValues
