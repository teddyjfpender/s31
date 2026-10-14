import S31.Semantics.Field

/-!
Semantic rules for the versioned pure-field normalized-to-canonical audit.
They cover operand ordering, constant folding, zero/one aliases and sharing.
The graph theorem permits several source names to point at the same optimized
node. Native `canonical.build` and its emitted digest still require the
separate executable Zig check; this file does not assert an AIR or PCS theorem.
-/

namespace S31.Functional.Correspondence.Optimizer

open S31.Field

inductive Expr (inputs : Nat) where
  | input (id : Fin inputs)
  | constant (value : F)
  | add (left right : Expr inputs)
  | sub (left right : Expr inputs)
  | mul (left right : Expr inputs)
deriving DecidableEq

def Expr.eval {inputs lanes : Nat} (values : Fin inputs → Fin lanes → F) :
    Expr inputs → Fin lanes → F
  | .input id => values id
  | .constant value => fun _ => value
  | .add left right => fun lane => left.eval values lane + right.eval values lane
  | .sub left right => fun lane => left.eval values lane - right.eval values lane
  | .mul left right => fun lane => left.eval values lane * right.eval values lane

/-- The transformations independently replayed by the native audit. `trans`
also permits a fold followed by CSE; `refl` is the semantic content of an
alias to an already emitted node. -/
inductive Preserves {inputs : Nat} : Expr inputs → Expr inputs → Prop where
  | refl (a) : Preserves a a
  | trans {a b c} : Preserves a b → Preserves b c → Preserves a c
  | add_comm (a b) : Preserves (.add a b) (.add b a)
  | mul_comm (a b) : Preserves (.mul a b) (.mul b a)
  | add_const (a b : F) :
      Preserves (.add (.constant a) (.constant b)) (.constant (a + b))
  | sub_const (a b : F) :
      Preserves (.sub (.constant a) (.constant b)) (.constant (a - b))
  | mul_const (a b : F) :
      Preserves (.mul (.constant a) (.constant b)) (.constant (a * b))
  | add_zero (a) : Preserves (.add a (.constant 0)) a
  | mul_one (a) : Preserves (.mul a (.constant 1)) a
  | mul_zero (a) : Preserves (.mul a (.constant 0)) (.constant 0)
  | add_congr {a b c d} : Preserves a c → Preserves b d →
      Preserves (.add a b) (.add c d)
  | sub_congr {a b c d} : Preserves a c → Preserves b d →
      Preserves (.sub a b) (.sub c d)
  | mul_congr {a b c d} : Preserves a c → Preserves b d →
      Preserves (.mul a b) (.mul c d)

theorem Preserves.eval_eq {inputs lanes : Nat} {a b : Expr inputs}
    (proof : Preserves a b) (values : Fin inputs → Fin lanes → F) :
    a.eval values = b.eval values := by
  induction proof with
  | refl => rfl
  | trans _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond
  | add_comm a b =>
      funext lane
      exact _root_.add_comm _ _
  | mul_comm a b =>
      funext lane
      exact _root_.mul_comm _ _
  | add_const a b => rfl
  | sub_const a b => rfl
  | mul_const a b => rfl
  | add_zero a =>
      funext lane
      exact _root_.add_zero _
  | mul_one a =>
      funext lane
      exact _root_.mul_one _
  | mul_zero a =>
      funext lane
      simp [Expr.eval]
  | add_congr _ _ ihLeft ihRight =>
      funext lane
      exact congrArg₂ (· + ·) (congrFun ihLeft lane) (congrFun ihRight lane)
  | sub_congr _ _ ihLeft ihRight =>
      funext lane
      exact congrArg₂ (· - ·) (congrFun ihLeft lane) (congrFun ihRight lane)
  | mul_congr _ _ ihLeft ihRight =>
      funext lane
      exact congrArg₂ (· * ·) (congrFun ihLeft lane) (congrFun ihRight lane)

/-- One certificate entry per source name, indexed by the native source map.
Duplicate target IDs are valid only when each source expression has a proof
against the shared target. This is independent of a finite input assignment. -/
def SourceMapSound {inputs : Nat} (source optimized : List (Expr inputs))
    (sourceToCanonical : List Nat) : Prop :=
  ∀ (sourceId canonicalId : Nat) (original compact : Expr inputs),
    sourceToCanonical[sourceId]? = some canonicalId →
    source[sourceId]? = some original →
    optimized[canonicalId]? = some compact →
    Preserves original compact

theorem mapped_output_eq {inputs lanes : Nat}
    {source optimized : List (Expr inputs)} {sourceToCanonical : List Nat}
    (sound : SourceMapSound source optimized sourceToCanonical)
    (sourceId canonicalId : Nat) (original compact : Expr inputs)
    (hmap : sourceToCanonical[sourceId]? = some canonicalId)
    (hsource : source[sourceId]? = some original)
    (hcompact : optimized[canonicalId]? = some compact)
    (values : Fin inputs → Fin lanes → F) :
    original.eval values = compact.eval values :=
  (sound sourceId canonicalId original compact hmap hsource hcompact).eval_eq values

end S31.Functional.Correspondence.Optimizer
