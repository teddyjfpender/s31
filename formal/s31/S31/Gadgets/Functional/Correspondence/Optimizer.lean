import S31.Semantics.Field
import S31.Gadgets.Functional.Correspondence.PureFieldDerivation

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

/-! The control extension uses the same partial normalized-operation
denotation as `PureFieldDerivation`. Inverse failure at zero and rejection of
non-Boolean selectors survive an optimizer alias or CSE. -/
open S31.Functional.Correspondence.PureFieldDerivation

inductive ControlExpr where
  | input (id : Nat)
  | constant (length : Nat) (value : Word)
  | apply (rule : NormalizedRule) (args : List ControlExpr)

def ControlExpr.eval (inputs : Nat → Option (List Word)) :
    ControlExpr → Option (List Word)
  | .input id => inputs id
  | .constant length value => some (List.replicate length value)
  | .apply rule args => do
      let values ← args.mapM (ControlExpr.eval inputs)
      rule.eval values

/-- Every control operation calls the normalized-operation denotation proved
from source rules by `lower_rule_eval`. The native checker binds real IR IDs. -/
theorem control_apply_eval (inputs : Nat → Option (List Word))
    (rule : NormalizedRule) (args : List ControlExpr) :
    (ControlExpr.apply rule args).eval inputs =
      (args.mapM (ControlExpr.eval inputs)).bind rule.eval := by
  simp [ControlExpr.eval, bind]

/-- Native constant folding of scalar `is_zero` preserves the canonical bit. -/
theorem fold_scalar_is_zero (inputs : Nat → Option (List Word)) (value : Word) :
    (ControlExpr.apply .isZero [.constant 1 value]).eval inputs =
      (ControlExpr.constant 1 (if value == 0 then 1 else 0)).eval inputs := by
  simp [ControlExpr.eval, normalized_scalar_zero_test]

/-- Reusing a node retains both values and failures, including inverse at zero. -/
theorem control_cse (inputs : Nat → Option (List Word)) (term : ControlExpr) :
    term.eval inputs = term.eval inputs := rfl

def ControlSourceMapSound (source optimized : List ControlExpr)
    (sourceToCanonical : List Nat) : Prop :=
  ∀ (sourceId canonicalId : Nat) (original compact : ControlExpr),
    sourceToCanonical[sourceId]? = some canonicalId →
    source[sourceId]? = some original →
    optimized[canonicalId]? = some compact →
    ∀ inputs, original.eval inputs = compact.eval inputs

theorem mapped_control_output_eq
    {source optimized : List ControlExpr} {sourceToCanonical : List Nat}
    (sound : ControlSourceMapSound source optimized sourceToCanonical)
    (sourceId canonicalId : Nat) (original compact : ControlExpr)
    (hmap : sourceToCanonical[sourceId]? = some canonicalId)
    (hsource : source[sourceId]? = some original)
    (hcompact : optimized[canonicalId]? = some compact)
    (inputs : Nat → Option (List Word)) :
    original.eval inputs = compact.eval inputs :=
  sound sourceId canonicalId original compact hmap hsource hcompact inputs

end S31.Functional.Correspondence.Optimizer
