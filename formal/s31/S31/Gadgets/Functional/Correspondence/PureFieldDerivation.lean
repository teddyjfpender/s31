import S31.Gadgets.Functional.Correspondence.GeneralLinearSSA
import S31.Semantics.Field

/-!
Compositional semantic kernel for the versioned pure-field derivation profile.
The Python checker independently parses exact source bytes and checks each
typed named rule against the complete normalized relation. This theorem says
that lowering any sequence of those rules preserves its partial field
denotation, including inverse-zero failure and selector Booleanity.

It does not prove the Python byte parser correct, establish optimizer or native
AIR refinement, or authenticate PCS openings.
-/

namespace S31.Functional.Correspondence.PureFieldDerivation

abbrev Word := S31.M31
abbrev Value := List Word
abbrev State := List Value

inductive SourceRule where
  | add | sub | mul | inv | isZero | select
  deriving DecidableEq, Repr

inductive NormalizedRule where
  | add | sub | mul | inv | isZero | select
  deriving DecidableEq, Repr

def lowerRule : SourceRule → NormalizedRule
  | .add => .add | .sub => .sub | .mul => .mul
  | .inv => .inv | .isZero => .isZero | .select => .select

private def binary (f : Word → Word → Word) : List Value → Option Value
  | [left, right] =>
      if left.length == right.length then
        some (List.zipWith f left right)
      else none
  | _ => none

private def inverse : List Value → Option Value
  | [input] =>
      if input.any (· == 0) then none else some (input.map S31.Field.inverse)
  | _ => none

private def zeroTest : List Value → Option Value
  | [[input]] => some [if input == 0 then 1 else 0]
  | _ => none

private def choice : List Value → Option Value
  | [[selector], onFalse, onTrue] =>
      if onFalse.length != onTrue.length then none
      else if selector == 0 then some onFalse
      else if selector == 1 then some onTrue
      else none
  | _ => none

/-- Source field semantics are partial exactly where inversion at zero or a
non-Boolean selector would make the production evaluator fail. -/
def SourceRule.eval : SourceRule → List Value → Option Value
  | .add => binary (· + ·)
  | .sub => binary (· - ·)
  | .mul => binary (· * ·)
  | .inv => inverse
  | .isZero => zeroTest
  | .select => choice

/-- A separate normalized operation decoder; the equality with the source
rules is proved for every constructor below. -/
def NormalizedRule.eval : NormalizedRule → List Value → Option Value
  | .add => binary (· + ·)
  | .sub => binary (· - ·)
  | .mul => binary (· * ·)
  | .inv => inverse
  | .isZero => zeroTest
  | .select => choice

theorem lower_rule_eval (rule : SourceRule) (args : List Value) :
    (lowerRule rule).eval args = rule.eval args := by
  cases rule <;> rfl

structure SourceStep where
  rule : SourceRule
  refs : List Nat
  deriving DecidableEq, Repr

structure NormalizedStep where
  rule : NormalizedRule
  refs : List Nat
  deriving DecidableEq, Repr

def lowerStep (step : SourceStep) : NormalizedStep :=
  ⟨lowerRule step.rule, step.refs⟩

def sourceStep (state : State) (step : SourceStep) : Option State := do
  let args ← step.refs.mapM (state[·]?)
  let result ← step.rule.eval args
  return state ++ [result]

def normalizedStep (state : State) (step : NormalizedStep) : Option State := do
  let args ← step.refs.mapM (state[·]?)
  let result ← step.rule.eval args
  return state ++ [result]

theorem lower_step (state : State) (step : SourceStep) :
    normalizedStep state (lowerStep step) = sourceStep state step := by
  simp only [normalizedStep, sourceStep, lowerStep, lower_rule_eval]

/-- Composition is length-independent: every accepted typed rule sequence
has the same success/failure and the same full value state after lowering. -/
theorem lower_run (steps : List SourceStep) (initial : State) :
    (steps.map lowerStep).foldlM normalizedStep initial =
      steps.foldlM sourceStep initial := by
  induction steps generalizing initial with
  | nil => rfl
  | cons step rest ih =>
      simp only [List.map_cons, List.foldlM_cons]
      rw [lower_step]
      cases h : sourceStep initial step with
      | none => simp
      | some next => simpa [h] using ih next

/-- A final output lookup preserves both the selected public value and the
same partial failure conditions across an arbitrarily long derivation. -/
theorem lower_output (steps : List SourceStep) (initial : State)
    (output : Nat) :
    ((steps.map lowerStep).foldlM normalizedStep initial).bind (·[output]?) =
      (steps.foldlM sourceStep initial).bind (·[output]?) := by
  rw [lower_run]

end S31.Functional.Correspondence.PureFieldDerivation
