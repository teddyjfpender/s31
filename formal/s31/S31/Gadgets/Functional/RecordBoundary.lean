import S31.Gadgets.Functional.Graph

/-!
An abstract model of the proposed public record ABI v2. A validated nominal
layout is represented by a binary product tree; each leaf is one first-order
value. This file proves flatten/reconstruct and alias projection facts, not
that the production Python compiler or Zig native verifier implements v2.
-/

namespace S31.Functional.RecordBoundary

inductive Layout where
  | leaf
  | pair (left right : Layout)
deriving Repr, DecidableEq

def Value (α : Type) : Layout → Type
  | .leaf => α
  | .pair left right => Value α left × Value α right

def flatten {α : Type} : (layout : Layout) → Value α layout → List α
  | .leaf, value => [value]
  | .pair left right, (a, b) => flatten left a ++ flatten right b

def reconstruct {α : Type} : (layout : Layout) → List α →
    Option (Value α layout × List α)
  | .leaf, [] => none
  | .leaf, head :: tail => some (head, tail)
  | .pair left right, words => do
      let (a, afterLeft) ← reconstruct left words
      let (b, afterRight) ← reconstruct right afterLeft
      pure ((a, b), afterRight)

/-- Parsing a typed value's flattened leaves consumes exactly those leaves,
even when more words follow. This is the core inverse needed at the ABI edge. -/
theorem reconstruct_flatten_append {α : Type} (layout : Layout)
    (value : Value α layout) (tail : List α) :
    reconstruct layout (flatten layout value ++ tail) = some (value, tail) := by
  induction layout generalizing tail with
  | leaf =>
      simp [Value, flatten, reconstruct]
  | pair left right ihLeft ihRight =>
      rcases value with ⟨a, b⟩
      simp [flatten, reconstruct, List.append_assoc,
        ihLeft a (flatten right b ++ tail), ihRight b tail]

/-- A well-typed, exact leaf sequence reconstructs the original product. -/
theorem reconstruct_flatten {α : Type} (layout : Layout)
    (value : Value α layout) :
    reconstruct layout (flatten layout value) = some (value, []) := by
  simpa using reconstruct_flatten_append layout value []

/-- Distinct well-typed values cannot silently flatten to identical leaves. -/
theorem flatten_injective {α : Type} (layout : Layout) :
    Function.Injective (flatten (α := α) layout) := by
  intro left right equalWords
  have leftRoundtrip := reconstruct_flatten layout left
  have rightRoundtrip := reconstruct_flatten layout right
  rw [equalWords, rightRoundtrip] at leftRoundtrip
  exact congrArg Prod.fst (Option.some.inj leftRoundtrip).symm

/-- A path is indexed by its checked product layout. `false` and `true`
encode its left and right edges; source field names are a separate nominal
layout check before this model is applied. -/
inductive Path : Layout → Type where
  | here : Path .leaf
  | left {a b : Layout} (child : Path a) : Path (.pair a b)
  | right {a b : Layout} (child : Path b) : Path (.pair a b)

def encodePath : {layout : Layout} → Path layout → List Bool
  | _, .here => []
  | _, .left child => false :: encodePath child
  | _, .right child => true :: encodePath child

/-- Distinct product positions have distinct tagged paths. This abstract
binary encoding corresponds to field and tuple tags after layout validation. -/
theorem encodePath_injective {layout : Layout} :
    Function.Injective (@encodePath layout) := by
  intro first second equalPath
  induction first with
  | here =>
      cases second
      rfl
  | left child ih =>
      cases second with
      | left other =>
          have equalChild : encodePath child = encodePath other :=
            (List.cons.inj equalPath).2
          exact congrArg Path.left (ih equalChild)
      | right other => cases equalPath
  | right child ih =>
      cases second with
      | left other => cases equalPath
      | right other =>
          have equalChild : encodePath child = encodePath other :=
            (List.cons.inj equalPath).2
          exact congrArg Path.right (ih equalChild)

/-- Two named fields may deliberately reference one relation wire. Their
public claims must then be equal, and the underlying wire remains singular. -/
def projectAliases {α : Type} {n : Nat} (wires : Fin n → α)
    (paths : List (Fin n)) : List α :=
  paths.map wires

theorem repeated_wire_claims_equal {α : Type} {n : Nat} (wires : Fin n → α)
    (wire : Fin n) :
    projectAliases wires [wire, wire] = [wires wire, wires wire] := rfl

theorem repeated_wire_claims_identical {α : Type} {n : Nat}
    (wires : Fin n → α) (wire : Fin n) :
    (projectAliases wires [wire, wire]).head? =
      (List.drop 1 (projectAliases wires [wire, wire])).head? := rfl

end S31.Functional.RecordBoundary
