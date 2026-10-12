import S31.Gadgets.Functional.Conditional

/-!
Post-typecheck model of source tuples and nominal records whose leaves are
M31 values. The Python frontend checks the source type and nominal identity;
this model concerns their first-order erasure. Every leaf uses the existing
field selector, so there is no product witness or product AIR operation.

The model does not prove that the production Python compiler emitted these
constraints or that the native verifier enforces the selected AIR. Those are
separate compiler and AIR correspondence obligations.
-/

namespace S31.Functional.ProductControl

inductive Shape where
  | field
  | pair (left right : Shape)
deriving DecidableEq

def Value : Shape → Type
  | .field => M31
  | .pair left right => Value left × Value right

/-- Structural source choice is exactly one existing field constraint per
leaf, in declaration order. -/
def Select : (shape : Shape) → (selector : M31) →
    (onFalse onTrue output : Value shape) → Prop
  | .field, selector, onFalse, onTrue, output =>
      fieldSelect selector onFalse onTrue output
  | .pair left right, selector, onFalse, onTrue, output =>
      Select left selector onFalse.1 onTrue.1 output.1 ∧
        Select right selector onFalse.2 onTrue.2 output.2

/-- Whole-product equality adds exactly its existing per-leaf equality
assertions; no extra relation node is required. -/
def Equal : (shape : Shape) → (left right : Value shape) → Prop
  | .field, left, right => left = right
  | .pair first second, left, right =>
      Equal first left.1 right.1 ∧ Equal second left.2 right.2

theorem equal_iff (shape : Shape) (left right : Value shape) :
    Equal shape left right ↔ left = right := by
  induction shape with
  | field => rfl
  | pair first second ihFirst ihSecond =>
      change (Equal first left.1 right.1 ∧ Equal second left.2 right.2) ↔ left = right
      constructor
      · intro accepted
        exact Prod.ext
          ((ihFirst left.1 right.1).mp accepted.1)
          ((ihSecond left.2 right.2).mp accepted.2)
      · intro same
        subst right
        exact ⟨(ihFirst left.1 left.1).mpr rfl,
          (ihSecond left.2 left.2).mpr rfl⟩

theorem select_zero_iff (shape : Shape) (onFalse onTrue output : Value shape) :
    Select shape 0 onFalse onTrue output ↔ output = onFalse := by
  induction shape with
  | field =>
      have hzero : (0 : M31) ≠ 1 := by decide
      simpa [Select, hzero] using (field_select_iff 0 onFalse onTrue output)
  | pair first second ihFirst ihSecond =>
      change (Select first 0 onFalse.1 onTrue.1 output.1 ∧
        Select second 0 onFalse.2 onTrue.2 output.2) ↔ output = onFalse
      constructor
      · intro accepted
        exact Prod.ext
          ((ihFirst onFalse.1 onTrue.1 output.1).mp accepted.1)
          ((ihSecond onFalse.2 onTrue.2 output.2).mp accepted.2)
      · intro chosen
        subst output
        exact ⟨(ihFirst onFalse.1 onTrue.1 onFalse.1).mpr rfl,
          (ihSecond onFalse.2 onTrue.2 onFalse.2).mpr rfl⟩

theorem select_one_iff (shape : Shape) (onFalse onTrue output : Value shape) :
    Select shape 1 onFalse onTrue output ↔ output = onTrue := by
  induction shape with
  | field =>
      have hone : (1 : M31) ≠ 0 := by decide
      simpa [Select, hone] using (field_select_iff 1 onFalse onTrue output)
  | pair first second ihFirst ihSecond =>
      change (Select first 1 onFalse.1 onTrue.1 output.1 ∧
        Select second 1 onFalse.2 onTrue.2 output.2) ↔ output = onTrue
      constructor
      · intro accepted
        exact Prod.ext
          ((ihFirst onFalse.1 onTrue.1 output.1).mp accepted.1)
          ((ihSecond onFalse.2 onTrue.2 output.2).mp accepted.2)
      · intro chosen
        subst output
        exact ⟨(ihFirst onFalse.1 onTrue.1 onTrue.1).mpr rfl,
          (ihSecond onFalse.2 onTrue.2 onTrue.2).mpr rfl⟩

theorem select_bit (shape : Shape) (selector : M31)
    (onFalse onTrue output : Value shape)
    (accepted : Select shape selector onFalse onTrue output) :
    selector = 0 ∨ selector = 1 := by
  induction shape generalizing selector with
  | field =>
      rcases (field_select_iff selector onFalse onTrue output).mp accepted with
        ⟨zero, _⟩ | ⟨one, _⟩
      · exact Or.inl zero
      · exact Or.inr one
  | pair first second ihFirst ihSecond =>
      exact ihFirst selector onFalse.1 onTrue.1 output.1 accepted.1

/-- Any satisfying leaf witnesses select exactly one whole product, and both
choices have honest leaf witnesses. This covers arbitrary nested pairs; a
nominal record becomes such a pair tree only after source type checking. -/
theorem select_iff (shape : Shape) (selector : M31)
    (onFalse onTrue output : Value shape) :
    Select shape selector onFalse onTrue output ↔
      (selector = 0 ∧ output = onFalse) ∨
      (selector = 1 ∧ output = onTrue) := by
  constructor
  · intro accepted
    rcases select_bit shape selector onFalse onTrue output accepted with zero | one
    · subst selector
      exact Or.inl ⟨rfl, (select_zero_iff shape onFalse onTrue output).mp accepted⟩
    · subst selector
      exact Or.inr ⟨rfl, (select_one_iff shape onFalse onTrue output).mp accepted⟩
  · rintro (⟨zero, chosen⟩ | ⟨one, chosen⟩)
    · subst selector
      exact (select_zero_iff shape onFalse onTrue output).mpr chosen
    · subst selector
      exact (select_one_iff shape onFalse onTrue output).mpr chosen

end S31.Functional.ProductControl
