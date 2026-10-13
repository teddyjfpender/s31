import S31.Gadgets.Functional.Correspondence.StaticTupleErasure

/-!
The common typed product rule behind the executable structural derivation:
tuple indices, helper parameter positions, and record field names are all
resolved to a finite slot, then projection selects the wire in that slot.
The label-to-slot resolver is a checked premise. This theorem does not parse
source bytes or authenticate native AIR rows; the existing v1 byte-run theorem
provides the source/interpreter link for its admitted grammar.
-/

namespace S31.Functional.Correspondence.TypedStructuralProjection

structure Product (α : Type) (n : Nat) where
  fields : Fin n → α

def construct {α : Type} {n : Nat} (fields : Fin n → α) : Product α n :=
  ⟨fields⟩

def project {α : Type} {n : Nat} (value : Product α n) (slot : Fin n) : α :=
  value.fields slot

theorem project_construct {α : Type} {n : Nat}
    (fields : Fin n → α) (slot : Fin n) :
    project (construct fields) slot = fields slot := rfl

/-- A name or position is first checked against the product's typed layout.
The same rule handles `.0`, a helper's formal parameter slot, or `.field`.
No witness or normalized relation node is created by this selection. -/
def projectNamed {α κ : Type} {n : Nat}
    (layout : κ → Option (Fin n)) (value : Product α n) (key : κ) : Option α :=
  (layout key).map (project value)

theorem project_named_construct {α κ : Type} {n : Nat}
    (layout : κ → Option (Fin n)) (fields : Fin n → α)
    (key : κ) (slot : Fin n)
    (hslot : layout key = some slot) :
    projectNamed layout (construct fields) key = some (fields slot) := by
  simp [projectNamed, hslot, project_construct]

end S31.Functional.Correspondence.TypedStructuralProjection
