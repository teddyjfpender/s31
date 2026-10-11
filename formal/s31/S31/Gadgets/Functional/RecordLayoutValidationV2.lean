import S31.Gadgets.Functional.RecordWordBoundaryV2

/-!
Executable validation of the *shape* of a public record ABI v2 type tree.
The raw constructors distinguish named record fields from tuple indices and
carry every leaf's declared kind and width. Unlike `WellTagged`, this input
contains no path-uniqueness proof. `checkRoot` checks finite local
obligations from the production type-tree walk: nonempty bounded nodes,
distinct sibling field names, depth, a per-root leaf bound, and M31/bit/u16
leaf widths.

The theorems discharge the tag and width premises of the generic nested
flattening theorem. They start from an already parsed raw tree and a separate
word block for each position. JSON parsing, lexical name validation,
record-name/nominal consistency across roots, the aggregate 1,024-leaf
budget, rejection of private input bit leaves, descriptor-to-relation wire
binding, canonical word values, SHA-256 and proof authentication remain
outside this module.
-/

namespace S31.Functional.RecordLayoutValidationV2

open RecordBoundary RecordAbiV2 RecordWordBoundaryV2

inductive RawLayout where
  | leaf (kind : PublicLeafKind) (width : Nat)
  | record (arity : Nat) (fieldName : Fin arity → String)
      (child : Fin arity → RawLayout)
  | tuple (arity : Nat) (child : Fin arity → RawLayout)

def erase : RawLayout → NominalTree
  | .leaf _ _ => .leaf
  | .record arity names child =>
      namedRecord arity names (fun index => erase (child index))
  | .tuple arity child =>
      indexedTuple arity (fun index => erase (child index))

def leafCount : RawLayout → Nat
  | .leaf _ _ => 1
  | .record arity _ child =>
      ((List.finRange arity).map fun index => leafCount (child index)).sum
  | .tuple arity child =>
      ((List.finRange arity).map fun index => leafCount (child index)).sum

def ValidLeaf (kind : PublicLeafKind) (width : Nat) : Prop :=
  1 ≤ width ∧ width ≤ 8 ∧ (kind = .bit → width = 1) ∧
    (kind = .u8 → width = 1)

def checkLeaf (kind : PublicLeafKind) (width : Nat) : Bool :=
  decide (1 ≤ width) && decide (width ≤ 8) &&
    decide (kind = .bit → width = 1) &&
    decide (kind = .u8 → width = 1)

theorem checkLeaf_iff (kind : PublicLeafKind) (width : Nat) :
    checkLeaf kind width = true ↔ ValidLeaf kind width := by
  simp only [checkLeaf, Bool.and_eq_true, decide_eq_true_eq, ValidLeaf]
  tauto

/-- `remaining` counts allowed record/tuple edges; a leaf needs no edge. -/
def checkLayout : Nat → RawLayout → Bool
  | _, .leaf kind width => checkLeaf kind width
  | 0, .record _ _ _ => false
  | remaining + 1, .record arity names child =>
      decide (1 ≤ arity) && decide (arity ≤ 64) &&
      decide (Function.Injective names) &&
      (List.finRange arity).all (fun index => checkLayout remaining (child index))
  | 0, .tuple _ _ => false
  | remaining + 1, .tuple arity child =>
      decide (1 ≤ arity) && decide (arity ≤ 64) &&
      (List.finRange arity).all (fun index => checkLayout remaining (child index))

def checkRoot (layout : RawLayout) : Bool :=
  checkLayout 32 layout && decide (leafCount layout ≤ 1024)

/-- The native ABI permits a scalar or named record at a root; tuples occur
only below a named record field. `checkRoot` itself describes the reusable
tree walk and intentionally permits a tuple at its entry point. -/
def checkNativeRoot (layout : RawLayout) : Bool :=
  match layout with
  | .tuple _ _ => false
  | _ => checkRoot layout

theorem checkNativeRoot_checked (layout : RawLayout)
    (accepted : checkNativeRoot layout = true) : checkRoot layout = true := by
  cases layout <;> simp [checkNativeRoot] at accepted ⊢
  all_goals assumption

/-- A checked raw tree has the local sibling uniqueness needed to make every
complete rooted path unique, at every nesting depth. -/
theorem checkLayout_wellTagged (layout : RawLayout) :
    ∀ remaining, checkLayout remaining layout = true → WellTagged (erase layout) := by
  induction layout with
  | leaf kind width =>
      intro remaining _
      trivial
  | record arity names child ih =>
      intro remaining accepted
      cases remaining with
      | zero => simp [checkLayout] at accepted
      | succ depth =>
          simp only [checkLayout, Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true] at accepted
          rcases accepted with ⟨⟨⟨_, _⟩, distinct⟩, checkedChildren⟩
          apply namedRecord_wellTagged arity names distinct
          intro index
          exact ih index depth (checkedChildren index (List.mem_finRange index))
  | tuple arity child ih =>
      intro remaining accepted
      cases remaining with
      | zero => simp [checkLayout] at accepted
      | succ depth =>
          simp only [checkLayout, Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true] at accepted
          rcases accepted with ⟨⟨_, _⟩, checkedChildren⟩
          apply indexedTuple_wellTagged arity
          intro index
          exact ih index depth (checkedChildren index (List.mem_finRange index))

def leafKindAt : (layout : RawLayout) → LeafPosition (erase layout) → PublicLeafKind
  | .leaf kind _, _ => kind
  | .record _ _ child, ⟨index, position⟩ => leafKindAt (child index) position
  | .tuple _ child, ⟨index, position⟩ => leafKindAt (child index) position

def leafWidthAt : (layout : RawLayout) → LeafPosition (erase layout) → Nat
  | .leaf _ width, _ => width
  | .record _ _ child, ⟨index, position⟩ => leafWidthAt (child index) position
  | .tuple _ child, ⟨index, position⟩ => leafWidthAt (child index) position

/-- Every position in an accepted raw layout has an allowed declared width;
public bit leaves in particular have exactly one word. -/
theorem checkLayout_leafValid (layout : RawLayout) :
    ∀ remaining, checkLayout remaining layout = true →
      ∀ position : LeafPosition (erase layout),
        ValidLeaf (leafKindAt layout position) (leafWidthAt layout position) := by
  induction layout with
  | leaf kind width =>
      intro remaining accepted position
      cases position
      exact (checkLeaf_iff kind width).mp (by simpa [checkLayout] using accepted)
  | record arity names child ih =>
      intro remaining accepted position
      cases remaining with
      | zero => simp [checkLayout] at accepted
      | succ depth =>
          simp only [checkLayout, Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true] at accepted
          rcases accepted with ⟨⟨⟨_, _⟩, _⟩, checkedChildren⟩
          rcases position with ⟨index, tail⟩
          exact ih index depth (checkedChildren index (List.mem_finRange index)) tail
  | tuple arity child ih =>
      intro remaining accepted position
      cases remaining with
      | zero => simp [checkLayout] at accepted
      | succ depth =>
          simp only [checkLayout, Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true] at accepted
          rcases accepted with ⟨⟨_, _⟩, checkedChildren⟩
          rcases position with ⟨index, tail⟩
          exact ih index depth (checkedChildren index (List.mem_finRange index)) tail

theorem checkRoot_wellTagged (layout : RawLayout)
    (accepted : checkRoot layout = true) : WellTagged (erase layout) := by
  have h : checkLayout 32 layout = true ∧ leafCount layout ≤ 1024 := by
    simpa [checkRoot] using accepted
  have checked := h.1
  exact checkLayout_wellTagged layout 32 checked

theorem checkRoot_leafValid (layout : RawLayout)
    (accepted : checkRoot layout = true)
    (position : LeafPosition (erase layout)) :
    ValidLeaf (leafKindAt layout position) (leafWidthAt layout position) := by
  have h : checkLayout 32 layout = true ∧ leafCount layout ≤ 1024 := by
    simpa [checkRoot] using accepted
  have checked := h.1
  exact checkLayout_leafValid layout 32 checked position

/-- The actual statement blocks must match the widths validated in the raw
descriptor. This premise is exactly the per-leaf width check in the native
claim loop, kept explicit rather than silently inferred from the type tree. -/
theorem checked_ordered_widths (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat)
    (accepted : checkRoot layout = true)
    (matching : ∀ position, (values position).width = leafWidthAt layout position) :
    ValidPublicWidths (orderedWidths root (erase layout) values) := by
  intro width present
  have ordered : orderedWidths root (erase layout) values =
      (orderedPositions (erase layout)).map (fun position => (values position).width) := by
    simp [orderedWidths, orderedRootLeaves, orderedNominalLeaves, List.map_map]
  rw [ordered] at present
  obtain ⟨position, _, sameWidth⟩ := List.mem_map.mp present
  rw [← sameWidth, matching position]
  have valid := checkRoot_leafValid layout accepted position
  exact ⟨valid.1, valid.2.1⟩

/-- Parsing and local shape validation now discharge *both* generic tree
premises: unique complete paths and valid ordered widths. Canonical numeric
values remain a separate statement check. -/
theorem checked_nested_public_boundary (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat)
    (accepted : checkRoot layout = true)
    (matching : ∀ position, (values position).width = leafWidthAt layout position)
    (canonical : CanonicalM31Words (orderedWords root (erase layout) values)) :
    ((orderedRootLeaves root (erase layout) values).map Prod.fst).Nodup ∧
      admitPublicWords (orderedWidths root (erase layout) values)
        (orderedWords root (erase layout) values) =
        some (((orderedRootLeaves root (erase layout) values).map Prod.snd).map
          WordBlock.words) := by
  exact validated_nested_public_boundary root (erase layout) values
    (checkRoot_wellTagged layout accepted)
    (checked_ordered_widths root layout values accepted matching) canonical

end S31.Functional.RecordLayoutValidationV2
