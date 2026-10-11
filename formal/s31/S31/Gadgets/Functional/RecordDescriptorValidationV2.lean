import S31.Gadgets.Functional.RecordLayoutValidationV2

/-!
An executable whole-descriptor shape check for public record ABI v2. The
input is an already parsed, explicitly named type tree. `checkDescriptor`
checks all roots together: local shape, the aggregate leaf budget, root names,
private `bit` exclusion, and equality of complete type structures sharing a
nominal record name. It also requires a top-level record boundary, as the
native v2 validator does.

The theorem does not identify this model with native JSON parser output,
check identifier spelling, relate leaves to first-order relation wires,
authenticate a descriptor digest, or establish verifier acceptance.
-/

namespace S31.Functional.RecordDescriptorValidationV2

open RecordAbiV2 RecordLayoutValidationV2

inductive NamedLayout where
  | leaf (kind : PublicLeafKind) (width : Nat)
  | record (nominal : String) (arity : Nat) (fieldName : Fin arity → String)
      (child : Fin arity → NamedLayout)
  | tuple (arity : Nat) (child : Fin arity → NamedLayout)

def toRaw : NamedLayout → RawLayout
  | .leaf kind width => .leaf kind width
  | .record _ arity names child => .record arity names (fun i => toRaw (child i))
  | .tuple arity child => .tuple arity (fun i => toRaw (child i))

/-- Arity-tagged preorder tokens uniquely delimit a finite type tree.
They preserve declaration order, names, kinds, and widths without requiring
recursive decidable equality on a higher-order child representation. -/
inductive TypeToken where
  | leaf (kind : PublicLeafKind) (width : Nat)
  | record (name : String) (arity : Nat)
  | field (name : String)
  | tuple (arity : Nat)
  deriving DecidableEq

def typeCode : NamedLayout → List TypeToken
  | .leaf kind width => [.leaf kind width]
  | .record name arity names child =>
      [.record name arity] ++
        ((List.finRange arity).flatMap fun i =>
          [.field (names i)] ++ typeCode (child i))
  | .tuple arity child =>
      [.tuple arity] ++
        ((List.finRange arity).flatMap fun i => typeCode (child i))

def nominalOccurrences : NamedLayout → List (String × List TypeToken)
  | .leaf _ _ => []
  | .record name arity names child =>
      (name, typeCode (.record name arity names child)) ::
        ((List.finRange arity).flatMap fun i => nominalOccurrences (child i))
  | .tuple arity child =>
      (List.finRange arity).flatMap fun i => nominalOccurrences (child i)

def noPrivateBit : NamedLayout → Bool
  | .leaf kind _ => decide (kind ≠ .bit)
  | .record _ arity _ child =>
      (List.finRange arity).all fun i => noPrivateBit (child i)
  | .tuple arity child =>
      (List.finRange arity).all fun i => noPrivateBit (child i)

theorem noPrivateBit_leaf (layout : NamedLayout)
    (accepted : noPrivateBit layout = true) :
    ∀ position : LeafPosition (erase (toRaw layout)),
      leafKindAt (toRaw layout) position ≠ .bit := by
  induction layout with
  | leaf kind width =>
      intro position
      cases position
      simpa [noPrivateBit, toRaw, leafKindAt] using accepted
  | record name arity names child ih =>
      intro position
      rcases position with ⟨i, tail⟩
      have childAccepted : noPrivateBit (child i) = true := by
        have h := accepted
        simp only [noPrivateBit, List.all_eq_true] at h
        exact h i (List.mem_finRange i)
      simpa [toRaw, leafKindAt] using ih i childAccepted tail
  | tuple arity child ih =>
      intro position
      rcases position with ⟨i, tail⟩
      have childAccepted : noPrivateBit (child i) = true := by
        have h := accepted
        simp only [noPrivateBit, List.all_eq_true] at h
        exact h i (List.mem_finRange i)
      simpa [toRaw, leafKindAt] using ih i childAccepted tail

inductive Visibility where
  | pub | priv
  deriving DecidableEq, Repr

structure InputRoot where
  name : String
  visibility : Visibility
  layout : NamedLayout

structure ResultRoot where
  name : String
  layout : NamedLayout

structure Descriptor where
  inputs : List InputRoot
  result : ResultRoot

def isTopRecord : NamedLayout → Bool
  | .record _ _ _ _ => true
  | _ => false

def allNominals (descriptor : Descriptor) : List (String × List TypeToken) :=
  (descriptor.inputs.flatMap fun root => nominalOccurrences root.layout) ++
    nominalOccurrences descriptor.result.layout

/-- A repeated nominal name must denote the same full declaration-order
type, including each nested nominal name. Both traversal directions are
checked, making the later two-occurrence theorem direct. -/
def checkNominals (descriptor : Descriptor) : Bool :=
  (allNominals descriptor).all fun a =>
    (allNominals descriptor).all fun b =>
      decide (a.1 = b.1 → a.2 = b.2)

abbrev NominalConsistent (descriptor : Descriptor) : Prop :=
  checkNominals descriptor = true

def totalLeaves (descriptor : Descriptor) : Nat :=
  (descriptor.inputs.map fun root => leafCount (toRaw root.layout)).sum +
    leafCount (toRaw descriptor.result.layout)

/-- This is the shape fragment of the native descriptor validator. The
per-root checker includes depth, arity, sibling fields, and leaf widths. -/
abbrev ValidDescriptor (descriptor : Descriptor) : Prop :=
  descriptor.inputs.all (fun root => checkNativeRoot (toRaw root.layout)) = true ∧
  checkNativeRoot (toRaw descriptor.result.layout) = true ∧
  descriptor.inputs.all (fun root =>
    if root.visibility = .priv then noPrivateBit root.layout else true) = true ∧
  (descriptor.inputs.map InputRoot.name).Nodup ∧
  descriptor.result.name = "result" ∧
  descriptor.result.name ∉ descriptor.inputs.map InputRoot.name ∧
  totalLeaves descriptor ≤ 1024 ∧
  NominalConsistent descriptor ∧
  (isTopRecord descriptor.result.layout = true ∨
    descriptor.inputs.any (fun root => isTopRecord root.layout) = true)

def checkDescriptor (descriptor : Descriptor) : Bool :=
  decide (ValidDescriptor descriptor)

theorem checkDescriptor_iff (descriptor : Descriptor) :
    checkDescriptor descriptor = true ↔ ValidDescriptor descriptor := by
  simp only [checkDescriptor, decide_eq_true_eq]

/-- Acceptance derives every local tree premise; no separate trusted
per-root shape hypothesis is needed downstream. -/
theorem checked_input_root (descriptor : Descriptor)
    (accepted : checkDescriptor descriptor = true)
    (root : InputRoot) (member : root ∈ descriptor.inputs) :
    checkRoot (toRaw root.layout) = true ∧
    WellTagged (erase (toRaw root.layout)) ∧
    ∀ position : LeafPosition (erase (toRaw root.layout)),
      ValidLeaf (leafKindAt (toRaw root.layout) position)
        (leafWidthAt (toRaw root.layout) position) := by
  have valid := (checkDescriptor_iff descriptor).mp accepted
  have checked : checkNativeRoot (toRaw root.layout) = true := by
    have h := valid.1
    simp only [List.all_eq_true] at h
    exact h root member
  have hroot := checkNativeRoot_checked (toRaw root.layout) checked
  exact ⟨hroot, checkRoot_wellTagged _ hroot,
    fun position => checkRoot_leafValid _ hroot position⟩

theorem checked_result_root (descriptor : Descriptor)
    (accepted : checkDescriptor descriptor = true) :
    checkRoot (toRaw descriptor.result.layout) = true ∧
    WellTagged (erase (toRaw descriptor.result.layout)) ∧
    ∀ position : LeafPosition (erase (toRaw descriptor.result.layout)),
      ValidLeaf (leafKindAt (toRaw descriptor.result.layout) position)
        (leafWidthAt (toRaw descriptor.result.layout) position) := by
  have valid := (checkDescriptor_iff descriptor).mp accepted
  have hroot := checkNativeRoot_checked (toRaw descriptor.result.layout) valid.2.1
  exact ⟨hroot, checkRoot_wellTagged _ hroot,
    fun position => checkRoot_leafValid _ hroot position⟩

theorem checked_private_input_no_bits (descriptor : Descriptor)
    (accepted : checkDescriptor descriptor = true)
    (root : InputRoot) (member : root ∈ descriptor.inputs)
    (privateRoot : root.visibility = .priv) :
    ∀ position : LeafPosition (erase (toRaw root.layout)),
      leafKindAt (toRaw root.layout) position ≠ .bit := by
  have valid := (checkDescriptor_iff descriptor).mp accepted
  have h := valid.2.2.1
  simp only [List.all_eq_true] at h
  have checked := h root member
  simp [privateRoot] at checked
  exact noPrivateBit_leaf root.layout checked

theorem checked_global_budget (descriptor : Descriptor)
    (accepted : checkDescriptor descriptor = true) :
    totalLeaves descriptor ≤ 1024 := by
  exact ((checkDescriptor_iff descriptor).mp accepted).2.2.2.2.2.2.1

theorem checked_nominals (descriptor : Descriptor)
    (accepted : checkDescriptor descriptor = true) :
    NominalConsistent descriptor := by
  exact ((checkDescriptor_iff descriptor).mp accepted).2.2.2.2.2.2.2.1

theorem checked_nominal_pair (descriptor : Descriptor)
    (accepted : checkDescriptor descriptor = true)
    (a b : String × List TypeToken)
    (aMember : a ∈ allNominals descriptor)
    (bMember : b ∈ allNominals descriptor)
    (sameName : a.1 = b.1) : a.2 = b.2 := by
  have h := checked_nominals descriptor accepted
  simp only [NominalConsistent, checkNominals, List.all_eq_true] at h
  exact (decide_eq_true_eq.mp (h a aMember b bMember)) sameName

/-- A one-field nominal record repeated at the input and result. -/
def pairType (width : Nat) : NamedLayout :=
  .record "Pair" 1 (fun _ => "value") (fun _ => .leaf .m31 width)

def exampleDescriptor : Descriptor :=
  { inputs := [{ name := "x", visibility := .pub, layout := pairType 1 }]
    result := { name := "result", layout := pairType 1 } }

theorem exampleDescriptor_accepted : checkDescriptor exampleDescriptor = true := by decide

def privateBitDescriptor : Descriptor :=
  { inputs := [{ name := "flag", visibility := .priv,
                 layout := .leaf .bit 1 }]
    result := { name := "result", layout := pairType 1 } }

theorem privateBitDescriptor_rejected :
    checkDescriptor privateBitDescriptor = false := by decide

def nominalMismatchDescriptor : Descriptor :=
  { inputs := [{ name := "x", visibility := .pub, layout := pairType 1 }]
    result := { name := "result", layout := pairType 2 } }

theorem nominalMismatchDescriptor_rejected :
    checkDescriptor nominalMismatchDescriptor = false := by decide

def duplicateRootDescriptor : Descriptor :=
  { inputs := [
      { name := "x", visibility := .pub, layout := pairType 1 },
      { name := "x", visibility := .pub, layout := pairType 1 }]
    result := { name := "result", layout := pairType 1 } }

theorem duplicateRootDescriptor_rejected :
    checkDescriptor duplicateRootDescriptor = false := by decide

def resultCollisionDescriptor : Descriptor :=
  { inputs := [{ name := "result", visibility := .pub, layout := pairType 1 }]
    result := { name := "result", layout := pairType 1 } }

theorem resultCollisionDescriptor_rejected :
    checkDescriptor resultCollisionDescriptor = false := by decide

theorem overBudget_rejected (descriptor : Descriptor)
    (tooMany : 1024 < totalLeaves descriptor) :
    checkDescriptor descriptor = false := by
  cases h : checkDescriptor descriptor with
  | false => rfl
  | true =>
      have within := checked_global_budget descriptor h
      exact False.elim ((Nat.not_le_of_gt tooMany) within)

end S31.Functional.RecordDescriptorValidationV2
