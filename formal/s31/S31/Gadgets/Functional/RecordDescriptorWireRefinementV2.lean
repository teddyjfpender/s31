import S31.Gadgets.Functional.RecordDescriptorLexicalV2
import S31.Gadgets.Functional.RecordStatementV2

/-!
An explicit bridge from an already parsed ABI v2 descriptor to the ordered
leaf descriptors consumed by the statement checker. The executable equality
check compares every emitted path, kind, width, and first-order relation wire.
The relation-wire reference function is an input: this module does not prove
that the native compiler or parser produced it, or that a proof authenticates
the descriptor or statement. In particular, JSON and digest equivalence are
separate obligations.
-/

namespace S31.Functional.RecordDescriptorWireRefinementV2

open RecordAbiV2 RecordLayoutValidationV2 RecordDescriptorValidationV2
  RecordDescriptorLexicalV2 RecordStatementV2

/-- The declaration-order statement leaf list for one public input root. -/
def expectedLeaves {n : Nat} (root : InputRoot)
    (refs : LeafPosition (erase (toRaw root.layout)) → Fin n) :
    List (RecordStatementV2.Descriptor n) :=
  (orderedPositions (erase (toRaw root.layout))).map fun position =>
    { path := rootedNominalPath root.name (erase (toRaw root.layout)) position
      kind := leafKindAt (toRaw root.layout) position
      width := leafWidthAt (toRaw root.layout) position
      wire := refs position }

/-- The relation leaf list must match the checked tree at every field,
including the wire reference. `refs` is supplied by the relation boundary. -/
def checkPublicInputBinding {n : Nat} (descriptor :
    RecordDescriptorValidationV2.Descriptor) (root : InputRoot)
    (refs : LeafPosition (erase (toRaw root.layout)) → Fin n)
    (relationLeaves : List (RecordStatementV2.Descriptor n)) : Bool :=
  checkLexicalDescriptor descriptor &&
    decide (root.visibility = .pub) &&
    decide (relationLeaves = expectedLeaves root refs)

theorem checked_public_input_binding {n : Nat}
    (descriptor : RecordDescriptorValidationV2.Descriptor)
    (root : InputRoot) (member : root ∈ descriptor.inputs)
    (refs : LeafPosition (erase (toRaw root.layout)) → Fin n)
    (relationLeaves : List (RecordStatementV2.Descriptor n))
    (accepted : checkPublicInputBinding descriptor root refs relationLeaves = true) :
    relationLeaves = expectedLeaves root refs ∧
      ((relationLeaves.map RecordStatementV2.Descriptor.path).Nodup) ∧
      ∀ leaf ∈ relationLeaves, ValidLeaf leaf.kind leaf.width := by
  have parts : checkLexicalDescriptor descriptor = true ∧
      root.visibility = .pub ∧ relationLeaves = expectedLeaves root refs := by
    simpa [checkPublicInputBinding, and_assoc] using accepted
  have shape : checkDescriptor descriptor = true :=
    (checkDescriptor_iff descriptor).mpr (checked_shape descriptor parts.1)
  have checked := checked_input_root descriptor shape root member
  have paths : (relationLeaves.map RecordStatementV2.Descriptor.path).Nodup := by
    rw [parts.2.2]
    have h := orderedRootLeaves_paths_nodup root.name
      (erase (toRaw root.layout)) refs checked.2.1
    simpa [expectedLeaves, orderedRootLeaves_paths, List.map_map] using h
  refine ⟨parts.2.2, paths, ?_⟩
  intro leaf present
  rw [parts.2.2] at present
  obtain ⟨position, _, same⟩ := List.mem_map.mp present
  subst leaf
  exact checked.2.2 position

/-- The positional claim checker now receives precisely the descriptor's
ordered paths and relation wire references; aliases remain checked by its
own executable pairwise test. -/
def checkPublicInputClaims {n : Nat}
    (descriptor : RecordDescriptorValidationV2.Descriptor)
    (root : InputRoot)
    (refs : LeafPosition (erase (toRaw root.layout)) → Fin n)
    (relationLeaves : List (RecordStatementV2.Descriptor n))
    (claims : List Claim) : Bool :=
  checkPublicInputBinding descriptor root refs relationLeaves &&
    admitClaims relationLeaves claims

theorem checked_public_input_claims {n : Nat}
    (descriptor : RecordDescriptorValidationV2.Descriptor)
    (root : InputRoot) (member : root ∈ descriptor.inputs)
    (refs : LeafPosition (erase (toRaw root.layout)) → Fin n)
    (relationLeaves : List (RecordStatementV2.Descriptor n))
    (claims : List Claim)
    (accepted : checkPublicInputClaims descriptor root refs relationLeaves claims = true) :
    relationLeaves = expectedLeaves root refs ∧
      (relationLeaves.map RecordStatementV2.Descriptor.path).Nodup ∧
      List.Forall₂ WellFormed relationLeaves claims ∧
      AliasConsistent relationLeaves claims := by
  have parts : checkPublicInputBinding descriptor root refs relationLeaves = true ∧
      admitClaims relationLeaves claims = true := by
    simpa [checkPublicInputClaims] using accepted
  have binding := checked_public_input_binding descriptor root member refs
    relationLeaves parts.1
  have claim := (admitClaims_iff relationLeaves claims).mp parts.2
  exact ⟨binding.1, binding.2.1, claim.1, claim.2⟩

/-- For any checked leaf occurrence, the statement checker's first-wire
projection returns that leaf's words, including when other paths alias its
wire. The occurrence itself comes from the checked ordered tree projection. -/
theorem checked_expected_wire_lookup {n : Nat}
    (descriptor : RecordDescriptorValidationV2.Descriptor)
    (root : InputRoot) (member : root ∈ descriptor.inputs)
    (refs : LeafPosition (erase (toRaw root.layout)) → Fin n)
    (relationLeaves : List (RecordStatementV2.Descriptor n))
    (claims : List Claim)
    (accepted : checkPublicInputClaims descriptor root refs relationLeaves claims = true)
    (pair : RecordStatementV2.Descriptor n × Claim)
    (present : pair ∈ List.zip (expectedLeaves root refs) claims) :
    firstWireWords (expectedLeaves root refs) claims pair.1.wire =
      some pair.2.words := by
  have checked := checked_public_input_claims descriptor root member refs
    relationLeaves claims accepted
  have parts : checkPublicInputBinding descriptor root refs relationLeaves = true ∧
      admitClaims relationLeaves claims = true := by
    simpa [checkPublicInputClaims] using accepted
  rw [checked.1] at parts
  exact firstWireWords_admitted (expectedLeaves root refs) claims parts.2
    pair present

/-- The one-field public `Pair` input has path `x.value` on wire zero. -/
def pairInput : InputRoot :=
  { name := "x", visibility := .pub, layout := pairType 1 }

def pairRefs : LeafPosition (erase (toRaw pairInput.layout)) → Fin 1 :=
  fun _ => 0

def pairLeaves : List (RecordStatementV2.Descriptor 1) :=
  [{ path := [.root "x", .field "value"], kind := .m31,
     width := 1, wire := 0 }]

def pairClaims : List Claim :=
  [{ path := [.root "x", .field "value"], words := [7] }]

theorem pair_binding_accepted :
    checkPublicInputClaims exampleDescriptor pairInput pairRefs
      pairLeaves pairClaims = true := by decide

theorem pair_input_member : pairInput ∈ exampleDescriptor.inputs := by
  simp [pairInput, exampleDescriptor]

theorem pair_statement_projection :
    admitStatement pairLeaves pairClaims [0] [] =
      some [7, 0, 0, 0, 0, 0, 0, 0] := by decide

def wrongWireLeaves : List (RecordStatementV2.Descriptor 2) :=
  [{ path := [.root "x", .field "value"], kind := .m31,
     width := 1, wire := 1 }]

def pairRefsTwo : LeafPosition (erase (toRaw pairInput.layout)) → Fin 2 :=
  fun _ => 0

theorem changed_wire_rejected :
    checkPublicInputBinding exampleDescriptor pairInput pairRefsTwo
      wrongWireLeaves = false := by decide

def wrongPathClaims : List Claim :=
  [{ path := [.root "x", .field "other"], words := [7] }]

theorem changed_path_rejected :
    checkPublicInputClaims exampleDescriptor pairInput pairRefs
      pairLeaves wrongPathClaims = false := by decide

end S31.Functional.RecordDescriptorWireRefinementV2
