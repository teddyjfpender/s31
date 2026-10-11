import S31.Gadgets.Functional.RecordBoundary

/-!
A narrow model of the public record ABI v2 boundary. A leaf is a checked block
of M31 words, so its declared width cannot silently differ from its payload.
The already-proved product-tree decoder is reused at the leaf level. Source
field names, canonical JSON, SHA-256, and the production Zig verifier are not
derived here. The n-ary nominal tree below derives path uniqueness from
distinct sibling field names and tuple indices; relating that tree to the
production Zig validator remains a separate refinement obligation.
-/

namespace S31.Functional.RecordAbiV2

open RecordBoundary

/-- One first-order M31 leaf with its checked width. The native v2 subset
currently admits M31 leaves only. -/
structure WordBlock (α : Type) where
  width : Nat
  words : List α
  exactWidth : words.length = width

def block {α : Type} (words : List α) : WordBlock α :=
  ⟨words.length, words, rfl⟩

/-- The ordered widths in the validated type tree. -/
def matchesWidths {α : Type} (layout : Layout)
    (value : Value (WordBlock α) layout) (expected : List Nat) : Prop :=
  (flatten layout value).map WordBlock.width = expected

/-- Decode whole leaf blocks, rejecting a different declared width sequence.
The caller must separately check the canonical tagged paths and word ranges. -/
def decodeChecked {α : Type} (layout : Layout) (expected : List Nat)
    (leaves : List (WordBlock α)) : Option (Value (WordBlock α) layout × List (WordBlock α)) := do
  let (value, rest) ← reconstruct layout leaves
  if matchesWidths layout value expected then some (value, rest) else none

/-- Checked flattening followed by decoding consumes exactly the record's
leaves and leaves any following leaves untouched. -/
theorem decodeChecked_flatten_append {α : Type} (layout : Layout)
    (value : Value (WordBlock α) layout) (expected : List Nat)
    (tail : List (WordBlock α)) (valid : matchesWidths layout value expected) :
    decodeChecked layout expected (flatten layout value ++ tail) =
      some (value, tail) := by
  simp [decodeChecked, reconstruct_flatten_append, valid]

/-- Exact checked leaf vectors recover their typed product and width order. -/
theorem decodeChecked_flatten {α : Type} (layout : Layout)
    (value : Value (WordBlock α) layout) (expected : List Nat)
    (valid : matchesWidths layout value expected) :
    decodeChecked layout expected (flatten layout value) = some (value, []) := by
  simpa using decodeChecked_flatten_append layout value expected [] valid

/-- Flatten the checked leaves into the exact public M31 word vector. -/
def concatBlocks {α : Type} (leaves : List (WordBlock α)) : List α :=
  leaves.flatMap WordBlock.words

/-- The flattened word count is the sum of checked leaf widths. -/
theorem concatBlocks_length {α : Type} (leaves : List (WordBlock α)) :
    (concatBlocks leaves).length = (leaves.map WordBlock.width).sum := by
  induction leaves with
  | nil => rfl
  | cons head tail ih =>
      simp [concatBlocks, head.exactWidth, ih]

/-- Typed public roots plus distinct result references use the same first
order word order as the native projection over tagged relation inputs. -/
def typedPublicWords {α : Type} {n : Nat} (roots : List (InputRoot (WordBlock α)))
    (wires : Fin n → WordBlock α) (resultRefs : List (Fin n)) : List α :=
  concatBlocks (boundaryProofWords roots wires resultRefs)

def nativeProjectedWords {α : Type} {n : Nat}
    (roots : List (InputRoot (WordBlock α))) (wires : Fin n → WordBlock α)
    (resultRefs : List (Fin n)) : List α :=
  concatBlocks (visibleWords (taggedInputLeaves roots)) ++
    concatBlocks (distinctProofWords wires resultRefs)

theorem typedPublicWords_eq_nativeProjection {α : Type} {n : Nat}
    (roots : List (InputRoot (WordBlock α))) (wires : Fin n → WordBlock α)
    (resultRefs : List (Fin n)) :
    typedPublicWords roots wires resultRefs =
      nativeProjectedWords roots wires resultRefs := by
  simp [typedPublicWords, nativeProjectedWords, boundaryProofWords,
    concatBlocks, publicInputWords_eq_visible_flatten]

/-- The native eight-word gate can be checked from descriptor widths without
counting repeated output aliases twice. -/
def withinEightWords {α : Type} {n : Nat}
    (roots : List (InputRoot (WordBlock α))) (wires : Fin n → WordBlock α)
    (resultRefs : List (Fin n)) : Prop :=
  (typedPublicWords roots wires resultRefs).length ≤ 8

theorem withinEightWords_iff_width_sum {α : Type} {n : Nat}
    (roots : List (InputRoot (WordBlock α))) (wires : Fin n → WordBlock α)
    (resultRefs : List (Fin n)) :
    withinEightWords roots wires resultRefs ↔
      ((boundaryProofWords roots wires resultRefs).map WordBlock.width).sum ≤ 8 := by
  simp [withinEightWords, typedPublicWords, concatBlocks_length]

/-- This is the semantic obligation discharged by the production type-tree
walk: two leaves of one root cannot receive the same tagged source path. -/
inductive Segment where
  | root (name : String)
  | field (name : String)
  | tuple (index : Nat)
deriving Repr, DecidableEq

structure ValidatedPaths (layout : Layout) where
  path : Path layout → List Segment
  injective : Function.Injective path

theorem validated_path_collision_impossible {layout : Layout}
    (paths : ValidatedPaths layout) (first second : Path layout)
    (same : paths.path first = paths.path second) : first = second :=
  paths.injective same

/-- The smallest nominal record fixture: two distinct named fields. -/
def twoFields : Layout := .pair .leaf .leaf

def twoFieldPath (root first second : String) : Path twoFields → List Segment
  | .left .here => [.root root, .field first]
  | .right .here => [.root root, .field second]

theorem twoFieldPath_injective (root first second : String)
    (distinct : first ≠ second) : Function.Injective (twoFieldPath root first second) := by
  intro a b same
  cases a with
  | left a =>
      cases a
      cases b with
      | left b => cases b; rfl
      | right b =>
          cases b
          have namesEqual : first = second := by
            simpa [twoFieldPath] using same
          exact False.elim (distinct namesEqual)
  | right a =>
      cases a
      cases b with
      | left b =>
          cases b
          have namesEqual : second = first := by
            simpa [twoFieldPath] using same
          exact False.elim (distinct namesEqual.symm)
      | right b => cases b; rfl

def twoFieldValidated (root first second : String) (distinct : first ≠ second) :
    ValidatedPaths twoFields :=
  ⟨twoFieldPath root first second, twoFieldPath_injective root first second distinct⟩

/-!
The binary Layout above describes first-order flattening. Native ABI paths
instead follow n-ary record and tuple nodes: a record edge contributes a
field-name segment, and a tuple edge contributes its index. This second tree
models that path computation without imposing an artificial binary edge on a
three-or-more-field source record. Local sibling uniqueness is a separate
validation predicate; neither the tree nor a path structure stores global
path injectivity.
-/

/-- A finite n-ary ABI type tree. A leaf is a first-order M31 word block;
each node supplies one segment and one subtree per child. This raw tree
stores no injectivity evidence. -/
inductive NominalTree where
  | leaf
  | node (arity : Nat) (tag : Fin arity → Segment)
      (child : Fin arity → NominalTree)

/-- The local validation obligation for every node. It is stated separately
from the tree and does not assume that complete paths are injective. -/
def WellTagged : NominalTree → Prop
  | .leaf => True
  | .node arity tag child =>
      Function.Injective tag ∧ ∀ index : Fin arity, WellTagged (child index)

/-- A leaf position selects one child at each node. -/
def LeafPosition : NominalTree → Type
  | .leaf => Unit
  | .node arity _ child => Σ index : Fin arity, LeafPosition (child index)

/-- The exact tagged suffix generated by walking one leaf position. The
root-name segment is added separately by rootedNominalPath. -/
def nominalPath : (tree : NominalTree) → LeafPosition tree → List Segment
  | .leaf, _ => []
  | .node _ tag child, ⟨index, tail⟩ =>
      tag index :: nominalPath (child index) tail

/-- Distinct leaf positions in any finite, arbitrarily nested n-ary tree
cannot produce the same tagged suffix when every node has distinct sibling
segments. No global path-injectivity premise is used. -/
theorem nominalPath_injective (tree : NominalTree) :
    WellTagged tree → Function.Injective (nominalPath tree) := by
  induction tree with
  | leaf =>
      intro _ first second _
      cases first
      cases second
      rfl
  | node arity tag child ih =>
      intro valid first second same
      obtain ⟨siblingTagsDistinct, validChild⟩ := valid
      rcases first with ⟨firstIndex, firstTail⟩
      rcases second with ⟨secondIndex, secondTail⟩
      change tag firstIndex :: nominalPath (child firstIndex) firstTail =
        tag secondIndex :: nominalPath (child secondIndex) secondTail at same
      have sameIndex : firstIndex = secondIndex :=
        siblingTagsDistinct ((List.cons.inj same).1)
      subst secondIndex
      have sameTail : firstTail = secondTail :=
        ih firstIndex (validChild firstIndex) ((List.cons.inj same).2)
      subst secondTail
      rfl

/-- A record node uses the source field name as its tagged edge. Local
duplicate-name validation is supplied to namedRecord_wellTagged. -/
def namedRecord (arity : Nat) (fieldName : Fin arity → String)
    (child : Fin arity → NominalTree) : NominalTree :=
  .node arity (fun index => .field (fieldName index)) child

theorem namedRecord_wellTagged (arity : Nat) (fieldName : Fin arity → String)
    (distinctNames : Function.Injective fieldName)
    (child : Fin arity → NominalTree)
    (validChild : ∀ index, WellTagged (child index)) :
    WellTagged (namedRecord arity fieldName child) := by
  refine ⟨?_, validChild⟩
  intro first second same
  apply distinctNames
  exact congrArg (fun segment => match segment with
    | .field name => name
    | _ => "") same

/-- A tuple node uses its canonical zero-based child index. -/
def indexedTuple (arity : Nat) (child : Fin arity → NominalTree) : NominalTree :=
  .node arity (fun index => .tuple index.val) child

theorem indexedTuple_wellTagged (arity : Nat)
    (child : Fin arity → NominalTree)
    (validChild : ∀ index, WellTagged (child index)) :
    WellTagged (indexedTuple arity child) := by
  refine ⟨?_, validChild⟩
  intro first second same
  apply Fin.ext
  exact congrArg (fun segment => match segment with
    | .tuple index => index
    | _ => 0) same

def rootedNominalPath (root : String) (tree : NominalTree)
    (position : LeafPosition tree) : List Segment :=
  .root root :: nominalPath tree position

/-- Unique local field names, tuple indices, and a fixed root imply unique
complete paths through arbitrarily nested records and tuples. -/
theorem rootedNominalPath_injective (root : String) (tree : NominalTree)
    (valid : WellTagged tree) :
    Function.Injective (rootedNominalPath root tree) := by
  intro first second same
  exact nominalPath_injective tree valid ((List.cons.inj same).2)

/-- Distinct root names separate paths even when their type trees and leaf
suffixes happen to be identical. This models the ABI's root-name check. -/
theorem rootedNominalPath_distinct_roots (firstRoot secondRoot : String)
    (different : firstRoot ≠ secondRoot) (firstTree secondTree : NominalTree)
    (first : LeafPosition firstTree) (second : LeafPosition secondTree) :
    rootedNominalPath firstRoot firstTree first ≠
      rootedNominalPath secondRoot secondTree second := by
  intro same
  have sameTag : Segment.root firstRoot = Segment.root secondRoot :=
    (List.cons.inj same).1
  apply different
  exact congrArg (fun segment => match segment with
    | .root name => name
    | _ => "") sameTag

/-- An explicit record containing a three-element tuple and a scalar. The
two fields have distinct names, and the tuple has canonical child indices. -/
def nestedFixture : NominalTree :=
  namedRecord 2 (fun index => if index.val = 0 then "items" else "salt")
    (fun index => if index.val = 0 then indexedTuple 3 (fun _ => .leaf) else .leaf)

theorem nestedFixture_wellTagged : WellTagged nestedFixture := by decide

theorem nested_fixture_tuple_paths_distinct :
    rootedNominalPath "request" nestedFixture ⟨0, ⟨1, ()⟩⟩ ≠
      rootedNominalPath "request" nestedFixture ⟨0, ⟨2, ()⟩⟩ := by decide

theorem nested_fixture_field_paths_distinct :
    rootedNominalPath "request" nestedFixture ⟨0, ⟨1, ()⟩⟩ ≠
      rootedNominalPath "request" nestedFixture ⟨1, ()⟩ := by decide

/-- Worked public/private record fixture. The two public input leaves have
widths 2 and 1. Two output paths alias one two-word wire. The private leaf is
absent; the proof word vector is precisely `[3, 4, 5, 13, 14]`. -/
def fixtureRoots : List (InputRoot (WordBlock Nat)) :=
  [⟨twoFields, .visible, (block [3, 4], block [5])⟩,
   ⟨.leaf, .secret, block [7]⟩]

def fixtureWires : Fin 1 → WordBlock Nat := fun _ => block [13, 14]

theorem fixture_public_words :
    typedPublicWords fixtureRoots fixtureWires [0, 0] = [3, 4, 5, 13, 14] := by
  decide

theorem fixture_fits_eight_words :
    withinEightWords fixtureRoots fixtureWires [0, 0] := by
  simp [withinEightWords, fixture_public_words]

theorem fixture_native_words :
    nativeProjectedWords fixtureRoots fixtureWires [0, 0] = [3, 4, 5, 13, 14] := by
  rw [← typedPublicWords_eq_nativeProjection]
  exact fixture_public_words

/-- A changed leaf width is rejected even if the number of leaves matches. -/
theorem fixture_wrong_width_rejected :
    decodeChecked twoFields [2, 2] [block [3, 4], block [5]] = none := by
  rfl

/-- Two distinct source names produce distinct paths for the worked record. -/
theorem fixture_paths_distinct :
    twoFieldPath "request" "left" "right" (.left .here) ≠
      twoFieldPath "request" "left" "right" (.right .here) := by
  decide

end S31.Functional.RecordAbiV2
