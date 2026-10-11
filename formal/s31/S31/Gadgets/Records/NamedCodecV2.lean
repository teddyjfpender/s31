import S31.Gadgets.Functional.RecordLayoutValidationV2
import S31.Gadgets.Functional.RecordStatementV2
import S31.Gadgets.Functional.RecordDescriptorValidationV2

/-!
An integrated, bounded leaf codec for one already parsed public record ABI v2
root. Native `record_abi.zig` visits record fields in declaration order, tuple
members in index order, then checks each path, leaf width, and numeric range.
The earlier formal modules establish these properties separately. This module
joins them for a root whose payloads are supplied at every typed leaf
position: encoding produces the exact named claims, and checked decoding
recovers the exact ordered blocks and flat word stream.

The `Fin 1` reference in the local statement descriptors is a dummy: this
module checks paths and payloads, not relation-wire aliasing. Source parsing,
nominal consistency across roots, descriptor-to-wire correspondence, JSON
canonicalization, SHA-256 and native proof admission remain separate.
-/

namespace S31.Records.NamedCodecV2

open S31.Functional.RecordAbiV2
open S31.Functional.RecordLayoutValidationV2
open S31.Functional.RecordWordBoundaryV2
open S31.Functional.RecordStatementV2

def positions (layout : RawLayout) : List (LeafPosition (erase layout)) :=
  orderedPositions (erase layout)

def paths (root : String) (layout : RawLayout) : List (List Segment) :=
  (positions layout).map (rootedNominalPath root (erase layout))

def widths (layout : RawLayout) : List Nat :=
  (positions layout).map (leafWidthAt layout)

def descriptors (root : String) (layout : RawLayout) :
    List (S31.Functional.RecordStatementV2.Descriptor 1) :=
  (positions layout).map fun position =>
    { path := rootedNominalPath root (erase layout) position
      kind := leafKindAt layout position
      width := leafWidthAt layout position
      wire := 0 }

def encode (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat) : List Claim :=
  (positions layout).map fun position =>
    { path := rootedNominalPath root (erase layout) position
      words := (values position).words }

def flatWords (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat) : List Nat :=
  (encode root layout values).flatMap Claim.words

/-- Check the ordered path/width/kind-range claims, then split the exact flat
M31 word stream at its validated leaf boundaries. -/
def decode (root : String) (layout : RawLayout) (claims : List Claim) :
    Option (List (List Nat)) :=
  if checkRoot layout && checkOrdered (descriptors root layout) claims then
    admitPublicWords (widths layout) (claims.flatMap Claim.words)
  else none

/-- The declared width at every typed position equals its supplied block. -/
def WidthsMatch (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat) : Prop :=
  ∀ position, (values position).width = leafWidthAt layout position

/-- The kind-specific native range rule: M31 words are canonical, bit words
are zero or one, and u16 words are below 65536. -/
def KindsInRange (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat) : Prop :=
  ∀ position, ∀ word ∈ (values position).words,
    word < publicLeafBound (leafKindAt layout position)

theorem encode_paths (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat) :
    (encode root layout values).map Claim.path = paths root layout := by
  simp [encode, paths, List.map_map]

theorem encode_paths_nodup (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat)
    (accepted : checkRoot layout = true) :
    ((encode root layout values).map Claim.path).Nodup := by
  rw [encode_paths]
  exact (orderedPositions_nodup (erase layout)).map
    (rootedNominalPath_injective root (erase layout)
      (checkRoot_wellTagged layout accepted))

theorem encode_ordered (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat)
    (matching : WidthsMatch layout values)
    (range : KindsInRange layout values) :
    checkOrdered (descriptors root layout) (encode root layout values) = true := by
  apply (checkOrdered_iff _ _).2
  unfold descriptors encode
  have walk (ps : List (LeafPosition (erase layout))) :
      List.Forall₂ WellFormed
        (ps.map fun position =>
          { path := rootedNominalPath root (erase layout) position
            kind := leafKindAt layout position
            width := leafWidthAt layout position
            wire := (0 : Fin 1) })
        (ps.map fun position =>
          { path := rootedNominalPath root (erase layout) position
            words := (values position).words }) := by
    induction ps with
    | nil => exact .nil
    | cons position rest ih =>
        apply List.Forall₂.cons
        · exact ⟨rfl, by simpa [matching position] using (values position).exactWidth,
            range position⟩
        · exact ih
  exact walk (positions layout)

theorem flatWords_eq_orderedWords (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat) :
    flatWords root layout values =
      orderedWords root (erase layout) values := by
  simp [flatWords, encode, positions, orderedWords, orderedRootLeaves,
    orderedNominalLeaves, concatBlocks, List.flatMap_map, List.map_map]

theorem widths_eq_orderedWidths (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat)
    (matching : WidthsMatch layout values) :
    widths layout = orderedWidths root (erase layout) values := by
  simp only [widths, positions, orderedWidths, orderedRootLeaves,
    orderedNominalLeaves, List.map_map, Function.comp_def]
  exact List.map_congr_left (fun position _ => (matching position).symm)

/-- Bit and u16 bounds are stronger than the canonical M31 bound. Thus the
native per-kind statement range check suffices for the flat word decoder. -/
theorem kindsInRange_canonical (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat)
    (range : KindsInRange layout values) :
    CanonicalM31Words (flatWords root layout values) := by
  intro word present
  have flat : flatWords root layout values =
      (positions layout).flatMap (fun position => (values position).words) := by
    simp [flatWords, encode, List.flatMap_map]
  rw [flat] at present
  obtain ⟨position, _, inBlock⟩ := List.mem_flatMap.mp present
  have bounded := range position word inBlock
  cases hKind : leafKindAt layout position with
  | m31 => simpa [hKind, publicLeafBound] using bounded
  | bit =>
      simp [hKind, publicLeafBound] at bounded
      omega
  | u16 =>
      simp [hKind, publicLeafBound] at bounded
      omega

/-- A successful decode preserves every claimed word, all declared leaf
boundaries, and the native ordered path/width/kind-range checks. -/
theorem decode_sound (root : String) (layout : RawLayout)
    (claims : List Claim) (blocks : List (List Nat))
    (accepted : decode root layout claims = some blocks) :
    checkRoot layout = true ∧
      checkOrdered (descriptors root layout) claims = true ∧
      ValidPublicWidths (widths layout) ∧
      blocks.map List.length = widths layout ∧
      blocks.flatMap id = claims.flatMap Claim.words ∧
      ∀ block ∈ blocks, CanonicalM31Words block := by
  unfold decode at accepted
  cases h : checkRoot layout && checkOrdered (descriptors root layout) claims with
  | false => simp [h] at accepted
  | true =>
      have checks : checkRoot layout = true ∧
          checkOrdered (descriptors root layout) claims = true := by
        simpa using h
      simp [h] at accepted
      obtain ⟨valid, lengths, exactWords, ranges⟩ :=
        admitPublicWords_sound (widths layout)
          (claims.flatMap Claim.words) blocks accepted
      exact ⟨checks.1, checks.2, valid, lengths, exactWords, ranges⟩

theorem decode_encode (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat)
    (accepted : checkRoot layout = true)
    (matching : WidthsMatch layout values)
    (range : KindsInRange layout values) :
    decode root layout (encode root layout values) =
      some ((positions layout).map fun position => (values position).words) := by
  have ordered := encode_ordered root layout values matching range
  have admittedWidth : ValidPublicWidths (widths layout) := by
    rw [widths_eq_orderedWidths root layout values matching]
    exact checked_ordered_widths root layout values accepted matching
  have hWords : flatWords root layout values =
      concatBlocks ((positions layout).map values) := by
    simp [flatWords, encode, concatBlocks, List.flatMap_map]
  have hWidths : widths layout = ((positions layout).map values).map WordBlock.width := by
    simp only [widths, List.map_map]
    exact List.map_congr_left (fun position _ => (matching position).symm)
  have decoded := admitPublicWords_complete
    ((positions layout).map values)
    (by simpa [hWidths] using admittedWidth)
    (by simpa [hWords] using kindsInRange_canonical root layout values range)
  unfold decode
  simp only [accepted, ordered, Bool.true_and, ↓reduceIte]
  change admitPublicWords (widths layout) (flatWords root layout values) =
    some ((positions layout).map fun position => (values position).words)
  rw [hWidths, hWords]
  simpa [List.map_map] using decoded

/-- Private roots remain in the source descriptor and circuit inputs, but
contribute no public named claims. -/
def encodeInput (visibility :
    S31.Functional.RecordDescriptorValidationV2.Visibility)
    (root : String) (layout : RawLayout)
    (values : LeafPosition (erase layout) → WordBlock Nat) : List Claim :=
  match visibility with
  | .pub => encode root layout values
  | .priv => []

theorem private_input_claims_irrelevant (root : String) (layout : RawLayout)
    (first second : LeafPosition (erase layout) → WordBlock Nat) :
    encodeInput .priv root layout first = encodeInput .priv root layout second := rfl

theorem public_private_public_claim_order
    (firstRoot secretRoot lastRoot : String)
    (firstLayout secretLayout lastLayout : RawLayout)
    (first : LeafPosition (erase firstLayout) → WordBlock Nat)
    (secret : LeafPosition (erase secretLayout) → WordBlock Nat)
    (last : LeafPosition (erase lastLayout) → WordBlock Nat) :
    encodeInput .pub firstRoot firstLayout first ++
      encodeInput .priv secretRoot secretLayout secret ++
      encodeInput .pub lastRoot lastLayout last =
      encode firstRoot firstLayout first ++ encode lastRoot lastLayout last := by
  simp [encodeInput]

/-- An explicit two-field nominal record; its declaration fixes the path
order even if a source constructor wrote fields in another order. -/
def pairLayout : RawLayout :=
  .record 2 (fun i => if i.val = 0 then "left" else "right")
    (fun _ => .leaf .m31 1)

theorem pair_layout_accepted : checkRoot pairLayout = true := by decide

theorem pair_declaration_order :
    paths "request" pairLayout =
      [[.root "request", .field "left"],
       [.root "request", .field "right"]] := by decide

theorem pair_swapped_claims_rejected :
    decode "request" pairLayout
      [{ path := [.root "request", .field "right"], words := [2] },
       { path := [.root "request", .field "left"], words := [1] }] = none := by
  decide

def bitLayout : RawLayout :=
  .record 1 (fun _ => "enabled") (fun _ => .leaf .bit 1)

theorem bit_zero_one_accepted :
    decode "request" bitLayout
      [{ path := [.root "request", .field "enabled"], words := [1] }] =
      some [[1]] := by decide

theorem bit_two_rejected :
    decode "request" bitLayout
      [{ path := [.root "request", .field "enabled"], words := [2] }] =
      none := by decide

def duplicateFields : RawLayout :=
  .record 2 (fun _ => "same") (fun _ => .leaf .m31 1)

theorem duplicate_fields_rejected : checkRoot duplicateFields = false := by decide

end S31.Records.NamedCodecV2
