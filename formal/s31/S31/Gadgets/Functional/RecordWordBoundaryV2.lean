import S31.Gadgets.Functional.RecordAbiV2

/-!
The public record ABI v2 word boundary after a validated nominal type tree.
The production validator supplies declaration-order leaves and their widths;
this model starts with those checked leaves. It proves that parsing the raw
public M31 vector by those widths has exactly one interpretation, including
arbitrarily nested record/tuple leaves and repeated result-wire references.

This is a semantic theorem, not a refinement of Python/Zig JSON parsing,
canonical byte serialization, SHA-256, or the native verifier. Those links
remain independent executable/proof obligations.
-/

namespace S31.Functional.RecordWordBoundaryV2

open RecordBoundary RecordAbiV2

/-- Parse exactly `width` words and return the unconsumed suffix. -/
def takeExactly {α : Type} : Nat → List α → Option (List α × List α)
  | 0, words => some ([], words)
  | _ + 1, [] => none
  | width + 1, word :: rest => do
      let (taken, tail) ← takeExactly width rest
      some (word :: taken, tail)

theorem takeExactly_append {α : Type} (front tail : List α) :
    takeExactly front.length (front ++ tail) = some (front, tail) := by
  induction front with
  | nil => rfl
  | cons word rest ih => simp [takeExactly, ih]

/-- Successful parsing cannot drop, duplicate, or invent a word. -/
theorem takeExactly_sound {α : Type} (width : Nat) (words front tail : List α)
    (accepted : takeExactly width words = some (front, tail)) :
    front.length = width ∧ words = front ++ tail := by
  induction width generalizing words front tail with
  | zero =>
      simp [takeExactly] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      simp
  | succ width ih =>
      cases words with
      | nil => simp [takeExactly] at accepted
      | cons word rest =>
          cases hTake : takeExactly width rest with
          | none => simp [takeExactly, hTake] at accepted
          | some pair =>
              rcases pair with ⟨result, tailWords⟩
              simp [takeExactly, hTake] at accepted
              rcases accepted with ⟨rfl, rfl⟩
              obtain ⟨length, original⟩ := ih rest result tailWords hTake
              simp [length, original]

/-- Decode one block for each declared leaf width, in declaration order. -/
def decodeWidths {α : Type} : List Nat → List α →
    Option (List (List α) × List α)
  | [], words => some ([], words)
  | width :: widths, words => do
      let (blockWords, afterBlock) ← takeExactly width words
      let (blocks, tail) ← decodeWidths widths afterBlock
      some (blockWords :: blocks, tail)

/-- The decoder accepts every checked leaf sequence and leaves an arbitrary
following suffix untouched. -/
theorem decodeWidths_concat_append {α : Type} (leaves : List (WordBlock α))
    (tail : List α) :
    decodeWidths (leaves.map WordBlock.width) (concatBlocks leaves ++ tail) =
      some (leaves.map WordBlock.words, tail) := by
  induction leaves with
  | nil => rfl
  | cons head rest ih =>
      have parsedHead := takeExactly_append head.words (concatBlocks rest ++ tail)
      rw [head.exactWidth] at parsedHead
      simp only [List.map_cons, concatBlocks, List.flatMap_cons,
        List.append_assoc, decodeWidths] at ih parsedHead ⊢
      simp [parsedHead, ih]

/-- A successful width decoder preserves the entire input and each declared
width, even on adversarial words. -/
theorem decodeWidths_sound {α : Type} (widths : List Nat)
    (words : List α) (blocks : List (List α)) (tail : List α)
    (accepted : decodeWidths widths words = some (blocks, tail)) :
    blocks.map List.length = widths ∧ words = blocks.flatMap id ++ tail := by
  induction widths generalizing words blocks tail with
  | nil =>
      simp [decodeWidths] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      simp
  | cons width widths ih =>
      cases hHead : takeExactly width words with
      | none => simp [decodeWidths, hHead] at accepted
      | some pair =>
          rcases pair with ⟨head, afterHead⟩
          cases hRest : decodeWidths widths afterHead with
          | none => simp [decodeWidths, hHead, hRest] at accepted
          | some pair =>
              rcases pair with ⟨rest, afterRest⟩
              simp [decodeWidths, hHead, hRest] at accepted
              rcases accepted with ⟨rfl, rfl⟩
              obtain ⟨headLength, headWords⟩ :=
                takeExactly_sound width words head afterHead hHead
              obtain ⟨restLengths, restWords⟩ :=
                ih afterHead rest afterRest hRest
              simp [headLength, restLengths, headWords, restWords]

/-- With a fixed width sequence, identical public words cannot conceal a
different leaf grouping. This compares payloads, independent of proof fields
carried by `WordBlock`. -/
theorem width_boundaries_unique {α : Type} (first second : List (WordBlock α))
    (sameWidths : first.map WordBlock.width = second.map WordBlock.width)
    (sameWords : concatBlocks first = concatBlocks second) :
    first.map WordBlock.words = second.map WordBlock.words := by
  have firstParsed := decodeWidths_concat_append first []
  have secondParsed := decodeWidths_concat_append second []
  simp only [List.append_nil] at firstParsed secondParsed
  rw [sameWidths, sameWords, secondParsed] at firstParsed
  exact congrArg Prod.fst (Option.some.inj firstParsed).symm

/-- The raw field representation is canonical only for integers in M31's
standard range. The production v2 ABI applies this check to public words. -/
def CanonicalM31Words (words : List Nat) : Prop :=
  ∀ word ∈ words, word < 2147483647

/-- The production v2 type-tree validator permits one through eight words
per scalar leaf. Its separate tree-depth and total-leaf limits are outside
this word decoder. -/
def ValidPublicWidths (widths : List Nat) : Prop :=
  ∀ width ∈ widths, 1 ≤ width ∧ width ≤ 8

def validWidthsCheck : List Nat → Bool
  | [] => true
  | width :: rest =>
      decide (1 ≤ width) && decide (width ≤ 8) && validWidthsCheck rest

theorem validWidthsCheck_iff (widths : List Nat) :
    validWidthsCheck widths = true ↔ ValidPublicWidths widths := by
  induction widths with
  | nil => simp [validWidthsCheck, ValidPublicWidths]
  | cons width rest ih => simp [validWidthsCheck, ValidPublicWidths, ih]

def canonicalCheck : List Nat → Bool
  | [] => true
  | word :: rest => decide (word < 2147483647) && canonicalCheck rest

theorem canonicalCheck_iff (words : List Nat) :
    canonicalCheck words = true ↔ CanonicalM31Words words := by
  induction words with
  | nil => simp [canonicalCheck, CanonicalM31Words]
  | cons word rest ih => simp [canonicalCheck, CanonicalM31Words, ih]

/-- An exact public-word decode simultaneously fixes leaf boundaries and
retains the canonical range predicate on every decoded word. -/
theorem decoded_canonical_blocks (widths : List Nat) (words : List Nat)
    (blocks : List (List Nat))
    (accepted : decodeWidths widths words = some (blocks, []))
    (canonical : CanonicalM31Words words) :
    blocks.map List.length = widths ∧
      ∀ block ∈ blocks, CanonicalM31Words block := by
  obtain ⟨lengths, original⟩ :=
    decodeWidths_sound widths words blocks [] accepted
  refine ⟨lengths, ?_⟩
  intro block present word inBlock
  apply canonical word
  rw [original]
  simpa using (List.mem_flatMap.mpr ⟨block, present, by simpa using inBlock⟩ :
    word ∈ blocks.flatMap id)

/-- The executable public-word admission step: reject an invalid leaf width,
an out-of-range M31 word, an incomplete last leaf, or extra words. -/
def admitPublicWords (widths : List Nat) (words : List Nat) :
    Option (List (List Nat)) :=
  if validWidthsCheck widths && canonicalCheck words then
    match decodeWidths widths words with
    | some (blocks, []) => some blocks
    | _ => none
  else none

theorem admitPublicWords_sound (widths words : List Nat)
    (blocks : List (List Nat))
    (accepted : admitPublicWords widths words = some blocks) :
    ValidPublicWidths widths ∧
      blocks.map List.length = widths ∧
      blocks.flatMap id = words ∧
      ∀ block ∈ blocks, CanonicalM31Words block := by
  unfold admitPublicWords at accepted
  cases hBoth : validWidthsCheck widths && canonicalCheck words with
  | true =>
    simp [hBoth] at accepted
    have hWidths : validWidthsCheck widths = true := by
      have h := hBoth
      simp at h
      exact h.1
    have hCanonical : canonicalCheck words = true := by
      have h := hBoth
      simp at h
      exact h.2
    cases hDecode : decodeWidths widths words with
    | none => simp [hDecode] at accepted
    | some pair =>
        rcases pair with ⟨decoded, tail⟩
        cases tail with
        | nil =>
            simp [hDecode] at accepted
            subst blocks
            obtain ⟨lengths, original⟩ :=
              decodeWidths_sound widths words decoded [] hDecode
            obtain ⟨_, ranges⟩ :=
              decoded_canonical_blocks widths words decoded hDecode
                ((canonicalCheck_iff words).mp hCanonical)
            exact ⟨(validWidthsCheck_iff widths).mp hWidths,
              lengths, by simpa using original.symm, ranges⟩
        | cons word rest => simp [hDecode] at accepted
  | false => simp [hBoth] at accepted

theorem admitPublicWords_complete (leaves : List (WordBlock Nat))
    (valid : ValidPublicWidths (leaves.map WordBlock.width))
    (canonical : CanonicalM31Words (concatBlocks leaves)) :
    admitPublicWords (leaves.map WordBlock.width) (concatBlocks leaves) =
      some (leaves.map WordBlock.words) := by
  have decoded := decodeWidths_concat_append leaves ([] : List Nat)
  simp only [List.append_nil] at decoded
  have checkedWidths := (validWidthsCheck_iff (leaves.map WordBlock.width)).mpr valid
  have checked := (canonicalCheck_iff (concatBlocks leaves)).mpr canonical
  simp [admitPublicWords, checkedWidths, checked, decoded]

/-- Widths emitted by the ordered nominal walk. -/
def orderedWidths {α : Type} (root : String) (tree : NominalTree)
    (values : LeafPosition tree → WordBlock α) : List Nat :=
  ((orderedRootLeaves root tree values).map Prod.snd).map WordBlock.width

/-- Raw public words emitted by the same ordered nominal walk. -/
def orderedWords {α : Type} (root : String) (tree : NominalTree)
    (values : LeafPosition tree → WordBlock α) : List α :=
  concatBlocks ((orderedRootLeaves root tree values).map Prod.snd)

/-- For any nested nominal tree, the descriptor's ordered widths decode its
exact declaration-order leaves. The `WellTagged` path condition is orthogonal
and combined with this theorem below. -/
theorem ordered_words_decode {α : Type} (root : String)
    (tree : NominalTree) (values : LeafPosition tree → WordBlock α) :
    decodeWidths (orderedWidths root tree values)
      (orderedWords root tree values) =
      some (((orderedRootLeaves root tree values).map Prod.snd).map
        WordBlock.words, []) := by
  simpa [orderedWidths, orderedWords] using
    decodeWidths_concat_append
      ((orderedRootLeaves root tree values).map Prod.snd) []

/-- Local sibling-name validation gives unique full paths; the width parser
recovers precisely the values in those paths' depth-first order. -/
theorem nested_paths_and_words_sound {α : Type} (root : String)
    (tree : NominalTree) (values : LeafPosition tree → WordBlock α)
    (valid : WellTagged tree) :
    ((orderedRootLeaves root tree values).map Prod.fst).Nodup ∧
      decodeWidths (orderedWidths root tree values)
        (orderedWords root tree values) =
        some (((orderedRootLeaves root tree values).map Prod.snd).map
          WordBlock.words, []) :=
  ⟨orderedRootLeaves_paths_nodup root tree values valid,
    ordered_words_decode root tree values⟩

/-- The complete semantic public input bridge: a validated nested nominal
tree has distinct rooted paths, and its width/range-checked flat public
statement decodes to exactly the corresponding ordered leaf payloads. -/
theorem validated_nested_public_boundary (root : String)
    (tree : NominalTree) (values : LeafPosition tree → WordBlock Nat)
    (validTags : WellTagged tree)
    (validWidths : ValidPublicWidths (orderedWidths root tree values))
    (canonical : CanonicalM31Words (orderedWords root tree values)) :
    ((orderedRootLeaves root tree values).map Prod.fst).Nodup ∧
      admitPublicWords (orderedWidths root tree values)
        (orderedWords root tree values) =
        some (((orderedRootLeaves root tree values).map Prod.snd).map
          WordBlock.words) := by
  refine ⟨orderedRootLeaves_paths_nodup root tree values validTags, ?_⟩
  exact admitPublicWords_complete
    ((orderedRootLeaves root tree values).map Prod.snd) validWidths canonical

/-- The native result statement follows first occurrence of each wire,
whereas every named leaf still has its own claim. -/
def orderedOutputRefs {n : Nat} (root : String) (tree : NominalTree)
    (refs : LeafPosition tree → Fin n) : List (Fin n) :=
  (orderedRootLeaves root tree refs).map Prod.snd

def orderedResultWords {α : Type} {n : Nat} (root : String)
    (tree : NominalTree) (refs : LeafPosition tree → Fin n)
    (wires : Fin n → WordBlock α) : List α :=
  concatBlocks (distinctProofWords wires (orderedOutputRefs root tree refs))

/-- The same first-reference deduplication used by the native result
statement determines the exact widths consumed from its raw public words. -/
theorem ordered_result_words_admit {n : Nat} (root : String)
    (tree : NominalTree) (refs : LeafPosition tree → Fin n)
    (wires : Fin n → WordBlock Nat)
    (valid : ValidPublicWidths
      ((distinctProofWords wires (orderedOutputRefs root tree refs)).map
        WordBlock.width))
    (canonical : CanonicalM31Words
      (orderedResultWords root tree refs wires)) :
    admitPublicWords
      ((distinctProofWords wires (orderedOutputRefs root tree refs)).map
        WordBlock.width)
      (orderedResultWords root tree refs wires) =
      some ((distinctProofWords wires (orderedOutputRefs root tree refs)).map
        WordBlock.words) := by
  exact admitPublicWords_complete
    (distinctProofWords wires (orderedOutputRefs root tree refs)) valid canonical

def orderedClaimsAccepted {α : Type} {n : Nat} (root : String)
    (tree : NominalTree) (refs : LeafPosition tree → Fin n)
    (wires : Fin n → α) (claims : List α) : Prop :=
  acceptsClaims wires (orderedOutputRefs root tree refs) claims

theorem ordered_claims_exact {α : Type} {n : Nat} (root : String)
    (tree : NominalTree) (refs : LeafPosition tree → Fin n)
    (wires : Fin n → α) (claims : List α) :
    orderedClaimsAccepted root tree refs wires claims ↔
      claims = (orderedPositions tree).map (fun position => wires (refs position)) := by
  simp [orderedClaimsAccepted, acceptsClaims, orderedOutputRefs,
    orderedRootLeaves, orderedNominalLeaves, projectAliases, List.map_map,
    Function.comp_def]

/-- Nested fixture: `items.0`, `items.1`, `items.2`, `salt`; the middle two
paths are distinct but both reference wire 1. -/
def nestedAliasRefs : LeafPosition nestedFixture → Fin 3
  | ⟨0, ⟨0, ()⟩⟩ => 0
  | ⟨0, ⟨1, ()⟩⟩ => 1
  | ⟨0, ⟨2, ()⟩⟩ => 1
  | ⟨1, ()⟩ => 2

def nestedAliasWires : Fin 3 → WordBlock Nat
  | 0 => block [3, 4]
  | 1 => block [5]
  | 2 => block [6]

theorem nested_alias_paths_unique :
    ((orderedRootLeaves "result" nestedFixture nestedAliasRefs).map
      Prod.fst).Nodup :=
  orderedRootLeaves_paths_nodup "result" nestedFixture nestedAliasRefs
    nestedFixture_wellTagged

theorem nested_alias_refs_order :
    orderedOutputRefs "result" nestedFixture nestedAliasRefs = [0, 1, 1, 2] := by
  decide

theorem nested_alias_statement_words :
    orderedResultWords "result" nestedFixture nestedAliasRefs
      nestedAliasWires = [3, 4, 5, 6] := by
  decide

theorem nested_alias_claims (claims : List (List Nat)) :
    orderedClaimsAccepted "result" nestedFixture nestedAliasRefs
      (fun index => (nestedAliasWires index).words) claims ↔
      claims = [[3, 4], [5], [5], [6]] := by
  rw [ordered_claims_exact]
  have concrete :
      (orderedPositions nestedFixture).map
        (fun position => (nestedAliasWires (nestedAliasRefs position)).words) =
        [[3, 4], [5], [5], [6]] := by decide
  rw [concrete]

theorem nested_alias_admitted_statement :
    admitPublicWords [2, 1, 1]
      (orderedResultWords "result" nestedFixture nestedAliasRefs
        nestedAliasWires) = some [[3, 4], [5], [6]] := by
  decide

theorem nested_alias_changed_second_claim_rejected :
    ¬ orderedClaimsAccepted "result" nestedFixture nestedAliasRefs
      (fun index => (nestedAliasWires index).words)
      [[3, 4], [5], [7], [6]] := by
  rw [nested_alias_claims]
  decide

theorem nested_alias_out_of_range_rejected :
    admitPublicWords [2, 1, 1] [3, 4, 2147483647, 6] = none := by
  decide

theorem nested_alias_zero_width_rejected :
    admitPublicWords [2, 0, 1] [3, 4, 5, 6] = none := by
  decide

theorem nested_alias_oversize_width_rejected :
    admitPublicWords [9] [3, 4, 5, 6] = none := by
  decide

theorem nested_alias_extra_word_rejected :
    admitPublicWords [2, 1, 1] [3, 4, 5, 6, 7] = none := by
  decide

theorem nested_alias_truncated_word_rejected :
    admitPublicWords [2, 1, 1] [3, 4, 5] = none := by
  decide

end S31.Functional.RecordWordBoundaryV2
