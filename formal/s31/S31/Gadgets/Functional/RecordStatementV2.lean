import S31.Gadgets.Functional.RecordWordBoundaryV2

/-!
The semantic core of the ABI v2 statement parser. This models the loop in
`record_abi.zig` that compares each claim against an already validated leaf
descriptor. It is polymorphic in the number of relation wires and the number
of public leaves. A name/path or alias check is never inferred from a proof
word: both are checked before the first-occurrence wire projection.

The premises start after JSON parsing, canonical-byte/digest validation, and
descriptor-to-relation validation. The latter steps are not proved here.
-/

namespace S31.Functional.RecordStatementV2

open RecordAbiV2

structure Descriptor (n : Nat) where
  path : List Segment
  kind : PublicLeafKind
  width : Nat
  wire : Fin n
deriving DecidableEq

structure Claim where
  path : List Segment
  words : List Nat
deriving DecidableEq

/-- One checked claim has the exact path, block width, and word range of its
declared leaf. The bit tag additionally restricts its sole word to 0 or 1. -/
def WellFormed {n : Nat} (descriptor : Descriptor n) (claim : Claim) : Prop :=
  claim.path = descriptor.path ∧
  claim.words.length = descriptor.width ∧
  ∀ word ∈ claim.words, word < publicLeafBound descriptor.kind

def checkClaim {n : Nat} (descriptor : Descriptor n) (claim : Claim) : Bool :=
  decide (claim.path = descriptor.path) &&
  decide (claim.words.length = descriptor.width) &&
  claim.words.all (fun word => decide (word < publicLeafBound descriptor.kind))

theorem checkClaim_iff {n : Nat} (descriptor : Descriptor n) (claim : Claim) :
    checkClaim descriptor claim = true ↔ WellFormed descriptor claim := by
  simp [checkClaim, WellFormed, List.all_eq_true, and_assoc]

/-- Positional comparison rejects an extra or missing public claim. -/
def checkOrdered {n : Nat} : List (Descriptor n) → List Claim → Bool
  | [], [] => true
  | descriptor :: descriptors, claim :: claims =>
      checkClaim descriptor claim && checkOrdered descriptors claims
  | _, _ => false

theorem checkOrdered_iff {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) :
    checkOrdered descriptors claims = true ↔
      List.Forall₂ WellFormed descriptors claims := by
  induction descriptors generalizing claims with
  | nil =>
      cases claims <;> simp [checkOrdered]
  | cons descriptor descriptors ih =>
      cases claims with
      | nil => simp [checkOrdered]
      | cons claim claims =>
          simp [checkOrdered, checkClaim_iff, ih]

/-- Pairwise consistency implements the native wire-value map's rule:
repeated references to one wire must carry identical payloads. A different
path does not create another wire. -/
def AliasConsistent {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) : Prop :=
  ∀ first ∈ List.zip descriptors claims,
    ∀ second ∈ List.zip descriptors claims,
      first.1.wire = second.1.wire → first.2.words = second.2.words

def checkAliases {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) : Bool :=
  let pairs := List.zip descriptors claims
  pairs.all fun first =>
    pairs.all fun second =>
      decide (first.1.wire = second.1.wire →
        first.2.words = second.2.words)

theorem checkAliases_iff {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) :
    checkAliases descriptors claims = true ↔
      AliasConsistent descriptors claims := by
  simp [checkAliases, AliasConsistent, List.all_eq_true]
  constructor
  · intro checked firstDescriptor firstClaim firstPresent
      secondDescriptor secondClaim secondPresent sameWire
    exact (checked firstDescriptor firstClaim firstPresent
      secondDescriptor secondClaim secondPresent).resolve_left
        (by intro different; exact different sameWire)
  · intro consistent firstDescriptor firstClaim firstPresent
      secondDescriptor secondClaim secondPresent
    by_cases sameWire : firstDescriptor.wire = secondDescriptor.wire
    · exact Or.inr (consistent firstDescriptor firstClaim firstPresent
        secondDescriptor secondClaim secondPresent sameWire)
    · exact Or.inl sameWire

def admitClaims {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) : Bool :=
  checkOrdered descriptors claims && checkAliases descriptors claims

/-- General statement admission equivalence for any number and ordering of
public roots/result leaves. It makes leaf count, order, shape, range, and
repeated-wire agreement explicit in the theorem conclusion. -/
theorem admitClaims_iff {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) :
    admitClaims descriptors claims = true ↔
      List.Forall₂ WellFormed descriptors claims ∧
      AliasConsistent descriptors claims := by
  simp [admitClaims, checkOrdered_iff, checkAliases_iff]

theorem admitted_same_wire_same_words {n : Nat}
    (descriptors : List (Descriptor n)) (claims : List Claim)
    (accepted : admitClaims descriptors claims = true)
    (first second : Descriptor n × Claim)
    (firstPresent : first ∈ List.zip descriptors claims)
    (secondPresent : second ∈ List.zip descriptors claims)
    (sameWire : first.1.wire = second.1.wire) :
    first.2.words = second.2.words := by
  exact ((admitClaims_iff descriptors claims).mp accepted).2
    first firstPresent second secondPresent sameWire

/-- Look up the first claimed payload for a relation wire, as the native
parser does after checking every alias. The caller's public input/output wire
lists are already bound to the validated relation. -/
def firstWireWords {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) (wire : Fin n) : Option (List Nat) :=
  ((List.zip descriptors claims).find? (fun pair => pair.1.wire == wire)).map
    (fun pair => pair.2.words)

/-- Once aliases have passed, looking up the first claim for any present wire
returns the payload of every claim for that wire. This justifies replacing the
native mutable wire-value map by a first-occurrence lookup in the model. -/
theorem firstWireWords_admitted {n : Nat}
    (descriptors : List (Descriptor n)) (claims : List Claim)
    (accepted : admitClaims descriptors claims = true)
    (pair : Descriptor n × Claim)
    (present : pair ∈ List.zip descriptors claims) :
    firstWireWords descriptors claims pair.1.wire = some pair.2.words := by
  let pairs := List.zip descriptors claims
  have someFound :
      (pairs.find? (fun candidate => candidate.1.wire == pair.1.wire)).isSome = true :=
    List.find?_isSome.mpr ⟨pair, present, by simp⟩
  obtain ⟨found, foundEq⟩ := Option.isSome_iff_exists.mp someFound
  have foundPresent : found ∈ pairs := List.mem_of_find?_eq_some foundEq
  have sameWire : found.1.wire = pair.1.wire := by
    simpa using List.find?_some foundEq
  have sameWords : found.2.words = pair.2.words :=
    admitted_same_wire_same_words descriptors claims accepted
      found pair foundPresent present sameWire
  simp [firstWireWords, pairs, foundEq, sameWords]

def projectedWords {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) (publicInputs distinctOutputs : List (Fin n)) :
    Option (List Nat) := do
  let inputBlocks ← publicInputs.mapM (firstWireWords descriptors claims)
  let outputBlocks ← distinctOutputs.mapM (firstWireWords descriptors claims)
  let words := inputBlocks.flatMap id ++ outputBlocks.flatMap id
  if 1 ≤ words.length && words.length ≤ 8 then some words else none

def paddedWords {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) (publicInputs distinctOutputs : List (Fin n)) :
    Option (List Nat) := do
  let words ← projectedWords descriptors claims publicInputs distinctOutputs
  some (words ++ List.replicate (8 - words.length) 0)

/-- The statement stage runs every leaf and alias check before projecting
public relation words. This ordering matches the native claimedWords loop. -/
def admitStatement {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) (publicInputs distinctOutputs : List (Fin n)) :
    Option (List Nat) :=
  if admitClaims descriptors claims then
    paddedWords descriptors claims publicInputs distinctOutputs
  else none

/-- Exact semantic characterization of a successfully decoded record
statement. The checked descriptor order, alias equations, and relation-wire
projection are separate obligations; none can be skipped. -/
theorem admitStatement_iff {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) (publicInputs distinctOutputs : List (Fin n))
    (words : List Nat) :
    admitStatement descriptors claims publicInputs distinctOutputs = some words ↔
      List.Forall₂ WellFormed descriptors claims ∧
      AliasConsistent descriptors claims ∧
      paddedWords descriptors claims publicInputs distinctOutputs = some words := by
  by_cases accepted : admitClaims descriptors claims = true
  · simp [admitStatement, accepted, (admitClaims_iff descriptors claims).mp accepted]
  · have rejected : admitClaims descriptors claims = false := by
      cases h : admitClaims descriptors claims <;> simp_all
    constructor
    · intro impossible
      simp [admitStatement, rejected] at impossible
    · rintro ⟨ordered, aliases, _⟩
      exact False.elim (accepted
        ((admitClaims_iff descriptors claims).mpr ⟨ordered, aliases⟩))

/-- A successful model projection always gives precisely eight prover public
word slots. The range gate in `projectedWords` rules out overflow and empty
claims before zero padding. -/
theorem paddedWords_length {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) (publicInputs distinctOutputs : List (Fin n))
    (words : List Nat)
    (accepted : paddedWords descriptors claims publicInputs distinctOutputs =
      some words) : words.length = 8 := by
  unfold paddedWords at accepted
  cases hProjection : projectedWords descriptors claims publicInputs distinctOutputs with
  | none => simp [hProjection] at accepted
  | some raw =>
      simp [hProjection] at accepted
      subst words
      unfold projectedWords at hProjection
      cases hInputs : publicInputs.mapM (firstWireWords descriptors claims) with
      | none => simp [hInputs] at hProjection
      | some inputs =>
          cases hOutputs : distinctOutputs.mapM (firstWireWords descriptors claims) with
          | none => simp [hInputs, hOutputs] at hProjection
          | some outputs =>
              simp [hInputs, hOutputs] at hProjection
              have bound : raw.length ≤ 8 := by
                rcases hProjection with ⟨range, eqRaw⟩
                rw [← eqRaw]
                simpa [List.length_append, List.length_flatten] using range.2
              simp [bound]

theorem admitStatement_sound {n : Nat} (descriptors : List (Descriptor n))
    (claims : List Claim) (publicInputs distinctOutputs : List (Fin n))
    (words : List Nat)
    (accepted : admitStatement descriptors claims publicInputs distinctOutputs =
      some words) :
    List.Forall₂ WellFormed descriptors claims ∧
    AliasConsistent descriptors claims ∧ words.length = 8 := by
  unfold admitStatement at accepted
  cases hClaims : admitClaims descriptors claims with
  | false => simp [hClaims] at accepted
  | true =>
      simp [hClaims] at accepted
      obtain ⟨ordered, aliases⟩ :=
        (admitClaims_iff descriptors claims).mp hClaims
      exact ⟨ordered, aliases,
        paddedWords_length descriptors claims publicInputs distinctOutputs
          words accepted⟩

/-- A generic two-field alias example. The public input and result paths are
distinct while their wire is identical; a changed result claim is rejected. -/
def aliasDescriptors : List (Descriptor 1) :=
  [⟨[.root "request", .field "x"], .m31, 1, 0⟩,
   ⟨[.root "result", .field "copy"], .m31, 1, 0⟩]

def aliasClaims : List Claim :=
  [⟨[.root "request", .field "x"], [7]⟩,
   ⟨[.root "result", .field "copy"], [7]⟩]

theorem alias_example_accepted : admitClaims aliasDescriptors aliasClaims = true := by
  decide

theorem alias_example_projection :
    admitStatement aliasDescriptors aliasClaims [0] [0] =
      some [7, 7, 0, 0, 0, 0, 0, 0] := by
  decide

theorem alias_example_split_rejected :
    admitClaims aliasDescriptors
      [⟨[.root "request", .field "x"], [7]⟩,
       ⟨[.root "result", .field "copy"], [8]⟩] = false := by
  decide

end S31.Functional.RecordStatementV2
