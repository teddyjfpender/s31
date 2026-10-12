import S31.Gadgets.Functional.RecordStatementV2

/-!
The public `u32` record ABI v2 uses two little-endian `u16` words. Each word
is an M31 public cell, while the 32-bit integer is a source-level value; no
single M31 cell is asserted to hold that integer. This module proves the
integer packing identity and reuses the modeled statement parser's exact
alias check. It assumes the production parser has validated a `u32` leaf's
width and ordering and the native circuit has constrained both limbs. It is
not a refinement proof for Python/Zig parsing, AIR emission, or STARK soundness.
-/

namespace S31.Functional.RecordU32BoundaryV2

open RecordAbiV2 RecordStatementV2

def limbBase : Nat := 65536

/-- Decode the ABI's low word followed by high word. The optional result
rejects extra words, missing words, and either non-u16 limb. -/
def packWords : List Nat → Option Nat
  | [low, high] =>
      if low < limbBase ∧ high < limbBase then
        some (low + limbBase * high)
      else none
  | _ => none

def unpackWords (value : Nat) : List Nat :=
  [value % limbBase, value / limbBase]

theorem packed_value_bounded (low high : Nat)
    (lowBound : low < limbBase) (highBound : high < limbBase) :
    low + limbBase * high < 4294967296 := by
  unfold limbBase at *
  omega

/-- Every canonical unsigned 32-bit value has two bounded u16 words and
packing those words recovers the value exactly. -/
theorem pack_unpack (value : Nat) (bounded : value < 4294967296) :
    packWords (unpackWords value) = some value := by
  have lowBound : value % limbBase < limbBase := by
    unfold limbBase
    exact Nat.mod_lt _ (by decide)
  have highBound : value / limbBase < limbBase := by
    unfold limbBase at *
    omega
  have identity : value % limbBase + limbBase * (value / limbBase) = value := by
    exact Nat.mod_add_div value limbBase
  simp [packWords, unpackWords, lowBound, highBound, identity]

/-- In the other direction, every accepted pair of u16 words has precisely
one 32-bit value and unpacking it recovers the same pair. -/
theorem unpack_pack (low high : Nat)
    (lowBound : low < limbBase) (_highBound : high < limbBase) :
    unpackWords (low + limbBase * high) = [low, high] := by
  have lowIdentity : (low + limbBase * high) % limbBase = low := by
    unfold limbBase at *
    omega
  have highIdentity : (low + limbBase * high) / limbBase = high := by
    unfold limbBase at *
    omega
  simp [unpackWords, lowIdentity, highIdentity]

theorem checked_pair_packs (low high : Nat)
    (lowBound : low < limbBase) (highBound : high < limbBase) :
    packWords [low, high] = some (low + limbBase * high) := by
  simp [packWords, lowBound, highBound]

theorem high_limb_out_of_range (low : Nat) :
    packWords [low, 65536] = none := by
  simp [packWords, limbBase]

theorem low_limb_out_of_range (high : Nat) :
    packWords [65536, high] = none := by
  simp [packWords, limbBase]

theorem width_mismatch_rejected (low high extra : Nat) :
    packWords [low, high, extra] = none := by
  rfl

/-- The modeled statement parser's accepted `u32` descriptor has exactly two
bounded limb claims. Its range test is per limb, not on a fictitious M31 word
holding the entire 32-bit integer. -/
theorem checked_u32_claim_packs {n : Nat} (descriptor : Descriptor n)
    (claim : Claim)
    (shape : descriptor.kind = .u32 ∧ descriptor.width = 2)
    (accepted : checkClaim descriptor claim = true) :
    ∃ low high, claim.words = [low, high] ∧
      low < limbBase ∧ high < limbBase ∧
      packWords claim.words = some (low + limbBase * high) ∧
      low + limbBase * high < 4294967296 := by
  obtain ⟨_, length, range⟩ := (checkClaim_iff descriptor claim).mp accepted
  have two : claim.words.length = 2 := by simpa [shape.2] using length
  obtain ⟨low, high, words⟩ := List.length_eq_two.mp two
  have lowBound : low < limbBase := by
    have h := range low (by simp [words])
    simpa [shape.1, publicLeafBound, limbBase] using h
  have highBound : high < limbBase := by
    have h := range high (by simp [words])
    simpa [shape.1, publicLeafBound, limbBase] using h
  exact ⟨low, high, words, lowBound, highBound,
    by simpa [words] using checked_pair_packs low high lowBound highBound,
    packed_value_bounded low high lowBound highBound⟩

/-- When the model admits two named leaves referring to the same relation
wire, their packed integers agree. The separate descriptor validation premise
requires each named leaf to have kind `u32` and width two. -/
theorem admitted_u32_alias_same_value {n : Nat}
    (descriptors : List (Descriptor n)) (claims : List Claim)
    (accepted : admitClaims descriptors claims = true)
    (first second : Descriptor n × Claim)
    (firstPresent : first ∈ List.zip descriptors claims)
    (secondPresent : second ∈ List.zip descriptors claims)
    (firstU32 : first.1.kind = .u32 ∧ first.1.width = 2)
    (secondU32 : second.1.kind = .u32 ∧ second.1.width = 2)
    (firstChecked : checkClaim first.1 first.2 = true)
    (secondChecked : checkClaim second.1 second.2 = true)
    (sameWire : first.1.wire = second.1.wire) :
    ∃ value, packWords first.2.words = some value ∧
      packWords second.2.words = some value ∧ value < 4294967296 := by
  obtain ⟨lowA, highA, _, _, _, packedA, boundA⟩ :=
    checked_u32_claim_packs first.1 first.2 firstU32 firstChecked
  obtain ⟨lowB, highB, _, _, _, packedB, _⟩ :=
    checked_u32_claim_packs second.1 second.2 secondU32 secondChecked
  have sameWords := admitted_same_wire_same_words descriptors claims accepted
    first second firstPresent secondPresent sameWire
  have equalValues : lowA + limbBase * highA = lowB + limbBase * highB := by
    apply Option.some.inj
    calc
      some (lowA + limbBase * highA) = packWords first.2.words := packedA.symm
      _ = packWords second.2.words := congrArg packWords sameWords
      _ = some (lowB + limbBase * highB) := packedB
  exact ⟨lowA + limbBase * highA, packedA,
    by simpa [equalValues] using packedB, boundA⟩

def exampleDescriptors : List (Descriptor 1) :=
  [⟨[.root "request", .field "amount"], .u32, 2, 0⟩,
   ⟨[.root "result", .field "first"], .u32, 2, 0⟩,
   ⟨[.root "result", .field "again"], .u32, 2, 0⟩]

def exampleClaims : List Claim :=
  [⟨[.root "request", .field "amount"], [22136, 4660]⟩,
   ⟨[.root "result", .field "first"], [22136, 4660]⟩,
   ⟨[.root "result", .field "again"], [22136, 4660]⟩]

def exampleInputPair : Descriptor 1 × Claim :=
  (⟨[.root "request", .field "amount"], .u32, 2, 0⟩,
   ⟨[.root "request", .field "amount"], [22136, 4660]⟩)

def exampleAliasPair : Descriptor 1 × Claim :=
  (⟨[.root "result", .field "again"], .u32, 2, 0⟩,
   ⟨[.root "result", .field "again"], [22136, 4660]⟩)

/-- 0x12345678 = 22136 + 65536 * 4660. Naming the same output twice adds
two typed result leaves but just one distinct public result wire. -/
theorem example_packs : packWords [22136, 4660] = some 305419896 := by
  decide

theorem example_admitted : admitClaims exampleDescriptors exampleClaims = true := by
  decide

theorem example_alias_same_integer :
    ∃ value, packWords exampleInputPair.2.words = some value ∧
      packWords exampleAliasPair.2.words = some value ∧
      value < 4294967296 := by
  exact admitted_u32_alias_same_value exampleDescriptors exampleClaims
    example_admitted exampleInputPair exampleAliasPair
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem example_projected :
    admitStatement exampleDescriptors exampleClaims [0] [0] =
      some [22136, 4660, 22136, 4660, 0, 0, 0, 0] := by
  decide

theorem example_changed_alias_rejected :
    admitClaims exampleDescriptors
      [⟨[.root "request", .field "amount"], [22136, 4660]⟩,
       ⟨[.root "result", .field "first"], [22136, 4660]⟩,
       ⟨[.root "result", .field "again"], [22137, 4660]⟩] = false := by
  decide

theorem example_bad_high_limb_rejected :
    admitClaims exampleDescriptors
      [⟨[.root "request", .field "amount"], [22136, 65536]⟩,
       ⟨[.root "result", .field "first"], [22136, 65536]⟩,
       ⟨[.root "result", .field "again"], [22136, 65536]⟩] = false := by
  decide

end S31.Functional.RecordU32BoundaryV2
