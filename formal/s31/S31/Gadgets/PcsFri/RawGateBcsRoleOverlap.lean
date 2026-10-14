import S31.Gadgets.PcsFri.MerkleBytePreimage
import Mathlib.Tactic

/-!
Byte-input equalities for the selected raw Gate channel and plain Merkle
profile. `hash` is uninterpreted. These facts show that role labels are not
encoded into the messages sent to BLAKE2s; they are not accepted-proof
counterexamples and do not quantify cryptographic security.
-/

namespace S31.Gadgets.PcsFri.RawGateBcsRoleOverlap

open S31.Gadgets.PcsFri.MerkleBytePreimage

/-- The selected channel's root absorption hashes `digest ++ root`. -/
def rootAbsorbMessage (digest root : List Nat) : List Nat := digest ++ root

/-- The selected channel's QM31-array absorption hashes the digest followed
by four little-endian bytes per canonical M31 limb. -/
def fieldAbsorbMessage (digest limbs : List Nat) : List Nat :=
  digest ++ leafMessage limbs

/-- For every pair of 32-byte digests, root absorption and a plain Merkle
parent use the same input bytes. No BLAKE2s collision is involved. -/
theorem root_absorption_is_plain_parent (digest root : List Nat) :
    rootAbsorbMessage digest root = parentMessage digest root := rfl

/-- A root whose bytes encode eight canonical M31 limbs is also the exact
payload of two QM31 values in the channel. The caller supplies the equality;
this theorem makes no claim that such a root occurs in an accepted proof. -/
theorem canonical_root_is_two_felt_payload
    (digest root limbs : List Nat)
    (rootBytes : root = leafMessage limbs) :
    rootAbsorbMessage digest root = fieldAbsorbMessage digest limbs := by
  simp [rootAbsorbMessage, fieldAbsorbMessage, rootBytes]

/-- A concrete 32-byte encoding witness exists, so the two role encodings
are not disjoint even before any hash is evaluated. -/
theorem zero_eight_limb_encoding_has_32_bytes :
    (leafMessage (List.replicate 8 0)).length = 32 := by decide

/-- A 16-word plain leaf is 64 bytes, the same byte shape as a parent. This
is an encoding overlap, not a witness of two valid Merkle paths. -/
theorem zero_sixteen_word_leaf_is_parent_message :
    leafMessage (List.replicate 16 0) =
      parentMessage (List.replicate 32 0) (List.replicate 32 0) := by decide

/-- Paper-only collision term at T=2^64 fails the 96-bit work-factor target
for lambda=161. Native lambda remains unassigned. -/
theorem paper_collision_161_exceeds_target :
    (1 : ℚ) / 2 ^ 96 <
      3 * (((2 : ℚ) ^ 64) ^ 2 + 1) / ((2 : ℚ) ^ 161 * 2 ^ 64) := by
  norm_num

/-- Lambda=162 leaves a positive budget for the IOP round errors, *if* a
matching BCS reduction and a 162-bit collision bound are later established. -/
theorem paper_collision_162_below_target :
    3 * (((2 : ℚ) ^ 64) ^ 2 + 1) / ((2 : ℚ) ^ 162 * 2 ^ 64) <
      (1 : ℚ) / 2 ^ 96 := by
  norm_num

end S31.Gadgets.PcsFri.RawGateBcsRoleOverlap
