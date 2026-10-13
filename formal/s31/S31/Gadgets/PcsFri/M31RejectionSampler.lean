import Mathlib.Tactic

/-!
The arithmetic part of the pinned Blake2s-M31 rejection sampler. It accepts
32-bit words below `2p`, where `p = 2^31 - 1`, and reduces them modulo `p`.
Every M31 residue has exactly two accepted word preimages. The theorem does
not model BLAKE2s, independence of hash blocks, transcript adaptivity, or
the Zig implementation's operational semantics.
-/

namespace S31.Gadgets.PcsFri.M31RejectionSampler

def modulus : Nat := 2147483647
def wordSpace : Nat := 4294967296

theorem twice_modulus : 2 * modulus = wordSpace - 2 := by decide

theorem accepted_preimages (r x : Nat) (hr : r < modulus) :
    (x < 2 * modulus ∧ x % modulus = r) ↔
      x = r ∨ x = r + modulus := by
  unfold modulus at *
  omega

theorem accepted_first (r : Nat) (hr : r < modulus) :
    r < 2 * modulus ∧ r % modulus = r := by
  exact (accepted_preimages r r hr).2 (Or.inl rfl)

theorem accepted_second (r : Nat) (hr : r < modulus) :
    r + modulus < 2 * modulus ∧ (r + modulus) % modulus = r := by
  exact (accepted_preimages r (r + modulus) hr).2 (Or.inr rfl)

theorem distinct_preimages (r : Nat) : r ≠ r + modulus := by
  unfold modulus
  omega

end S31.Gadgets.PcsFri.M31RejectionSampler
