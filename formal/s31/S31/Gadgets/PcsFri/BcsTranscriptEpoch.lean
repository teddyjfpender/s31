import S31.Gadgets.PcsFri.QueryAndTranscript

/-!
Abstract pre-hash-input facts for the P07 post-PoW query epoch. The native
source audit and independent Zig/Python differential fixture establish the
selected direct Gate schedule and byte encoding only for pinned source and
tested inputs. Here `H` is deliberately uninterpreted: none of these theorems
claim Blake2s random-oracle security, PoW soundness, or full BCS reduction.
-/

namespace S31.Gadgets.PcsFri.BcsTranscriptEpoch

open S31.Gadgets.PcsFri.QueryAndTranscript

/-- The next digest after a verified nonce is absorbed. The nonce's exact
little-endian bytes are supplied by the caller. -/
def afterNonce (H : Bytes → Bytes) (before nonceLE : Bytes) : Bytes :=
  H (before ++ nonceLE)

/-- The messages sent to `H` by a fresh sequence of query-block draws. -/
def queryInputs (H : Bytes → Bytes) (before nonceLE : Bytes)
    (counterLE : Nat → Bytes) (blocks : Nat) : List Bytes :=
  (List.range blocks).map (fun i =>
    drawMessage (afterNonce H before nonceLE) (counterLE i))

theorem query_inputs_length (H : Bytes → Bytes) (before nonceLE : Bytes)
    (counterLE : Nat → Bytes) (blocks : Nat) :
    (queryInputs H before nonceLE counterLE blocks).length = blocks := by
  simp [queryInputs]

/-- Injective counter encodings give distinct hash *inputs* in this epoch.
There is no claim here that the hash outputs are distinct. -/
theorem query_inputs_nodup (H : Bytes → Bytes) (before nonceLE : Bytes)
    (counterLE : Nat → Bytes) (blocks : Nat)
    (hcounter : Function.Injective counterLE) :
    (queryInputs H before nonceLE counterLE blocks).Nodup := by
  unfold queryInputs
  apply (List.nodup_map_iff_inj_on List.nodup_range).2
  intro i _ j _ heq
  exact hcounter (draw_message_injective_at_fixed_digest
    (afterNonce H before nonceLE) (counterLE i) (counterLE j) heq)

/-- Seventy queries consume nine eight-word blocks. Every counter is below
the u32 cardinality, assuming absorption reset the counter to zero. -/
theorem sealed_gate_query_epoch :
    (70 + 8 - 1) / 8 = 9 ∧
    ∀ i ∈ List.range 9, i < 2 ^ 32 := by
  constructor
  · decide
  · intro i hi
    have h : i < 9 := List.mem_range.mp hi
    omega

/-- Concrete little-endian u32 bytes for the bounded query counters. -/
def counterLE32 (n : Nat) : Bytes :=
  [UInt8.ofNat n, UInt8.ofNat (n / 256),
   UInt8.ofNat (n / 65536), UInt8.ofNat (n / 16777216)]

/-- For the sealed 70-query epoch the native counter encodings 0 through 8
are distinct. This uses exact finite reduction, without a global injectivity
assumption for a wrapping u32 encoding. -/
theorem sealed_gate_query_inputs_nodup (H : Bytes → Bytes)
    (before nonceLE : Bytes) :
    (queryInputs H before nonceLE counterLE32 9).Nodup := by
  have hencoded : ((List.range 9).map counterLE32).Nodup := by
    decide
  unfold queryInputs
  apply (List.nodup_map_iff_inj_on List.nodup_range).2
  intro i hi j hj heq
  have hcounter := (List.nodup_map_iff_inj_on List.nodup_range).mp hencoded
  exact hcounter i hi j hj (draw_message_injective_at_fixed_digest
    (afterNonce H before nonceLE) (counterLE32 i) (counterLE32 j) heq)

/-- The abstract successful query epoch requires a checked nonce. -/
def checkedQueryInputs (valid : Bytes → Bool) (H : Bytes → Bytes)
    (before nonceLE : Bytes) (counterLE : Nat → Bytes)
    (blocks : Nat) : Option (List Bytes) :=
  if valid nonceLE then some (queryInputs H before nonceLE counterLE blocks) else none

theorem checked_query_epoch_requires_valid_nonce (valid : Bytes → Bool)
    (H : Bytes → Bytes) (before nonceLE : Bytes)
    (counterLE : Nat → Bytes) (blocks : Nat) (inputs : List Bytes)
    (h : checkedQueryInputs valid H before nonceLE counterLE blocks = some inputs) :
    valid nonceLE = true ∧
    inputs = queryInputs H before nonceLE counterLE blocks := by
  unfold checkedQueryInputs at h
  split at h
  · constructor
    · assumption
    · exact Option.some.inj h |>.symm
  · cases h

end S31.Gadgets.PcsFri.BcsTranscriptEpoch
