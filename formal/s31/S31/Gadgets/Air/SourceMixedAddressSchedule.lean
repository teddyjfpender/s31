import S31.Gadgets.Air.SourceMixedPath

/-!
Exact address arithmetic for the reviewed one-to-eight-call mixed chain
family. The independent Python/native-inspector acceptance test uses the same
closed formulas. These theorems establish canonical addresses, repeated
handoff identity, and fresh output blocks for the *modeled* schedule. They do
not prove that the production Zig compiler emits this schedule; that equality
is checked separately by the native inspector fixture.
-/

namespace S31.Gadgets.Air.SourceMixedAddressSchedule

open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Packed

/-- Context/public reservations end at 10. The first four private inputs are
11..14. Later inputs are the previous call's four output words. -/
def inputAddress (call lane : Nat) : Nat :=
  if call = 0 then 11 + lane else 13 + 10 * call + lane

/-- Every call allocates four scalar outputs and six packing temporaries, so
successive output blocks advance by ten addresses. -/
def outputAddress (call lane : Nat) : Nat :=
  23 + 10 * call + lane

def bridgeAddress (call : Nat) (slot : Fin 8) : Nat :=
  if slot.val < 4 then inputAddress call slot.val
  else outputAddress call (slot.val - 4)

theorem first_input (lane : Fin 4) :
    inputAddress 0 lane.val = 11 + lane.val := by
  simp [inputAddress]

theorem next_input_is_previous_output (call lane : Nat) :
    inputAddress (call + 1) lane = outputAddress call lane := by
  simp [inputAddress, outputAddress]
  omega

theorem output_block_fresh (first second laneFirst laneSecond : Nat)
    (hfirst : first < second) (hlaneFirst : laneFirst < 4)
    (hlaneSecond : laneSecond < 4) :
    outputAddress first laneFirst ≠ outputAddress second laneSecond := by
  simp only [outputAddress]
  omega

theorem input_output_disjoint (call laneInput laneOutput : Nat)
    (hi : laneInput < 4) (ho : laneOutput < 4) :
    inputAddress call laneInput ≠ outputAddress call laneOutput := by
  unfold inputAddress outputAddress
  split_ifs <;> omega

theorem first_input_not_public_output (lane : Fin 4) :
    10 < inputAddress 0 lane.val := by
  simp only [inputAddress, ↓reduceIte]
  omega

/-- Every modeled bridge address is a canonical M31 field element for any
admitted call count. -/
def canonicalAddress {N : Nat} (hN : N ≤ 8)
    (call : Fin N) (slot : Fin 8) : CanonicalAddress :=
  ⟨bridgeAddress call.val slot, by
    have hcall : call.val < 8 := Nat.lt_of_lt_of_le call.isLt hN
    have hslot := slot.isLt
    unfold bridgeAddress inputAddress outputAddress
    split_ifs <;> omega⟩

theorem canonical_handoff {N : Nat} (hN : N ≤ 8)
    (call : Fin N) (hnext : call.val + 1 < N) (lane : Fin 4) :
    canonicalAddress hN ⟨call.val + 1, hnext⟩ ⟨lane.val, by omega⟩ =
      canonicalAddress hN call ⟨4 + lane.val, by omega⟩ := by
  apply Fin.ext
  simp [canonicalAddress, bridgeAddress, next_input_is_previous_output]

theorem first_call_addresses :
    (List.ofFn fun slot : Fin 8 =>
      canonicalAddress (by decide : 1 ≤ 8) (0 : Fin 1) slot).map Fin.val =
      [11, 12, 13, 14, 23, 24, 25, 26] := by
  decide

theorem eighth_call_addresses :
    (List.ofFn fun slot : Fin 8 =>
      canonicalAddress (by decide : 8 ≤ 8) (7 : Fin 8) slot).map Fin.val =
      [83, 84, 85, 86, 93, 94, 95, 96] := by
  decide

/-- Every bridge endpoint is a Gate use. Exact Gate balance then locates its
value among circuit yields; the bridge itself is not a producer. -/
private theorem bridge_event_produced {N : Nat} (boundary : Boundary N)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (call : Fin N) (slot : Fin 8) :
    ((boundary.addresses call slot).val, base (boundary.words call slot)) ∈
      allYields boundary.jointGateSource.gateRows
        boundary.jointGateSource.gateExternalYields := by
  apply hbalance.mem_iff.mp
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(boundary.addresses call slot, base (boundary.words call slot)), ?_, rfl⟩
  unfold Boundary.jointGateSource
  apply List.mem_append_right
  unfold Boundary.bridgeGates
  apply List.mem_flatMap.mpr
  exact ⟨call, List.mem_finRange call,
    List.mem_ofFn.mpr ⟨slot, rfl⟩⟩

/-- If the native Gate source has one value per produced address, the exact
source-shaped address schedule forces the next chip's four input words to be
the previous chip's four output words. The Gate uniqueness premise is still
an AIR/lookup/PCS obligation for a production proof. -/
theorem adjacent_call_words_coherent {N : Nat} (hN : N ≤ 8)
    (boundary : Boundary N)
    (haddresses : ∀ call slot,
      boundary.addresses call slot = canonicalAddress hN call slot)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (hunique : uniqueProduced
      (allYields boundary.jointGateSource.gateRows
        boundary.jointGateSource.gateExternalYields))
    (call : Fin N) (hnext : call.val + 1 < N) (lane : Fin 4) :
    boundary.words ⟨call.val + 1, hnext⟩ ⟨lane.val, by omega⟩ =
      boundary.words call ⟨4 + lane.val, by omega⟩ := by
  let next : Fin N := ⟨call.val + 1, hnext⟩
  let input : Fin 8 := ⟨lane.val, by omega⟩
  let output : Fin 8 := ⟨4 + lane.val, by omega⟩
  have sameAddress : boundary.addresses next input =
      boundary.addresses call output := by
    rw [haddresses next input, haddresses call output]
    exact canonical_handoff hN call hnext lane
  have samePacked := hunique (boundary.addresses next input).val
    (base (boundary.words next input))
    (base (boundary.words call output))
    (bridge_event_produced boundary hbalance next input)
    (by simpa [sameAddress] using bridge_event_produced boundary hbalance call output)
  exact congrArg Quad.a samePacked

end S31.Gadgets.Air.SourceMixedAddressSchedule
