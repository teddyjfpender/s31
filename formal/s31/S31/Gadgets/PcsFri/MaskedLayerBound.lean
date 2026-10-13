import S31.Gadgets.PcsFri.LayerAcceptance
import S31.Gadgets.PcsFri.M31MaskedQuery

/-!
The arbitrary-layer FRI acceptance theorem and the exact M31-masked raw-query
distribution compose in the finite ideal product space. The committed oracle,
good set, and layer schedule must be fixed before raw words are sampled.

This is not a native PCS/FRI soundness theorem. In particular, native verifier
success to modeled acceptance, Merkle binding, ideal independent hash words,
and the IOP proximity bound remain explicit premises.
-/

namespace S31.Gadgets.PcsFri.MaskedLayerBound

open S31.Gadgets.PcsFri.LayerAcceptance
open S31.Gadgets.PcsFri.M31MaskedQuery

variable {F : Type*}

/-- The native channel reduces a raw 32-bit word modulo M31 before masking. -/
def position (k : Nat) (word : Fin rawSize) : Nat :=
  sampleIndex k word.val

/-- Exact masked-query replacement for the uniform query term in the
arbitrary-layer conditional bound. The `hproximity` premise is about the fixed
raw-word good event; it must be obtained from a separate FRI proximity theorem.
The `h_native_refines` premise is the missing Zig success-to-model bridge. -/
theorem conditional_native_masked_layers_bound
    (k draws : Nat) (hk : 2 ≤ k) (hk31 : k ≤ 31)
    (current : Nat → F) (layers : List (Layer F)) (terminal : Terminal F)
    (good : Finset (Fin (2 ^ k))) (alpha : ℚ)
    (nativeAccepted merkleFailure samplingFailure :
      Finset (Fin draws → Fin rawSize))
    (merkleBudget samplingBudget : ℚ)
    (hα : uniformMass k good ≤ alpha)
    (hproximity : ∀ word : Fin rawSize,
      queryPath (position k word) (current (position k word)) layers terminal →
        word ∈ goodRawFin k good)
    (h_native_refines : nativeAccepted ⊆
      merkleFailure ∪ samplingFailure ∪
        modeledAccepted draws (position k) current layers terminal)
    (h_merkle : (merkleFailure.card : ℚ) /
      (Fintype.card (Fin draws → Fin rawSize) : ℚ) ≤ merkleBudget)
    (h_sampling : (samplingFailure.card : ℚ) /
      (Fintype.card (Fin draws → Fin rawSize) : ℚ) ≤ samplingBudget) :
    (nativeAccepted.card : ℚ) /
      (Fintype.card (Fin draws → Fin rawSize) : ℚ) ≤
      merkleBudget + samplingBudget +
        (alpha + 2 / (rawSize : ℚ)) ^ draws := by
  haveI : Nonempty (Fin rawSize) := ⟨⟨0, by norm_num [rawSize]⟩⟩
  have hbase := conditional_native_general_layers_bound
    draws (position k) current layers terminal (goodRawFin k good)
    nativeAccepted merkleFailure samplingFailure merkleBudget samplingBudget
    hproximity h_native_refines h_merkle h_sampling
  have hgood :
      (((goodRawFin k good).card : ℚ) /
        (Fintype.card (Fin rawSize) : ℚ)) ^ draws =
        maskedMass k good ^ draws := by
    simp only [Fintype.card_fin, maskedMass, good_raw_fin_card]
  have hbase' :
      (nativeAccepted.card : ℚ) /
        (Fintype.card (Fin draws → Fin rawSize) : ℚ) ≤
        merkleBudget + samplingBudget + maskedMass k good ^ draws := by
    simpa only [hgood] using hbase
  have hbiased := independent_masked_ge_two_vs_alpha k hk hk31
    good draws alpha hα
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (hbase'.trans (add_le_add_right hbiased (merkleBudget + samplingBudget)))

end S31.Gadgets.PcsFri.MaskedLayerBound
