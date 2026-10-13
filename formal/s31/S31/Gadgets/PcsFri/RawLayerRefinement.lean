import S31.Gadgets.PcsFri.LayerAcceptance

/-!
The native FRI capture keeps one slot per raw transcript query, including
duplicates. The verifier itself folds a sorted, deduplicated query set. This
module proves, for any finite layer schedule, that local checks on every raw
slot suffice for `LayerAcceptance.accepts` on the normalized sets.

`rawLayerChecks` is a semantic premise about the native reconstruction,
authenticated openings, and fold output. The Zig-success-to-`rawLayerChecks`
extraction is **not** proved here. The native regression and source guard give
finite differential evidence for it; they do not replace a Zig semantics
proof, Merkle binding, or FRI proximity.
-/

namespace S31.Gadgets.PcsFri.RawLayerRefinement

open S31.Gadgets.PcsFri.QueryAndTranscript
open S31.Gadgets.PcsFri.LayerAcceptance

variable {F : Type*}

/-- The local transition is checked once per raw transcript slot. -/
def rawLayerChecks (raw : List Nat) (current : Nat → F)
    (layer : Layer F) : Prop :=
  ∀ q ∈ raw, localTransition q (current q) layer

/-- The exact three local obligations needed to extract a raw-slot certificate:
queried-value placement and fold output are native operational facts; opened
subset equality with the putative oracle additionally needs Merkle binding. -/
theorem rawLayerChecks_of_components (raw : List Nat)
    (current : Nat → F) (layer : Layer F)
    (hcurrent : ∀ q ∈ raw,
      current q = layer.opened (foldPosition layer.step q) (q % width layer))
    (horacle : ∀ q ∈ raw, ∀ r < width layer,
      layer.opened (foldPosition layer.step q) r =
        layer.oracle (foldPosition layer.step q * width layer + r))
    (hfold : ∀ q ∈ raw,
      layer.next (foldPosition layer.step q) =
        layer.fold (fun r => layer.opened (foldPosition layer.step q) r)) :
    rawLayerChecks raw current layer := by
  intro q hq
  exact ⟨hcurrent q hq, horacle q hq, hfold q hq⟩

/-- Raw-slot checking covers every normalized query and every resulting fold
group, including groups hit by several different raw positions. -/
theorem rawLayerChecks_implies_layerChecks (raw : List Nat)
    (current : Nat → F) (layer : Layer F)
    (hraw : rawLayerChecks raw current layer) :
    layerChecks (normalized raw) current layer := by
  have hall : ∀ q ∈ normalized raw,
      localTransition q (current q) layer :=
    (all_raw_iff_all_normalized raw _).mp hraw
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    exact (hall q hq).1
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (hall q hq).2.1
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (hall q hq).2.2

/-- The next normalized query set is precisely the support of raw positions
shifted for this layer. -/
theorem normalized_folded_raw (raw : List Nat) (layer : Layer F) :
    nextQueries (normalized raw) layer =
      normalized (raw.map (foldPosition layer.step)) := by
  simpa [nextQueries, folded, normalized] using
    (folded_eq_image_of_normalized layer.step raw).symm

/-- Native-style raw-slot acceptance with a local certificate at each layer.
The terminal check is also over raw slots, preserving duplicates. -/
def rawAccepts (raw : List Nat) (current : Nat → F) :
    List (Layer F) → Terminal F → Prop
  | [], terminal =>
      terminalDegreeOk terminal ∧
      ∀ q ∈ raw, current q = terminalEval terminal q
  | layer :: rest, terminal =>
      rawLayerChecks raw current layer ∧
      rawAccepts (raw.map (foldPosition layer.step)) layer.next rest terminal

/-- Arbitrarily many native-style raw layers refine the normalized IOP
acceptance relation, assuming their local certificates. This is the proved
structural portion of native verifier-to-model refinement. -/
theorem rawAccepts_implies_accepts (raw : List Nat) (current : Nat → F)
    (layers : List (Layer F)) (terminal : Terminal F)
    (hraw : rawAccepts raw current layers terminal) :
    accepts (normalized raw) current layers terminal := by
  induction layers generalizing raw current with
  | nil =>
      exact ⟨hraw.1, (all_raw_iff_all_normalized raw _).mp hraw.2⟩
  | cons layer rest ih =>
      refine ⟨rawLayerChecks_implies_layerChecks raw current layer hraw.1, ?_⟩
      rw [normalized_folded_raw]
      exact ih _ _ hraw.2

/-- A raw-slot certificate yields the full arbitrary-layer path and terminal
evaluation already proved for modeled acceptance. -/
theorem rawAccepts_implies_iop_path (raw : List Nat)
    (current : Nat → F) (layers : List (Layer F))
    (terminal : Terminal F)
    (hraw : rawAccepts raw current layers terminal)
    (q : Nat) (hq : q ∈ raw) :
    terminalDegreeOk terminal ∧
    queryPath q (current q) layers terminal ∧
      terminalValue layers q (current q) =
        terminalEval terminal (foldPosition (totalSteps layers) q) := by
  exact modeled_acceptance_has_iop_path raw current layers terminal
    (rawAccepts_implies_accepts raw current layers terminal hraw) q hq

/-- A corrupted local transition in any raw slot prevents raw acceptance
at that layer. This applies after arbitrary prior shifts. -/
theorem bad_raw_transition_rejects (raw : List Nat) (current : Nat → F)
    (layer : Layer F) (rest : List (Layer F)) (terminal : Terminal F)
    (q : Nat) (hq : q ∈ raw)
    (hbad : ¬ localTransition q (current q) layer) :
    ¬ rawAccepts raw current (layer :: rest) terminal := by
  intro haccept
  exact hbad (haccept.1 q hq)

end S31.Gadgets.PcsFri.RawLayerRefinement
