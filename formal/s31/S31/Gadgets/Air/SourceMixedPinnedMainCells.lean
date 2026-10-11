import S31.Gadgets.Air.SourceMixedDecodedBoundary
import S31.Gadgets.Air.SourceMixedFixedWeightBridge

/-!
Exact committed-main-cell premises for the source-pinned mixed N1/N8 chain.
A positive decoded producer row gives `ValueAt` for its *actual output main
value*, without Gate balance or a selected challenge. Ten finite row positions
per chain size bind those values to packed endpoints and basis constants.
The main-cell equalities remain explicit; local Gate AIR alone cannot pin
same-address inputs to the same value without lookup coherence.
-/

namespace S31.Gadgets.Air.SourceMixedPinnedMainCells

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedPublicClosure
open S31.Gadgets.Air.SourceMixedFixedOutputSchedule
open S31.Gadgets.Air.SourceMixedScheduledPublicPath
open S31.Gadgets.Air.SourceMixedDecodedBoundary
open S31.Gadgets.Air.SourceMixedLookupBound
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.GeneratedMixedFixedRows

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- A positive row of the exact decoded Gate list produces its actual main
output at its fixed output address. This does not rely on arithmetic AIR or
lookup balance; the main value itself is a premise. -/
theorem valueAt_of_decoded_output {N : Nat} (boundary : Boundary N)
    (trace : Trace 9)
    (hrows : nativeRows trace = boundary.rows.map CanonicalRow.toGate)
    (i : Fin 512) (address : Nat) (value : Quad)
    (haddress : (row trace i).outAddress = address)
    (hpositive : 0 < (row trace i).multiplicity)
    (hmain : (row trace i).output = value) :
    ValueAt boundary address value := by
  have hmem : row trace i ∈ boundary.jointGateSource.gateRows := by
    change row trace i ∈ boundary.rows.map CanonicalRow.toGate
    rw [← hrows]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hyield := row_output_yield
    boundary.jointGateSource.gateRows
    boundary.jointGateSource.gateExternalYields
    (row trace i) hmem hpositive
  simpa [ValueAt, produced, haddress, hmain] using hyield

def n1UnitRow (lane : Fin 4) : Fin 512 :=
  ([16, 461, 474, 489] : List (Fin 512))[lane.val]!

def n8UnitRow (lane : Fin 4) : Fin 512 :=
  ([37, 412, 446, 461] : List (Fin 512))[lane.val]!

def n1InverseRow (lane : Fin 4) : Fin 512 :=
  ([0, 488, 494, 484] : List (Fin 512))[lane.val]!

def n8InverseRow (lane : Fin 4) : Fin 512 :=
  ([0, 460, 466, 456] : List (Fin 512))[lane.val]!

/-- Exactly ten output main cells per chain size. These are concrete trace
cells, not logical wire equalities inferred from a lookup claim. -/
structure N1MainPins (trace : Trace 9) (initial final : State) : Prop where
  packedInitial : (row trace ⟨2, by decide⟩).output = packState initial
  packedFinal : (row trace ⟨5, by decide⟩).output = packState final
  zero : (row trace ⟨15, by decide⟩).output = base 0
  unit : ∀ lane, (row trace (n1UnitRow lane)).output = unit lane
  inverse : ∀ lane, lane.val ≠ 0 →
    (row trace (n1InverseRow lane)).output = unitInverse lane

structure N8MainPins (trace : Trace 9) (initial final : State) : Prop where
  packedInitial : (row trace ⟨2, by decide⟩).output = packState initial
  packedFinal : (row trace ⟨26, by decide⟩).output = packState final
  zero : (row trace ⟨36, by decide⟩).output = base 0
  unit : ∀ lane, (row trace (n8UnitRow lane)).output = unit lane
  inverse : ∀ lane, lane.val ≠ 0 →
    (row trace (n8InverseRow lane)).output = unitInverse lane

private theorem n1_fixed_pins :
    (N1.fixedAt ⟨2, by decide⟩ ⟨6, by decide⟩).val = 22 ∧
    0 < (N1.fixedAt ⟨2, by decide⟩ ⟨7, by decide⟩).val ∧
    (N1.fixedAt ⟨5, by decide⟩ ⟨6, by decide⟩).val = 32 ∧
    0 < (N1.fixedAt ⟨5, by decide⟩ ⟨7, by decide⟩).val ∧
    (N1.fixedAt ⟨15, by decide⟩ ⟨6, by decide⟩).val = 0 ∧
    0 < (N1.fixedAt ⟨15, by decide⟩ ⟨7, by decide⟩).val ∧
    (∀ lane : Fin 4,
      (N1.fixedAt (n1UnitRow lane) ⟨6, by decide⟩).val =
        unitAddress lane ∧
      0 < (N1.fixedAt (n1UnitRow lane) ⟨7, by decide⟩).val) ∧
    (∀ lane : Fin 4, lane.val ≠ 0 →
      (N1.fixedAt (n1InverseRow lane) ⟨6, by decide⟩).val =
        inverseAddress 1 lane ∧
      0 < (N1.fixedAt (n1InverseRow lane) ⟨7, by decide⟩).val) := by
  decide

private theorem n8_fixed_pins :
    (N8.fixedAt ⟨2, by decide⟩ ⟨6, by decide⟩).val = 22 ∧
    0 < (N8.fixedAt ⟨2, by decide⟩ ⟨7, by decide⟩).val ∧
    (N8.fixedAt ⟨26, by decide⟩ ⟨6, by decide⟩).val = 102 ∧
    0 < (N8.fixedAt ⟨26, by decide⟩ ⟨7, by decide⟩).val ∧
    (N8.fixedAt ⟨36, by decide⟩ ⟨6, by decide⟩).val = 0 ∧
    0 < (N8.fixedAt ⟨36, by decide⟩ ⟨7, by decide⟩).val ∧
    (∀ lane : Fin 4,
      (N8.fixedAt (n8UnitRow lane) ⟨6, by decide⟩).val =
        unitAddress lane ∧
      0 < (N8.fixedAt (n8UnitRow lane) ⟨7, by decide⟩).val) ∧
    (∀ lane : Fin 4, lane.val ≠ 0 →
      (N8.fixedAt (n8InverseRow lane) ⟨6, by decide⟩).val =
        inverseAddress 8 lane ∧
      0 < (N8.fixedAt (n8InverseRow lane) ⟨7, by decide⟩).val) := by
  decide

private theorem n1_valueAt (template : Boundary 1) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c) (initial : State)
    (i : Fin 512) (address : Nat) (value : Quad)
    (hposition : (N1.fixedAt i ⟨6, by decide⟩).val = address ∧
      0 < (N1.fixedAt i ⟨7, by decide⟩).val)
    (hmain : (row trace i).output = value) :
    ValueAt (n1PinnedBoundary template trace hfixed initial)
      address value := by
  apply valueAt_of_decoded_output
    (n1PinnedBoundary template trace hfixed initial) trace
    (pinnedBoundary_rows (by decide : 1 ≤ 8) template trace
      (n1_trace_bounds trace hfixed) initial) i address value
  · change (trace.fixed i ⟨6, by decide⟩).val = address
    rw [hfixed i ⟨6, by decide⟩]
    exact hposition.1
  · change 0 < (trace.fixed i ⟨7, by decide⟩).val
    rw [hfixed i ⟨7, by decide⟩]
    exact hposition.2
  · exact hmain

private theorem n8_valueAt (template : Boundary 8) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c) (initial : State)
    (i : Fin 512) (address : Nat) (value : Quad)
    (hposition : (N8.fixedAt i ⟨6, by decide⟩).val = address ∧
      0 < (N8.fixedAt i ⟨7, by decide⟩).val)
    (hmain : (row trace i).output = value) :
    ValueAt (n8PinnedBoundary template trace hfixed initial)
      address value := by
  apply valueAt_of_decoded_output
    (n8PinnedBoundary template trace hfixed initial) trace
    (pinnedBoundary_rows (by decide : 8 ≤ 8) template trace
      (n8_trace_bounds trace hfixed) initial) i address value
  · change (trace.fixed i ⟨6, by decide⟩).val = address
    rw [hfixed i ⟨6, by decide⟩]
    exact hposition.1
  · change 0 < (trace.fixed i ⟨7, by decide⟩).val
    rw [hfixed i ⟨7, by decide⟩]
    exact hposition.2
  · exact hmain

/-- Replaces ten abstract `ValueAt` assumptions by ten exact decoded main
output pins at kernel-checked positive producer positions. -/
theorem n1_local_schedule_of_main_pins (template : Boundary 1)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (initial : State)
    (rows : ∀ call,
      Fin ((n1PinnedBoundary template trace hfixed initial).rounds call) →
        NativeRow)
    (hbaseline : template.baselineYields = [])
    (pins : N1MainPins trace initial
      ((n1PinnedBoundary template trace hfixed initial).finish
        ⟨1 - 1, by omega⟩)) :
    LocalPublicSchedule (by decide : 1 ≤ 8) (by decide : 0 < 1)
      (n1PinnedBoundary template trace hfixed initial) rows initial := by
  obtain ⟨hpi, hpim, hpf, hpfm, hz, hzm, hu, hi⟩ := n1_fixed_pins
  exact n1_pinned_local_schedule template trace hfixed initial rows hbaseline
    (n1_valueAt template trace hfixed initial ⟨2, by decide⟩ 22
      (packState initial) ⟨hpi, hpim⟩ pins.packedInitial)
    (n1_valueAt template trace hfixed initial ⟨5, by decide⟩ 32
      (packState ((n1PinnedBoundary template trace hfixed initial).finish
        ⟨1 - 1, by omega⟩)) ⟨hpf, hpfm⟩ pins.packedFinal)
    (n1_valueAt template trace hfixed initial ⟨15, by decide⟩ 0
      (base 0) ⟨hz, hzm⟩ pins.zero)
    (fun lane => n1_valueAt template trace hfixed initial
      (n1UnitRow lane) (unitAddress lane) (unit lane)
      (hu lane) (pins.unit lane))
    (fun lane hne => n1_valueAt template trace hfixed initial
      (n1InverseRow lane) (inverseAddress 1 lane) (unitInverse lane)
      (hi lane hne) (pins.inverse lane hne))

/-- N8 counterpart with the final packed endpoint at address 102. -/
theorem n8_local_schedule_of_main_pins (template : Boundary 8)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (initial : State)
    (rows : ∀ call,
      Fin ((n8PinnedBoundary template trace hfixed initial).rounds call) →
        NativeRow)
    (hbaseline : template.baselineYields = [])
    (pins : N8MainPins trace initial
      ((n8PinnedBoundary template trace hfixed initial).finish
        ⟨8 - 1, by omega⟩)) :
    LocalPublicSchedule (by decide : 8 ≤ 8) (by decide : 0 < 8)
      (n8PinnedBoundary template trace hfixed initial) rows initial := by
  obtain ⟨hpi, hpim, hpf, hpfm, hz, hzm, hu, hi⟩ := n8_fixed_pins
  exact n8_pinned_local_schedule template trace hfixed initial rows hbaseline
    (n8_valueAt template trace hfixed initial ⟨2, by decide⟩ 22
      (packState initial) ⟨hpi, hpim⟩ pins.packedInitial)
    (n8_valueAt template trace hfixed initial ⟨26, by decide⟩ 102
      (packState ((n8PinnedBoundary template trace hfixed initial).finish
        ⟨8 - 1, by omega⟩)) ⟨hpf, hpfm⟩ pins.packedFinal)
    (n8_valueAt template trace hfixed initial ⟨36, by decide⟩ 0
      (base 0) ⟨hz, hzm⟩ pins.zero)
    (fun lane => n8_valueAt template trace hfixed initial
      (n8UnitRow lane) (unitAddress lane) (unit lane)
      (hu lane) (pins.unit lane))
    (fun lane hne => n8_valueAt template trace hfixed initial
      (n8InverseRow lane) (inverseAddress 8 lane) (unitInverse lane)
      (hi lane hne) (pins.inverse lane hne))

private theorem n1_fixed_weight_sum :
    (List.ofFn (fun i : Fin 512 =>
      (N1.fixedAt i ⟨7, by decide⟩).val)).sum = 1041 := by
  decide

private theorem n8_fixed_weight_sum :
    (List.ofFn (fun i : Fin 512 =>
      (N8.fixedAt i ⟨7, by decide⟩).val)).sum = 1097 := by
  decide

/-- The entire source-shape size/weight certificate follows from the pinned
fixed export and trace-owned row construction. Only the absence of extra
baseline events still comes from the source roster. -/
theorem n1_pinned_source_shape (template : Boundary 1) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c) (initial : State)
    (huses : template.baselineUses = [])
    (hyields : template.baselineYields = []) :
    SourceShape (n1PinnedBoundary template trace hfixed initial) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (canonicalRows trace (n1_trace_bounds trace hfixed)).length = 512
    simp only [canonicalRows, List.length_ofFn]
  · have hweights :
        ((n1PinnedBoundary template trace hfixed initial).rows.map
          CanonicalRow.multiplicity) =
        List.ofFn (fun i : Fin 512 =>
          (N1.fixedAt i ⟨7, by decide⟩).val) := by
      simp only [n1PinnedBoundary, pinnedBoundary, canonicalRows,
        List.map_ofFn]
      congr 1
      funext i
      exact congrArg ZMod.val (hfixed i ⟨7, by decide⟩)
    rw [hweights, n1_fixed_weight_sum]
  · simpa [n1PinnedBoundary, pinnedBoundary] using huses
  · simpa [n1PinnedBoundary, pinnedBoundary] using hyields
  · intro call; rfl

theorem n8_pinned_source_shape (template : Boundary 8) (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c) (initial : State)
    (huses : template.baselineUses = [])
    (hyields : template.baselineYields = []) :
    SourceShape (n8PinnedBoundary template trace hfixed initial) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (canonicalRows trace (n8_trace_bounds trace hfixed)).length = 512
    simp only [canonicalRows, List.length_ofFn]
  · have hweights :
        ((n8PinnedBoundary template trace hfixed initial).rows.map
          CanonicalRow.multiplicity) =
        List.ofFn (fun i : Fin 512 =>
          (N8.fixedAt i ⟨7, by decide⟩).val) := by
      simp only [n8PinnedBoundary, pinnedBoundary, canonicalRows,
        List.map_ofFn]
      congr 1
      funext i
      exact congrArg ZMod.val (hfixed i ⟨7, by decide⟩)
    rw [hweights, n8_fixed_weight_sum]
  · simpa [n8PinnedBoundary, pinnedBoundary] using huses
  · simpa [n8PinnedBoundary, pinnedBoundary] using hyields
  · intro call; rfl

end S31.Gadgets.Air.SourceMixedPinnedMainCells
