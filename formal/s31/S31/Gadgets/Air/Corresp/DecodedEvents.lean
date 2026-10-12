import S31.Gadgets.Air.SourceMixedPinnedMainCells
import S31.Gadgets.Air.SourceMixedRawEventAlignment

/-!
Field-level correspondence for one decoded mixed Gate trace and its physical
chip/bridge component rows. The global Gate event permutations are consequences
of these cell identities and empty source baseline lists; they are not separate
premises. The exact decoded trace and component-cell identities are assumptions
about committed columns, not consequences of succinct proof acceptance.
-/

namespace S31.Gadgets.Air.Corresp.DecodedEvents

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.IndexedManyChipPath
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedPoleClosure
open S31.Gadgets.Air.SourceMixedBridgePoleClosure
open S31.Gadgets.Air.SourceMixedRawTraceClosure
open S31.Gadgets.Air.SourceMixedRawEventAlignment
open S31.Gadgets.Air.SourceMixedDecodedBoundary
open S31.Gadgets.Air.SourceMixedPinnedMainCells
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.GeneratedMixedFixedRows

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- One physical chip row means the same row, step and four M31 words as the
source-side native row. A sixteen-row count and call tag are explicit. -/
structure ChipCells {N : Nat} (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    {alpha z : GateSecure}
    (chip : Fin N → ChipRows 8 (by decide) alpha z) : Prop where
  rounds : ∀ call, boundary.rounds call = 16
  call : ∀ call, (chip call).call = nativeCallId call
  step : ∀ call (row : Fin 16),
    (chip call).step row =
      (rows call ⟨row.val, by rw [rounds call]; exact row.isLt⟩).step
  input : ∀ call (row : Fin 16),
    (chip call).input row =
      (rows call ⟨row.val, by rw [rounds call]; exact row.isLt⟩).input
  output : ∀ call (row : Fin 16),
    (chip call).output row =
      (rows call ⟨row.val, by rw [rounds call]; exact row.isLt⟩).output

/-- The bridge reads the source's eight addresses and words at its native
anchor; it also carries the verifier-selected call ID and round count. -/
structure BridgeCells {N : Nat} (boundary : Boundary N)
    {alpha z : GateSecure}
    (bridge : Fin N → RawBridgeRows alpha z) : Prop where
  addresses : ∀ call lane,
    (bridge call).addresses lane =
      ((boundary.addresses call lane).val : F)
  words : ∀ call lane,
    (bridge call).words lane sourceBridgeAnchor =
      boundary.words call lane
  call : ∀ call, (bridge call).call = nativeCallId call
  rounds : ∀ call,
    (bridge call).rounds = (boundary.rounds call : F)

/-- The Gate row map is fixed by the decoded main/fixed rows and the
trace-owned boundary constructor. It need not be postulated independently. -/
theorem gate_rows_of_decoded {N : Nat} (template : Boundary N)
    (trace : Trace 9) (hbound : DeclaredAddressBounds trace)
    {alpha z : GateSecure} (gate : RawGateRows alpha z)
    (hcells : ∀ i : Fin 512, gate.rows i = row trace i) :
    List.ofFn gate.rows =
      (boundaryFromTrace template trace hbound).jointGateSource.gateRows := by
  calc
    List.ofFn gate.rows = nativeRows trace := by
      simpa only [nativeRows] using congrArg List.ofFn (funext hcells)
    _ = (boundaryFromTrace template trace hbound).jointGateSource.gateRows :=
      boundaryFromTrace_rows template trace hbound

/-- Exact N1 fixed columns discharge the address bounds needed to construct
the canonical Gate rows. The only Gate correspondence premise is equality of
all 512 decoded logical rows to the modeled physical Gate rows. -/
theorem n1_gate_rows_of_decoded (template : Boundary 1)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (initial : State) {alpha z : GateSecure}
    (gate : RawGateRows alpha z)
    (hcells : ∀ i : Fin 512, gate.rows i = row trace i) :
    List.ofFn gate.rows =
      (n1PinnedBoundary template trace hfixed initial).jointGateSource.gateRows := by
  calc
    List.ofFn gate.rows = nativeRows trace := by
      simpa only [nativeRows] using congrArg List.ofFn (funext hcells)
    _ = (n1PinnedBoundary template trace hfixed initial).jointGateSource.gateRows := by
      simpa only [n1PinnedBoundary] using
        pinnedBoundary_rows (by decide : 1 ≤ 8) template trace
          (n1_trace_bounds trace hfixed) initial

/-- N8 counterpart: exact fixed export plus decoded row cells determine the
entire Gate roster, including padding and multiplicities. -/
theorem n8_gate_rows_of_decoded (template : Boundary 8)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (initial : State) {alpha z : GateSecure}
    (gate : RawGateRows alpha z)
    (hcells : ∀ i : Fin 512, gate.rows i = row trace i) :
    List.ofFn gate.rows =
      (n8PinnedBoundary template trace hfixed initial).jointGateSource.gateRows := by
  calc
    List.ofFn gate.rows = nativeRows trace := by
      simpa only [nativeRows] using congrArg List.ofFn (funext hcells)
    _ = (n8PinnedBoundary template trace hfixed initial).jointGateSource.gateRows := by
      simpa only [n8PinnedBoundary] using
        pinnedBoundary_rows (by decide : 8 ≤ 8) template trace
          (n8_trace_bounds trace hfixed) initial

private theorem bridge_gate_tuple_of_cells {N : Nat}
    (boundary : Boundary N) {alpha z : GateSecure}
    (bridge : Fin N → RawBridgeRows alpha z)
    (cells : BridgeCells boundary bridge)
    (call : Fin N) (lane : Fin 8) :
    sourceBridgeGateTuple (bridge call).addresses (bridge call).words
      lane sourceBridgeAnchor =
    embedGateEvent ((boundary.addresses call lane).val,
      base (boundary.words call lane)) := by
  have hnative := boundary.bridgeGate_native_tuple call lane sourceBridgeAnchor
  unfold sourceBridgeGateTuple
  rw [cells.addresses call lane, cells.words call lane]
  simpa only [sourceBridgeGateTuple] using hnative.symm

/-- Eight address/word cells at the bridge anchor determine the exact
ordered Gate read list. This preserves repeated addresses as occurrences. -/
theorem BridgeCells.gate_events {N : Nat}
    (boundary : Boundary N) {alpha z : GateSecure}
    (bridge : Fin N → RawBridgeRows alpha z)
    (cells : BridgeCells boundary bridge) (call : Fin N) :
    (bridge call).gateEvents =
      ((boundary.callBridgeGates call).map CanonicalEvent.toGate).map
        embedGateEvent := by
  have hsource :
      sourceBridgeGateEvents (bridge call).addresses (bridge call).words =
        List.ofFn (fun lane : Fin 8 =>
          sourceBridgeGateTuple (bridge call).addresses (bridge call).words
            lane sourceBridgeAnchor) := by
    rfl
  rw [RawBridgeRows.gateEvents, hsource]
  simp only [Boundary.callBridgeGates, List.map_ofFn]
  change List.ofFn (fun lane : Fin 8 =>
    sourceBridgeGateTuple (bridge call).addresses (bridge call).words lane
      sourceBridgeAnchor) =
    List.ofFn (fun lane : Fin 8 =>
      embedGateEvent ((boundary.addresses call lane).val,
        base (boundary.words call lane)))
  exact congrArg List.ofFn (funext (bridge_gate_tuple_of_cells
    boundary bridge cells call))

/-- The two bridge endpoint event lists follow from its anchor words, call
tag, and fixed round count. -/
theorem BridgeCells.start_events {N : Nat}
    (boundary : Boundary N) {alpha z : GateSecure}
    (bridge : Fin N → RawBridgeRows alpha z)
    (cells : BridgeCells boundary bridge) (call : Fin N) :
    (bridge call).startEvents = [nativeTuple call 0 (boundary.start call)] := by
  have hstate :
      (fun lane : Fin 4 =>
        (bridge call).words (bridgeInputLane lane) sourceBridgeAnchor) =
      boundary.start call := by
    funext lane
    exact cells.words call (bridgeInputLane lane)
  simp only [RawBridgeRows.startEvents, sourceBridgeStartEvents,
    sourceBridgeStartTuple, nativeTuple]
  rw [cells.call call, hstate]

theorem BridgeCells.finish_events {N : Nat}
    (boundary : Boundary N) {alpha z : GateSecure}
    (bridge : Fin N → RawBridgeRows alpha z)
    (cells : BridgeCells boundary bridge) (call : Fin N) :
    (bridge call).finishEvents =
      [nativeTuple call (boundary.rounds call) (boundary.finish call)] := by
  have hstate :
      (fun lane : Fin 4 =>
        (bridge call).words (bridgeOutputLane lane) sourceBridgeAnchor) =
      boundary.finish call := by
    funext lane
    exact cells.words call (bridgeOutputLane lane)
  simp only [RawBridgeRows.finishEvents, sourceBridgeFinishEvents,
    sourceBridgeFinishTuple, nativeTuple]
  rw [cells.call call, cells.rounds call, hstate]

/-- Chip rows supply the input and output event lists one cell at a time;
the equality includes call ID, step and all four state words. -/
private theorem chip_input_list_of_cells {N R : Nat}
    {alpha z : GateSecure} (call : Fin N)
    (chip : ChipRows 8 (by decide) alpha z)
    (rows : Fin R → NativeRow) (hR : R = 16)
    (hcall : chip.call = nativeCallId call)
    (hstep : ∀ row : Fin 16,
      chip.step row =
        (rows ⟨row.val, by rw [hR]; exact row.isLt⟩).step)
    (hinput : ∀ row : Fin 16,
      chip.input row =
        (rows ⟨row.val, by rw [hR]; exact row.isLt⟩).input) :
    chip.inputEvents = List.ofFn (fun row : Fin R =>
      nativeTuple call (rows row).step (rows row).input) := by
  subst R
  simp only [ChipRows.inputEvents, nativeTuple]
  congr 1
  funext row
  change chipTuple7 chip.call (chip.step row) (chip.input row) =
    chipTuple7 (nativeCallId call) (rows row).step (rows row).input
  rw [hcall, hstep row, hinput row]

theorem ChipCells.input_events {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    {alpha z : GateSecure}
    (chip : Fin N → ChipRows 8 (by decide) alpha z)
    (cells : ChipCells boundary rows chip) (call : Fin N) :
    (chip call).inputEvents =
      List.ofFn (fun row : Fin (boundary.rounds call) =>
        nativeTuple call (rows call row).step (rows call row).input) := by
  exact chip_input_list_of_cells call (chip call) (rows call)
    (cells.rounds call) (cells.call call) (cells.step call) (cells.input call)

private theorem chip_output_list_of_cells {N R : Nat}
    {alpha z : GateSecure} (call : Fin N)
    (chip : ChipRows 8 (by decide) alpha z)
    (rows : Fin R → NativeRow) (hR : R = 16)
    (hcall : chip.call = nativeCallId call)
    (hstep : ∀ row : Fin 16,
      chip.step row =
        (rows ⟨row.val, by rw [hR]; exact row.isLt⟩).step)
    (houtput : ∀ row : Fin 16,
      chip.output row =
        (rows ⟨row.val, by rw [hR]; exact row.isLt⟩).output) :
    chip.outputEvents = List.ofFn (fun row : Fin R =>
      nativeTuple call ((rows row).step + 1) (rows row).output) := by
  subst R
  simp only [ChipRows.outputEvents, nativeTuple]
  congr 1
  funext row
  change chipTuple7 chip.call (chip.step row + 1) (chip.output row) =
    chipTuple7 (nativeCallId call) ((rows row).step + 1) (rows row).output
  rw [hcall, hstep row, houtput row]

theorem ChipCells.output_events {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    {alpha z : GateSecure}
    (chip : Fin N → ChipRows 8 (by decide) alpha z)
    (cells : ChipCells boundary rows chip) (call : Fin N) :
    (chip call).outputEvents =
      List.ofFn (fun row : Fin (boundary.rounds call) =>
        nativeTuple call ((rows call row).step + 1) (rows call row).output) := by
  exact chip_output_list_of_cells call (chip call) (rows call)
    (cells.rounds call) (cells.call call) (cells.step call) (cells.output call)

/-- All five local event equalities are derived from typed physical fields.
No event-list identity is postulated separately. -/
def physicalProjection {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (alpha z : GateSecure)
    (chip : Fin N → ChipRows 8 (by decide) alpha z)
    (bridge : Fin N → RawBridgeRows alpha z)
    (chipCells : ChipCells boundary rows chip)
    (bridgeCells : BridgeCells boundary bridge) :
    RawEventProjection boundary rows alpha z chip bridge :=
  { bridgeGates := bridgeCells.gate_events boundary bridge
    chipInputs := chipCells.input_events boundary rows chip
    bridgeFinish := bridgeCells.finish_events boundary bridge
    chipOutputs := chipCells.output_events boundary rows chip
    bridgeStart := bridgeCells.start_events boundary bridge }

/-- Build the raw all-row trace contract for the N1 source-pinned boundary.
Decoded Gate cells, physical chip/bridge cells, empty source baseline events,
the public ABI words, and the claimed-sum fold are the only correspondence
inputs. The fixed-row export proves shape and Gate address bounds. -/
def n1_pinned_raw_trace (template : Boundary 1)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N1.fixedAt i c)
    (initial : State)
    (hbaselineUses : template.baselineUses = [])
    (hbaselineYields : template.baselineYields = [])
    (rows : ∀ call,
      Fin ((n1PinnedBoundary template trace hfixed initial).rounds call) →
        NativeRow)
    (alpha z : GateSecure)
    (gate : RawGateRows alpha z)
    (chip : Fin 1 → ChipRows 8 (by decide) alpha z)
    (bridge : Fin 1 → RawBridgeRows alpha z)
    (words : List Quad)
    (gateCells : ∀ i : Fin 512, gate.rows i = row trace i)
    (chipCells : ChipCells
      (n1PinnedBoundary template trace hfixed initial) rows chip)
    (bridgeCells : BridgeCells
      (n1PinnedBoundary template trace hfixed initial) bridge)
    (hwords : words = List.ofFn (fun output : Fin 8 =>
      base ((n1PinnedBoundary template trace hfixed initial).publicOutputs output)))
    (hfold : gate.claim +
      ((List.finRange 1).map (fun call =>
        (chip call).claim + (bridge call).claim)).sum +
      productionReciprocalSum7 (publicOutputYields words) alpha z = 0) :
    RawAuthenticatedMixedTrace
      (n1PinnedBoundary template trace hfixed initial) rows alpha z :=
  let boundary := n1PinnedBoundary template trace hfixed initial
  let projection := physicalProjection boundary rows alpha z chip bridge
    chipCells bridgeCells
  projection.assembleOfShape
    (n1_pinned_source_shape template trace hfixed initial
      hbaselineUses hbaselineYields)
    gate chip bridge words
    (n1_gate_rows_of_decoded template trace hfixed initial gate gateCells)
    hwords hfold

/-- N8 counterpart with the same field-level correspondence contract. -/
def n8_pinned_raw_trace (template : Boundary 8)
    (trace : Trace 9)
    (hfixed : ∀ i : Fin 512, ∀ c : Fin 8,
      trace.fixed i c = N8.fixedAt i c)
    (initial : State)
    (hbaselineUses : template.baselineUses = [])
    (hbaselineYields : template.baselineYields = [])
    (rows : ∀ call,
      Fin ((n8PinnedBoundary template trace hfixed initial).rounds call) →
        NativeRow)
    (alpha z : GateSecure)
    (gate : RawGateRows alpha z)
    (chip : Fin 8 → ChipRows 8 (by decide) alpha z)
    (bridge : Fin 8 → RawBridgeRows alpha z)
    (words : List Quad)
    (gateCells : ∀ i : Fin 512, gate.rows i = row trace i)
    (chipCells : ChipCells
      (n8PinnedBoundary template trace hfixed initial) rows chip)
    (bridgeCells : BridgeCells
      (n8PinnedBoundary template trace hfixed initial) bridge)
    (hwords : words = List.ofFn (fun output : Fin 8 =>
      base ((n8PinnedBoundary template trace hfixed initial).publicOutputs output)))
    (hfold : gate.claim +
      ((List.finRange 8).map (fun call =>
        (chip call).claim + (bridge call).claim)).sum +
      productionReciprocalSum7 (publicOutputYields words) alpha z = 0) :
    RawAuthenticatedMixedTrace
      (n8PinnedBoundary template trace hfixed initial) rows alpha z :=
  let boundary := n8PinnedBoundary template trace hfixed initial
  let projection := physicalProjection boundary rows alpha z chip bridge
    chipCells bridgeCells
  projection.assembleOfShape
    (n8_pinned_source_shape template trace hfixed initial
      hbaselineUses hbaselineYields)
    gate chip bridge words
    (n8_gate_rows_of_decoded template trace hfixed initial gate gateCells)
    hwords hfold

end S31.Gadgets.Air.Corresp.DecodedEvents
