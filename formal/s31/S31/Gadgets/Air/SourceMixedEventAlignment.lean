import S31.Gadgets.Air.SourceMixedAuthenticatedTrace

/-!
Reduce the mixed trace's global event-permutation premises to source-owned
circuit lists and five per-call component projections. The native circuit
lists group all bridge Gate reads before chip rows; the per-call algebra
interleaves them. Exact list equality is therefore the wrong contract.
-/

namespace S31.Gadgets.Air.SourceMixedEventAlignment

open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAuthenticatedTrace
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge

structure EventProjection {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (alpha z : GateSecure)
    (gate : GateRows alpha z)
    (chip : Fin N → ChipRows 8 (by decide) alpha z)
    (bridge : Fin N → BridgeRows alpha z)
    (publicWords : List S31.Gadgets.Packed.Quad) : Prop where
  circuitUses : boundary.jointGateSource.circuitUses =
    (gate.uses ++ publicOutputYields publicWords) ++
      (List.finRange N).flatMap (fun call => (bridge call).gateEvents)
  circuitYields : boundary.jointGateSource.circuitYields = gate.yields
  chipInputs : ∀ call,
    (chip call).inputEvents = List.ofFn (fun row : Fin (boundary.rounds call) =>
      nativeTuple call (rows call row).step (rows call row).input)
  bridgeFinish : ∀ call,
    (bridge call).finishEvents =
      [nativeTuple call (boundary.rounds call) (boundary.finish call)]
  chipOutputs : ∀ call,
    (chip call).outputEvents = List.ofFn (fun row : Fin (boundary.rounds call) =>
      nativeTuple call ((rows call row).step + 1) (rows call row).output)
  bridgeStart : ∀ call,
    (bridge call).startEvents = [nativeTuple call 0 (boundary.start call)]

/-- The per-call positive order is Gate reads, chip inputs, then terminal
endpoint. Native `callUses` puts the terminal endpoint before chip inputs;
both have exactly the same occurrences. -/
private theorem call_positive_perm {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    {gate : GateRows alpha z}
    {chip : Fin N → ChipRows 8 (by decide) alpha z}
    {bridge : Fin N → BridgeRows alpha z}
    {words : List S31.Gadgets.Packed.Quad}
    (projection : EventProjection boundary rows alpha z gate chip bridge words)
    (call : Fin N) :
    ((bridge call).gateEvents ++ (chip call).inputEvents ++
      (bridge call).finishEvents).Perm
      ((bridge call).gateEvents ++ callUses rows boundary.finish call) := by
  rw [projection.chipInputs call, projection.bridgeFinish call]
  simp only [callUses]
  have hswap := (List.perm_append_comm :
    ((List.ofFn (fun row : Fin (boundary.rounds call) =>
      nativeTuple call (rows call row).step (rows call row).input)) ++
      [nativeTuple call (boundary.rounds call) (boundary.finish call)]).Perm
    ([nativeTuple call (boundary.rounds call) (boundary.finish call)] ++
      List.ofFn (fun row : Fin (boundary.rounds call) =>
        nativeTuple call (rows call row).step (rows call row).input)))
  simpa only [List.append_assoc] using
    hswap.append_left (bridge call).gateEvents

theorem EventProjection.positiveAligned {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    {gate : GateRows alpha z}
    {chip : Fin N → ChipRows 8 (by decide) alpha z}
    {bridge : Fin N → BridgeRows alpha z}
    {words : List S31.Gadgets.Packed.Quad}
    (projection : EventProjection boundary rows alpha z gate chip bridge words) :
    ((gate.uses ++ publicOutputYields words) ++
      (List.finRange N).flatMap (fun call =>
        (bridge call).gateEvents ++ (chip call).inputEvents ++
          (bridge call).finishEvents)).Perm
      (boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) := by
  let calls := List.finRange N
  let gateEvents := fun call : Fin N => (bridge call).gateEvents
  let rest := callUses rows boundary.finish
  have hlocal :
      (calls.flatMap (fun call =>
        gateEvents call ++ (chip call).inputEvents ++
          (bridge call).finishEvents)).Perm
      (calls.flatMap (fun call => gateEvents call ++ rest call)) := by
    apply List.Perm.flatMap_left
    intro call _
    exact call_positive_perm projection call
  have hsplit :
      (calls.flatMap (fun call => gateEvents call ++ rest call)).Perm
      (calls.flatMap gateEvents ++ calls.flatMap rest) :=
    (List.flatMap_append_perm calls gateEvents rest).symm
  rw [projection.circuitUses]
  simp only [jointUses]
  simpa only [List.append_assoc, calls, gateEvents, rest] using
    (hlocal.trans hsplit).append_left
      (gate.uses ++ publicOutputYields words)

private theorem call_negative_perm {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    {gate : GateRows alpha z}
    {chip : Fin N → ChipRows 8 (by decide) alpha z}
    {bridge : Fin N → BridgeRows alpha z}
    {words : List S31.Gadgets.Packed.Quad}
    (projection : EventProjection boundary rows alpha z gate chip bridge words)
    (call : Fin N) :
    ((chip call).outputEvents ++ (bridge call).startEvents).Perm
      (callYields rows boundary.start call) := by
  rw [projection.chipOutputs call, projection.bridgeStart call]
  simp only [callYields]
  exact List.perm_append_comm

theorem EventProjection.negativeAligned {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    {gate : GateRows alpha z}
    {chip : Fin N → ChipRows 8 (by decide) alpha z}
    {bridge : Fin N → BridgeRows alpha z}
    {words : List S31.Gadgets.Packed.Quad}
    (projection : EventProjection boundary rows alpha z gate chip bridge words) :
    (gate.yields ++ (List.finRange N).flatMap (fun call =>
      (chip call).outputEvents ++ (bridge call).startEvents)).Perm
      (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start) := by
  rw [projection.circuitYields]
  simp only [jointYields]
  exact List.Perm.append_left _
    (List.Perm.flatMap_left _ (fun call _ => call_negative_perm projection call))

/-- Construct the complete trace contract from source/component projections.
There is no additional global ordered-list equality premise. The remaining
fields still require authenticated arithmetic/interaction rows, exact public
words and the native claim fold. -/
def EventProjection.assemble {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (gate : GateRows alpha z)
    (chip : Fin N → ChipRows 8 (by decide) alpha z)
    (bridge : Fin N → BridgeRows alpha z)
    (words : List S31.Gadgets.Packed.Quad)
    (projection : EventProjection boundary rows alpha z gate chip bridge words)
    (hrows : List.ofFn gate.rows = boundary.jointGateSource.gateRows)
    (hwords : words =
      List.ofFn (fun output : Fin 8 =>
        S31.Gadgets.Packed.base (boundary.publicOutputs output)))
    (hfold : gate.claim +
      ((List.finRange N).map (fun call =>
        (chip call).claim + (bridge call).claim)).sum +
      productionReciprocalSum7 (publicOutputYields words) alpha z = 0) :
    AuthenticatedMixedTrace boundary rows alpha z :=
  { gate := gate
    chip := chip
    bridge := bridge
    gateRowsEq := hrows
    publicWords := words
    publicWordsEq := hwords
    positiveAligned := projection.positiveAligned
    negativeAligned := projection.negativeAligned
    claimFoldZero := hfold }

end S31.Gadgets.Air.SourceMixedEventAlignment
