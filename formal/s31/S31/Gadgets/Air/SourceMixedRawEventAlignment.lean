import S31.Gadgets.Air.SourceMixedRawTraceClosure

/-!
Source-shaped event projection for raw Gate and bridge rows. The five per-call
equalities identify committed component tuples with the ideal source tuples;
the circuit lists then follow from the Gate row roster and source-owned
external uses. No nonzero denominator or checked trace is constructed here.
-/

namespace S31.Gadgets.Air.SourceMixedRawEventAlignment

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedLookupBound
open S31.Gadgets.Air.SourceMixedFalseClaimBound
open S31.Gadgets.Air.SourceMixedPoleClosure
open S31.Gadgets.Air.SourceMixedBridgePoleClosure
open S31.Gadgets.Air.SourceMixedRawTraceClosure
open S31.Gadgets.Air.SourceMixedEventAlignment
open S31.Gadgets.Air.SourceMixedScheduledPublicPath

/-- The five local component projections. The raw rows remain independent of
the selected challenge except for their AIR residual fields. -/
structure RawEventProjection {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (alpha z : GateSecure)
    (chip : Fin N → ChipRows 8 (by decide) alpha z)
    (bridge : Fin N → RawBridgeRows alpha z) : Prop where
  bridgeGates : ∀ call,
    (bridge call).gateEvents =
      ((boundary.callBridgeGates call).map CanonicalEvent.toGate).map
        embedGateEvent
  chipInputs : ∀ call,
    (chip call).inputEvents =
      List.ofFn (fun row : Fin (boundary.rounds call) =>
        nativeTuple call (rows call row).step (rows call row).input)
  bridgeFinish : ∀ call,
    (bridge call).finishEvents =
      [nativeTuple call (boundary.rounds call) (boundary.finish call)]
  chipOutputs : ∀ call,
    (chip call).outputEvents =
      List.ofFn (fun row : Fin (boundary.rounds call) =>
        nativeTuple call ((rows call row).step + 1) (rows call row).output)
  bridgeStart : ∀ call,
    (bridge call).startEvents = [nativeTuple call 0 (boundary.start call)]

private theorem circuit_yields_of_raw_rows {N : Nat}
    (boundary : Boundary N) {alpha z : GateSecure}
    (gate : RawGateRows alpha z)
    (hrows : List.ofFn gate.rows = boundary.jointGateSource.gateRows)
    (hbaseline : boundary.baselineYields = []) :
    boundary.jointGateSource.circuitYields = rawGateYields gate := by
  calc
    boundary.jointGateSource.circuitYields =
        (allYields boundary.jointGateSource.gateRows []).map
          embedGateEvent := by
            simp [GateSource.circuitYields,
              GateSource.gateExternalYields, Boundary.jointGateSource,
              hbaseline]
    _ = rawGateYields gate := by
      rw [← hrows]
      rfl

private theorem circuit_uses_of_raw_rows {N : Nat}
    (boundary : Boundary N) {alpha z : GateSecure}
    (gate : RawGateRows alpha z)
    (bridge : Fin N → RawBridgeRows alpha z)
    (words : List Quad)
    (hrows : List.ofFn gate.rows = boundary.jointGateSource.gateRows)
    (hbaseline : boundary.baselineUses = [])
    (hwords : words = List.ofFn (fun output : Fin 8 =>
      base (boundary.publicOutputs output)))
    (hbridge : ∀ call,
      (bridge call).gateEvents =
        ((boundary.callBridgeGates call).map CanonicalEvent.toGate).map
          embedGateEvent) :
    boundary.jointGateSource.circuitUses =
      (rawGateUses gate ++ publicOutputYields words) ++
        (List.finRange N).flatMap (fun call => (bridge call).gateEvents) := by
  have hpublic := boundary.publicFeeder_native_events
  rw [← hwords] at hpublic
  have hbridgeList :
      ((boundary.bridgeGates.map CanonicalEvent.toGate).map
        embedGateEvent) =
      (List.finRange N).flatMap (fun call => (bridge call).gateEvents) := by
    simp only [Boundary.bridgeGates, List.map_flatMap]
    exact List.flatMap_congr (fun call _ => (hbridge call).symm)
  calc
    boundary.jointGateSource.circuitUses =
        rawGateUses gate ++
          ((boundary.publicFeeder.map CanonicalEvent.toGate).map
            embedGateEvent) ++
          ((boundary.bridgeGates.map CanonicalEvent.toGate).map
            embedGateEvent) := by
              change (allUses boundary.jointGateSource.gateRows
                boundary.jointGateSource.gateExternalUses).map
                  embedGateEvent = _
              rw [← hrows]
              have hext : boundary.jointGateSource.gateExternalUses =
                  (boundary.publicFeeder ++ boundary.bridgeGates).map
                    CanonicalEvent.toGate := by
                simp [GateSource.gateExternalUses,
                  Boundary.jointGateSource, hbaseline]
              rw [hext]
              simp only [allUses, rawGateUses, List.append_nil,
                List.map_append, List.append_assoc]
    _ = (rawGateUses gate ++ publicOutputYields words) ++
          (List.finRange N).flatMap fun call =>
            (bridge call).gateEvents := by
              rw [hpublic, hbridgeList]

private theorem call_positive_perm {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    {chip : Fin N → ChipRows 8 (by decide) alpha z}
    {bridge : Fin N → RawBridgeRows alpha z}
    (projection : RawEventProjection boundary rows alpha z chip bridge)
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

/-- Source roster and five local projections imply the raw positive event
permutation, without constructing a checked bridge. -/
theorem RawEventProjection.positiveAligned {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (gate : RawGateRows alpha z)
    {chip : Fin N → ChipRows 8 (by decide) alpha z}
    {bridge : Fin N → RawBridgeRows alpha z}
    (words : List Quad)
    (projection : RawEventProjection boundary rows alpha z chip bridge)
    (hrows : List.ofFn gate.rows = boundary.jointGateSource.gateRows)
    (hbaseline : boundary.baselineUses = [])
    (hwords : words = List.ofFn (fun output : Fin 8 =>
      base (boundary.publicOutputs output))) :
    ((rawGateUses gate ++ publicOutputYields words) ++
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
  rw [circuit_uses_of_raw_rows boundary gate bridge words hrows
    hbaseline hwords projection.bridgeGates]
  simp only [jointUses]
  simpa only [List.append_assoc, calls, gateEvents, rest] using
    (hlocal.trans hsplit).append_left
      (rawGateUses gate ++ publicOutputYields words)

private theorem call_negative_perm {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    {chip : Fin N → ChipRows 8 (by decide) alpha z}
    {bridge : Fin N → RawBridgeRows alpha z}
    (projection : RawEventProjection boundary rows alpha z chip bridge)
    (call : Fin N) :
    ((chip call).outputEvents ++ (bridge call).startEvents).Perm
      (callYields rows boundary.start call) := by
  rw [projection.chipOutputs call, projection.bridgeStart call]
  simp only [callYields]
  exact List.perm_append_comm

/-- Source roster and local projections imply the raw negative event
permutation. -/
theorem RawEventProjection.negativeAligned {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (gate : RawGateRows alpha z)
    {chip : Fin N → ChipRows 8 (by decide) alpha z}
    {bridge : Fin N → RawBridgeRows alpha z}
    (projection : RawEventProjection boundary rows alpha z chip bridge)
    (hrows : List.ofFn gate.rows = boundary.jointGateSource.gateRows)
    (hbaseline : boundary.baselineYields = []) :
    (rawGateYields gate ++ (List.finRange N).flatMap (fun call =>
      (chip call).outputEvents ++ (bridge call).startEvents)).Perm
      (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start) := by
  rw [circuit_yields_of_raw_rows boundary gate hrows hbaseline]
  simp only [jointYields]
  exact List.Perm.append_left _
    (List.Perm.flatMap_left _ (fun call _ => call_negative_perm projection call))

/-- Assemble raw AIR rows and source-local event projections. No global
event-permutation premise or nonpole challenge is required. -/
def RawEventProjection.assemble {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (gate : RawGateRows alpha z)
    (chip : Fin N → ChipRows 8 (by decide) alpha z)
    (bridge : Fin N → RawBridgeRows alpha z)
    (words : List Quad)
    (projection : RawEventProjection boundary rows alpha z chip bridge)
    (hrows : List.ofFn gate.rows = boundary.jointGateSource.gateRows)
    (hbaselineUses : boundary.baselineUses = [])
    (hbaselineYields : boundary.baselineYields = [])
    (hwords : words = List.ofFn (fun output : Fin 8 =>
      base (boundary.publicOutputs output)))
    (hfold : gate.claim +
      ((List.finRange N).map (fun call =>
        (chip call).claim + (bridge call).claim)).sum +
      productionReciprocalSum7 (publicOutputYields words) alpha z = 0) :
    RawAuthenticatedMixedTrace boundary rows alpha z :=
  { gate := gate
    chip := chip
    bridge := bridge
    gateRowsEq := hrows
    publicWords := words
    publicWordsEq := hwords
    positiveAligned := RawEventProjection.positiveAligned gate words projection
      hrows hbaselineUses hwords
    negativeAligned := RawEventProjection.negativeAligned gate projection
      hrows hbaselineYields
    claimFoldZero := hfold }

/-- The admitted source shape supplies both empty-baseline facts needed by
`assemble`; only the five per-call tuple identifications remain local. -/
def RawEventProjection.assembleOfShape {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (hshape : SourceShape boundary)
    (gate : RawGateRows alpha z)
    (chip : Fin N → ChipRows 8 (by decide) alpha z)
    (bridge : Fin N → RawBridgeRows alpha z)
    (words : List Quad)
    (projection : RawEventProjection boundary rows alpha z chip bridge)
    (hrows : List.ofFn gate.rows = boundary.jointGateSource.gateRows)
    (hwords : words = List.ofFn (fun output : Fin 8 =>
      base (boundary.publicOutputs output)))
    (hfold : gate.claim +
      ((List.finRange N).map (fun call =>
        (chip call).claim + (bridge call).claim)).sum +
      productionReciprocalSum7 (publicOutputYields words) alpha z = 0) :
    RawAuthenticatedMixedTrace boundary rows alpha z :=
  RawEventProjection.assemble gate chip bridge words projection hrows
    hshape.baselineUses hshape.baselineYields hwords hfold

/-- The same five local tuple identifications also supply the checked
`EventProjection` after the raw rows are converted outside the pole set.
This removes a second, independently trusted event projection from the
scheduled false-claim theorem. -/
def RawEventProjection.toCheckedProjection {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (hshape : SourceShape boundary)
    (raw : RawAuthenticatedMixedTrace boundary rows alpha z)
    (projection : RawEventProjection boundary rows alpha z
      raw.chip raw.bridge)
    (hgood : (alpha, z) ∉
      mixedErrorPairs boundary rows raw.gate.rows) :
    EventProjection boundary rows alpha z
      (raw.toChecked hgood).gate
      (raw.toChecked hgood).chip
      (raw.toChecked hgood).bridge
      (raw.toChecked hgood).publicWords := by
  apply EventProjection.ofSourceRows boundary rows alpha z
    (raw.toChecked hgood).gate
    (raw.toChecked hgood).chip
    (raw.toChecked hgood).bridge
    (raw.toChecked hgood).publicWords
  · exact raw.gateRowsEq
  · exact hshape.baselineUses
  · exact hshape.baselineYields
  · exact raw.publicWordsEq
  · exact projection.bridgeGates
  · exact projection.chipInputs
  · exact projection.bridgeFinish
  · exact projection.chipOutputs
  · exact projection.bridgeStart

/-- A false public word is exceptional from raw Gate/bridge AIR rows, checked
chip rows, a source schedule, and the five local tuple projections. -/
theorem raw_scheduled_false_word_from_local_events_is_exceptional {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (hshape : SourceShape boundary)
    (schedule : LocalPublicSchedule hN hpositive boundary rows initial)
    (product : Bool) (lane : Fin 4)
    (hfalse : FalsePublicWord boundary initial product lane)
    (alpha z : GateSecure)
    (raw : RawAuthenticatedMixedTrace boundary rows alpha z)
    (projection : RawEventProjection boundary rows alpha z
      raw.chip raw.bridge)
    (hconstant : ∀ call,
      (raw.chip call).constant = boundary.constants call) :
    (alpha, z) ∈ mixedErrorPairs boundary rows raw.gate.rows ∧
      (mixedErrorPairs boundary rows raw.gate.rows).card ≤
        36494846 * Fintype.card GateSecure :=
  raw_scheduled_false_word_is_exceptional hN hpositive boundary rows initial
    hshape schedule product lane hfalse alpha z raw
    (fun hgood => projection.toCheckedProjection hshape raw hgood)
    hconstant

/-- Expose the complete local algebraic certificate: physical Gate and bridge
rows, chip rows, the source row/public mappings, five per-call tuple
equalities, and the native claimed-sum fold. Global event permutations and
the checked trace are derived internally. -/
theorem raw_rows_local_projection_false_word_is_exceptional {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (hshape : SourceShape boundary)
    (schedule : LocalPublicSchedule hN hpositive boundary rows initial)
    (product : Bool) (lane : Fin 4)
    (hfalse : FalsePublicWord boundary initial product lane)
    (alpha z : GateSecure)
    (gate : RawGateRows alpha z)
    (chip : Fin N → ChipRows 8 (by decide) alpha z)
    (bridge : Fin N → RawBridgeRows alpha z)
    (words : List Quad)
    (projection : RawEventProjection boundary rows alpha z chip bridge)
    (hrows : List.ofFn gate.rows = boundary.jointGateSource.gateRows)
    (hwords : words = List.ofFn (fun output : Fin 8 =>
      base (boundary.publicOutputs output)))
    (hfold : gate.claim +
      ((List.finRange N).map (fun call =>
        (chip call).claim + (bridge call).claim)).sum +
      productionReciprocalSum7 (publicOutputYields words) alpha z = 0)
    (hconstant : ∀ call,
      (chip call).constant = boundary.constants call) :
    (alpha, z) ∈ mixedErrorPairs boundary rows gate.rows ∧
      (mixedErrorPairs boundary rows gate.rows).card ≤
        36494846 * Fintype.card GateSecure := by
  let raw := projection.assembleOfShape hshape gate chip bridge words
    hrows hwords hfold
  exact raw_scheduled_false_word_from_local_events_is_exceptional
    hN hpositive boundary rows initial hshape schedule product lane hfalse
    alpha z raw projection hconstant

end S31.Gadgets.Air.SourceMixedRawEventAlignment
