import S31.Gadgets.Air.SourceMixedPublicClosure
import S31.Gadgets.Air.PackRows

/-!
The direct mixed compiler's `simd.pack` path. Four scalar bridge words enter
three extension-basis multiplication rows and three addition rows. Exact
Gate balance and producer uniqueness tie the row operands together; local
Qm31 AIR acceptance fixes the packed output. This module establishes the two
packed memberships required by `SourceMixedPublicClosure`, conditional on
compiler row selection and basis-constant memberships.
-/

namespace S31.Gadgets.Air.SourceMixedPackCorrespondence

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateWireMap
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAddressSchedule
open S31.Gadgets.Air.SourceMixedPublicClosure
open S31.Gadgets.Air.SourceMixedChainSemantics
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence

private noncomputable def wire {N : Nat} (boundary : Boundary N) : Nat → Quad :=
  producedWire (produced boundary)

private theorem selected_row_air {N : Nat} (boundary : Boundary N)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (hunique : uniqueProduced (produced boundary))
    (a b out : Nat) (op : Qm31Ops.Op)
    (hrow : AcceptedRow boundary a b out op) :
    accepts (encode op) (wire boundary a) (wire boundary b)
      (wire boundary out) := by
  obtain ⟨row, hmem, h0, h1, hout, hflags, hm, hair⟩ := hrow
  have hgate : row.toGate ∈ boundary.jointGateSource.gateRows :=
    List.mem_map.mpr ⟨row, hmem, rfl⟩
  have hwire := row_accepts_on_wire
    boundary.jointGateSource.gateRows
    boundary.jointGateSource.gateExternalUses
    boundary.jointGateSource.gateExternalYields
    hbalance hunique row.toGate hgate
    (by simpa [CanonicalRow.toGate] using hm)
    (by simpa [CanonicalRow.toGate] using hair)
  simpa [wire, produced, CanonicalRow.toGate, h0, h1, hout,
    hflags] using hwire

private theorem selected_output_produced {N : Nat}
    (boundary : Boundary N) (a b out : Nat) (op : Qm31Ops.Op)
    (hrow : AcceptedRow boundary a b out op) :
    ∃ value, ValueAt boundary out value := by
  obtain ⟨row, hmem, _, _, hout, _, hm, _⟩ := hrow
  refine ⟨row.output, ?_⟩
  unfold ValueAt produced
  have hgate : row.toGate ∈ boundary.jointGateSource.gateRows :=
    List.mem_map.mpr ⟨row, hmem, rfl⟩
  have hyield := row_output_yield boundary.jointGateSource.gateRows
    boundary.jointGateSource.gateExternalYields row.toGate hgate
    (by simpa [CanonicalRow.toGate] using hm)
  simpa [CanonicalRow.toGate, hout] using hyield

private theorem bridge_value {N : Nat} (boundary : Boundary N)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (call : Fin N) (slot : Fin 8) :
    ValueAt boundary (boundary.addresses call slot).val
      (base (boundary.words call slot)) := by
  unfold ValueAt produced
  apply hbalance.mem_iff.mp
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(boundary.addresses call slot,
    base (boundary.words call slot)), ?_, rfl⟩
  unfold Boundary.jointGateSource
  apply List.mem_append_right
  unfold Boundary.bridgeGates
  apply List.mem_flatMap.mpr
  exact ⟨call, List.mem_finRange call,
    List.mem_ofFn.mpr ⟨slot, rfl⟩⟩

/-- The six output addresses are allocated by the compiler. The rows follow
`simd.pack`: basis-j times scalar-j, then the left-associated additions
`scalar0 + term1`, `sum1 + term2`, `sum2 + term3`. No row value is supplied. -/
def PackPath {N : Nat} (boundary : Boundary N)
    (scalarAddress : Fin 4 → Nat) (packedAddress : Nat) : Prop :=
  ∃ (basisAddress : Fin 4 → Nat)
    (termAddress : Fin 4 → Nat) (sum1Address sum2Address : Nat),
    (∀ j : Fin 4, 0 < j.val →
      ValueAt boundary (basisAddress j) (unit j) ∧
      AcceptedRow boundary (basisAddress j) (scalarAddress j)
        (termAddress j) .mul) ∧
    AcceptedRow boundary (scalarAddress ⟨0, by decide⟩)
      (termAddress ⟨1, by decide⟩) sum1Address .add ∧
    AcceptedRow boundary sum1Address (termAddress ⟨2, by decide⟩)
      sum2Address .add ∧
    AcceptedRow boundary sum2Address (termAddress ⟨3, by decide⟩)
      packedAddress .add

/-- Gate balance, producer uniqueness, bridge scalar values, and the six
selected local AIR rows establish the packed tuple at the selected address.
The selected last row's positive multiplicity makes the tuple produced. -/
theorem pack_path_produces_state {N : Nat} (boundary : Boundary N)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (hunique : uniqueProduced (produced boundary))
    (state : State) (scalarAddress : Fin 4 → Nat) (packedAddress : Nat)
    (hscalar : ∀ lane, ValueAt boundary (scalarAddress lane)
      (base (state lane)))
    (hpack : PackPath boundary scalarAddress packedAddress) :
    ValueAt boundary packedAddress (packState state) := by
  obtain ⟨basisAddress, termAddress, sum1Address, sum2Address,
    hterms, hsum1, hsum2, hpacked⟩ := hpack
  have hscalarWire : ∀ lane, wire boundary (scalarAddress lane) =
      base (state lane) := by
    intro lane
    exact producedWire_eq _ hunique _ _ (hscalar lane)
  have hbasisWire : ∀ j : Fin 4, 0 < j.val →
      wire boundary (basisAddress j) = unit j := by
    intro j hj
    exact producedWire_eq _ hunique _ _ (hterms j hj).1
  have htermAir : ∀ j : Fin 4, 0 < j.val →
      accepts (encode .mul) (unit j) (base (state j))
        (wire boundary (termAddress j)) := by
    intro j hj
    have h := selected_row_air boundary hbalance hunique
      (basisAddress j) (scalarAddress j) (termAddress j)
      .mul (hterms j hj).2
    simpa [hbasisWire j hj, hscalarWire j] using h
  have hsum1Air : accepts (encode .add)
      (base (state ⟨0, by decide⟩))
      (wire boundary (termAddress ⟨1, by decide⟩))
      (wire boundary sum1Address) := by
    have h := selected_row_air boundary hbalance hunique
      _ _ _ .add hsum1
    rw [hscalarWire ⟨0, by decide⟩] at h
    exact h
  have hsum2Air : accepts (encode .add)
      (wire boundary sum1Address)
      (wire boundary (termAddress ⟨2, by decide⟩))
      (wire boundary sum2Address) :=
    selected_row_air boundary hbalance hunique _ _ _ .add hsum2
  have hpackedAir : accepts (encode .add)
      (wire boundary sum2Address)
      (wire boundary (termAddress ⟨3, by decide⟩))
      (wire boundary packedAddress) :=
    selected_row_air boundary hbalance hunique _ _ _ .add hpacked
  let source : Fin 4 → S31.M31 := fun lane =>
    S31.Field.fromZMod (state lane)
  have hlocal : S31.Gadgets.Air.PackRows.acceptsPack source
      (wire boundary (termAddress ⟨1, by decide⟩))
      (wire boundary (termAddress ⟨2, by decide⟩))
      (wire boundary (termAddress ⟨3, by decide⟩))
      (wire boundary sum1Address) (wire boundary sum2Address)
      (wire boundary packedAddress) := by
    refine ⟨?_, ?_, ?_, ?_, hsum2Air, hpackedAir⟩
    · simpa [source, S31.Field.to_from] using
        htermAir ⟨1, by decide⟩ (by decide)
    · simpa [source, S31.Field.to_from] using
        htermAir ⟨2, by decide⟩ (by decide)
    · simpa [source, S31.Field.to_from] using
        htermAir ⟨3, by decide⟩ (by decide)
    · simpa [source, S31.Field.to_from] using hsum1Air
  have hwirePacked := S31.Gadgets.Air.PackRows.acceptsPack_sound
    source _ _ _ _ _ _ hlocal
  have hpackState : packM31 source = packState state := by
    simp [packM31, packState, source, S31.Field.to_from]
  rw [hpackState] at hwirePacked
  obtain ⟨value, hvalue⟩ := selected_output_produced boundary
    _ _ _ .add hpacked
  have hvalueWire : wire boundary packedAddress = value :=
    producedWire_eq _ hunique _ _ hvalue
  have hvalueEq : packState state = value :=
    hwirePacked.symm.trans hvalueWire
  rw [← hvalueEq] at hvalue
  exact hvalue

/-- First and last scalar bridge tuples are actual produced Gate events under
the canonical source address schedule. No scalar-value premise is added. -/
theorem bridge_scalar_endpoints {N : Nat} (hN : N ≤ 8)
    (hpositive : 0 < N) (boundary : Boundary N) (initial : State)
    (haddresses : ∀ call slot,
      boundary.addresses call slot = canonicalAddress hN call slot)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (hfirst : boundary.start ⟨0, hpositive⟩ = initial) :
    (∀ lane : Fin 4,
      ValueAt boundary (inputAddress 0 lane.val) (base (initial lane))) ∧
    (∀ lane : Fin 4,
      ValueAt boundary (outputAddress (N - 1) lane.val)
        (base (boundary.finish ⟨N - 1, by omega⟩ lane))) := by
  constructor
  · intro lane
    have h := bridge_value boundary hbalance ⟨0, hpositive⟩
      ⟨lane.val, by omega⟩
    have hinitLane := congrFun hfirst lane
    change boundary.words ⟨0, hpositive⟩
      ⟨lane.val, by omega⟩ = initial lane at hinitLane
    have h' : ValueAt boundary (inputAddress 0 lane.val)
        (base (boundary.words ⟨0, hpositive⟩
          ⟨lane.val, by omega⟩)) := by
      simpa [haddresses ⟨0, hpositive⟩ ⟨lane.val, by omega⟩,
        canonicalAddress, bridgeAddress] using h
    rw [hinitLane] at h'
    exact h'
  · intro lane
    have h := bridge_value boundary hbalance ⟨N - 1, by omega⟩
      ⟨4 + lane.val, by omega⟩
    simpa [haddresses ⟨N - 1, by omega⟩
      ⟨4 + lane.val, by omega⟩, canonicalAddress, bridgeAddress,
      Boundary.finish] using h

/-- The two packed `ValueAt` premises of the public closure follow from
source-shaped scalar bridge events and actual six-row `simd.pack` paths. -/
theorem packed_inputs_from_bridge_and_pack {N : Nat} (hN : N ≤ 8)
    (hpositive : 0 < N) (boundary : Boundary N) (initial : State)
    (haddresses : ∀ call slot,
      boundary.addresses call slot = canonicalAddress hN call slot)
    (hfirst : boundary.start ⟨0, hpositive⟩ = initial)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (hunique : uniqueProduced (produced boundary))
    (hpackInitial : PackPath boundary
      (fun lane => inputAddress 0 lane.val) 22)
    (hpackFinal : PackPath boundary
      (fun lane => outputAddress (N - 1) lane.val) (22 + 10 * N)) :
    ValueAt boundary 22 (packState initial) ∧
      ValueAt boundary (22 + 10 * N)
        (packState (boundary.finish ⟨N - 1, by omega⟩)) := by
  obtain ⟨hinput, houtput⟩ := bridge_scalar_endpoints hN hpositive
    boundary initial haddresses hbalance hfirst
  exact ⟨pack_path_produces_state boundary hbalance hunique initial
      _ 22 hinput hpackInitial,
    pack_path_produces_state boundary hbalance hunique
      (boundary.finish ⟨N - 1, by omega⟩)
      _ (22 + 10 * N) houtput hpackFinal⟩

/-- Public closure with both packed-value premises replaced by selected
six-row compiler pack paths. The actual emitted row roster, exact joint
balance, unique producers, and local AIR authenticity remain premises. -/
theorem all_public_outputs_from_pack_paths {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (haddresses : ∀ call slot,
      boundary.addresses call slot = canonicalAddress hN call slot)
    (hunique : uniqueProduced (produced boundary))
    (hfirst : boundary.start ⟨0, hpositive⟩ = initial)
    (hrounds : ∀ call, boundary.rounds call = 16)
    (hconstants : ∀ call, boundary.constants call = (13 + call.val : F))
    (hjoint : ((boundary.jointGateSource).circuitYields ++
      jointUses rows boundary.finish).Perm
      ((boundary.jointGateSource).circuitUses ++
        jointYields rows boundary.start))
    (hstep : ∀ call row,
      (rows call row).output =
        boundary.step call (rows call row).input)
    (hpackInitial : PackPath boundary
      (fun lane => inputAddress 0 lane.val) 22)
    (hpackFinal : PackPath boundary
      (fun lane => outputAddress (N - 1) lane.val) (22 + 10 * N))
    (hzero : ValueAt boundary 0 (base 0))
    (hadd : AcceptedRow boundary 22 (22 + 10 * N) (23 + 10 * N) .add)
    (hmul : AcceptedRow boundary 22 (22 + 10 * N)
      (24 + 10 * N) .pointwiseMul)
    (hpaths : ∀ product lane, OutputPath boundary N product lane) :
    ∀ lane : Fin 4,
      boundary.publicOutputs (outputSlot false lane) =
        sourcePrefix N initial lane + initial lane ∧
      boundary.publicOutputs (outputSlot true lane) =
        sourcePrefix N initial lane * initial lane := by
  have hbalance := (joint_gate_and_every_chip_path hN boundary rows
    (by intro call; rw [hrounds call]; omega)
    (by intro call; rw [hrounds call]; omega)
    hjoint hstep).1
  obtain ⟨hpackedInitial, hpackedFinal⟩ :=
    packed_inputs_from_bridge_and_pack hN hpositive boundary initial
      haddresses hfirst hbalance hunique hpackInitial hpackFinal
  exact all_public_outputs_match_source hN hpositive boundary rows initial
    haddresses hunique hfirst hrounds hconstants hjoint hstep
    hpackedInitial hpackedFinal hzero hadd hmul hpaths

end S31.Gadgets.Air.SourceMixedPackCorrespondence
