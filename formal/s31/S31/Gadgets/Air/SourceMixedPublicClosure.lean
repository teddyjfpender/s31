import S31.Gadgets.Air.SourceMixedChainSemantics

/-!
Conditional closure of the reviewed source-shaped mixed program's eight public
M31 words. The chip path produces the final state. The source tail contains
four addition rows and four pointwise multiplication rows, each selected by
the exact canonical input and public-output addresses. Their operand and
output values are *not* supplied as premises: exact joint event balance,
unique Gate producers, and local nine-residual Qm31 acceptance determine them.

The model still assumes that the native compiler emits these rows and that a
verified native proof authenticates the exact joint event balance, uniqueness,
and local row constraints. This theorem does not discharge those obligations.
-/

namespace S31.Gadgets.Air.SourceMixedPublicClosure

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAddressSchedule
open S31.Gadgets.Air.SourceMixedChainSemantics
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge

private theorem bridge_is_produced {N : Nat} (boundary : Boundary N)
    (call : Fin N) (slot : Fin 8) :
    ((boundary.addresses call slot).val,
      base (boundary.words call slot)) ∈
      allYields boundary.jointGateSource.gateRows
        boundary.jointGateSource.gateExternalYields := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(boundary.addresses call slot, base (boundary.words call slot)), ?_, rfl⟩
  unfold Boundary.jointGateSource
  apply List.mem_append_right
  unfold Boundary.bridgeGates
  apply List.mem_flatMap.mpr
  exact ⟨call, List.mem_finRange call, List.mem_ofFn.mpr ⟨slot, rfl⟩⟩

private theorem public_is_produced {N : Nat} (boundary : Boundary N)
    (slot : Fin 8) :
    (3 + slot.val, base (boundary.publicOutputs slot)) ∈
      allYields boundary.jointGateSource.gateRows
        boundary.jointGateSource.gateExternalYields := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨((⟨3 + slot.val, by omega⟩ : CanonicalAddress),
    base (boundary.publicOutputs slot)), ?_, rfl⟩
  unfold Boundary.jointGateSource
  apply List.mem_append_left
  apply List.mem_append_right
  unfold Boundary.publicFeeder
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot, rfl⟩)

/-- A selected tail row has the reviewed scalar address topology and is
accepted by the local Qm31 AIR. No operand or result value is assumed. -/
def TailRow {N : Nat} (boundary : Boundary N) (last : Fin N)
    (lane : Fin 4) (op : Qm31Ops.Op) (publicAddress : Nat) : Prop :=
  ∃ row ∈ boundary.rows,
    row.in0Address.val = outputAddress last.val lane.val ∧
    row.in1Address.val = inputAddress 0 lane.val ∧
    row.outAddress.val = publicAddress ∧
    row.flags = encode op ∧
    0 < row.multiplicity ∧
    accepts row.flags row.in0 row.in1 row.output

private theorem tail_row_value {N : Nat} (hN : N ≤ 8)
    (hpositive : 0 < N)
    (boundary : Boundary N) (last : Fin N) (lane : Fin 4)
    (op : Qm31Ops.Op) (publicSlot : Fin 8)
    (haddresses : ∀ call slot,
      boundary.addresses call slot = canonicalAddress hN call slot)
    (hbalanced : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (hunique : uniqueProduced
      (allYields boundary.jointGateSource.gateRows
        boundary.jointGateSource.gateExternalYields))
    (htail : TailRow boundary last lane op (3 + publicSlot.val)) :
    base (boundary.publicOutputs publicSlot) =
      evaluate op (base (boundary.finish last lane))
        (base (boundary.start ⟨0, hpositive⟩ lane)) := by
  obtain ⟨row, hrow, hin0, hin1, hout, hflags, hm, hair⟩ := htail
  let rows := boundary.jointGateSource.gateRows
  let yields := allYields rows boundary.jointGateSource.gateExternalYields
  have hrowGate : row.toGate ∈ rows := List.mem_map.mpr ⟨row, hrow, rfl⟩
  have hfinal :
      (row.in0Address.val, base (boundary.finish last lane)) ∈ yields := by
    have h := bridge_is_produced boundary last
      ⟨4 + lane.val, by omega⟩
    rw [hin0]
    simpa [Boundary.finish, haddresses last ⟨4 + lane.val, by omega⟩,
      canonicalAddress, bridgeAddress] using h
  have hinitial :
      (row.in1Address.val,
        base (boundary.start ⟨0, hpositive⟩ lane)) ∈ yields := by
    have h := bridge_is_produced boundary ⟨0, hpositive⟩
      ⟨lane.val, by omega⟩
    rw [hin1]
    simpa [Boundary.start, haddresses ⟨0, hpositive⟩
      ⟨lane.val, by omega⟩, canonicalAddress, bridgeAddress] using h
  obtain ⟨actualOp, hactual, hresult⟩ := addressed_row_sound
    rows boundary.jointGateSource.gateExternalUses
    boundary.jointGateSource.gateExternalYields row.toGate hrowGate
    hbalanced hunique _ _ hfinal hinitial hair
  have hop : actualOp = op := by
    cases actualOp <;> cases op <;> simp_all [encode, CanonicalRow.toGate]
  have houtput : (row.outAddress.val, row.output) ∈ yields :=
    row_output_yield rows boundary.jointGateSource.gateExternalYields
      row.toGate hrowGate (by simpa [CanonicalRow.toGate] using hm)
  have hpub := public_is_produced boundary publicSlot
  have heq := hunique (3 + publicSlot.val)
    (base (boundary.publicOutputs publicSlot)) row.output
    hpub (by simpa [hout] using houtput)
  simpa [hop] using heq.trans hresult

/-- Exact joint event balance, the source-shaped chip schedule, and eight
selected locally accepted tail rows force every public word to be the source
evaluation. The eight claims remain the verifier statement words supplied to
`Boundary.publicFeeder`; no claim value occurs among the tail-row premises. -/
theorem all_public_outputs_match_source {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (haddresses : ∀ call slot,
      boundary.addresses call slot = canonicalAddress hN call slot)
    (hunique : uniqueProduced
      (allYields boundary.jointGateSource.gateRows
        boundary.jointGateSource.gateExternalYields))
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
    (hadd : ∀ lane : Fin 4,
      TailRow boundary ⟨N - 1, by omega⟩ lane .add (3 + lane.val))
    (hmul : ∀ lane : Fin 4,
      TailRow boundary ⟨N - 1, by omega⟩ lane .pointwiseMul
        (7 + lane.val)) :
    ∀ lane : Fin 4,
      boundary.publicOutputs ⟨lane.val, by omega⟩ =
        sourcePrefix N initial lane + initial lane ∧
      boundary.publicOutputs ⟨4 + lane.val, by omega⟩ =
        sourcePrefix N initial lane * initial lane := by
  let last : Fin N := ⟨N - 1, by omega⟩
  have hbalance := (joint_gate_and_every_chip_path hN boundary rows
    (by intro call; rw [hrounds call]; omega)
    (by intro call; rw [hrounds call]; omega)
    hjoint hstep).1
  have hprefix := source_prefix_of_joint_event_balance hN hpositive
    boundary rows initial haddresses hunique hfirst hrounds hconstants
    hjoint hstep
  have hlast : last.val + 1 = N := by simp [last]; omega
  have hend : boundary.finish last = sourcePrefix N initial := by
    simpa [hlast] using hprefix last
  intro lane
  have ha := tail_row_value hN hpositive boundary last lane .add
    ⟨lane.val, by omega⟩ haddresses hbalance hunique (hadd lane)
  have hm := tail_row_value hN hpositive boundary last lane .pointwiseMul
    ⟨4 + lane.val, by omega⟩ haddresses hbalance hunique
    (by simpa [show 3 + (4 + lane.val) = 7 + lane.val by omega]
      using hmul lane)
  constructor
  · have ha' := congrArg Quad.a ha
    rw [hfirst, hend] at ha'
    simpa [Qm31Ops.evaluate, Packed.add, Packed.base] using ha'
  · have hm' := congrArg Quad.a hm
    rw [hfirst, hend] at hm'
    simpa [Qm31Ops.evaluate, Packed.pointwise, Packed.base] using hm'

end S31.Gadgets.Air.SourceMixedPublicClosure
