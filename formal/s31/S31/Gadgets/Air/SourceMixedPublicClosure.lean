import S31.Gadgets.Air.SourceMixedChainSemantics
import S31.Gadgets.Air.UnpackRows
import S31.Gadgets.Air.GateWireMap

/-!
Conditional public closure for the direct-output mixed source family. The
compiler emits two packed arithmetic rows, `simd.unpackIdx` mask/inverse rows,
and `setOutputs` copy rows. It does not emit scalar add/mul rows directly at
reserved public addresses 3..10. Every row below is selected from the actual
modeled Gate list and checked by the local Qm31 AIR; row values are not assumed.
The two packed input value memberships are explicit compiler/packing boundary
obligations, not consequences of the chip bridge alone.
-/

namespace S31.Gadgets.Air.SourceMixedPublicClosure

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateWireMap
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAddressSchedule
open S31.Gadgets.Air.SourceMixedChainSemantics
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.UnpackRows

/-- Four source lanes in the production packed QM31 layout. -/
def packState (state : State) : Quad :=
  ⟨state ⟨0, by decide⟩, state ⟨1, by decide⟩,
   state ⟨2, by decide⟩, state ⟨3, by decide⟩⟩

theorem coord_packState (state : State) (lane : Fin 4) :
    coord (packState state) lane = state lane := by
  fin_cases lane <;> rfl

def produced {N : Nat} (boundary : Boundary N) : List Event :=
  allYields boundary.jointGateSource.gateRows
    boundary.jointGateSource.gateExternalYields

def ValueAt {N : Nat} (boundary : Boundary N) (address : Nat)
    (value : Quad) : Prop := (address, value) ∈ produced boundary

private theorem value_wire {N : Nat} (boundary : Boundary N)
    (hunique : uniqueProduced (produced boundary))
    {address : Nat} {value : Quad} (h : ValueAt boundary address value) :
    producedWire (produced boundary) address = value :=
  producedWire_eq _ hunique address value h

/-- A selected production Gate row, including source-owned addresses,
positive output multiplicity and its nine local AIR residuals. -/
def AcceptedRow {N : Nat} (boundary : Boundary N)
    (in0 in1 out : Nat) (op : Qm31Ops.Op) : Prop :=
  ∃ row ∈ boundary.rows,
    row.in0Address.val = in0 ∧ row.in1Address.val = in1 ∧
    row.outAddress.val = out ∧ row.flags = encode op ∧
    0 < row.multiplicity ∧
    accepts row.flags row.in0 row.in1 row.output

private theorem accepted_row_equation {N : Nat} (boundary : Boundary N)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (hunique : uniqueProduced (produced boundary))
    (in0 in1 out : Nat) (op : Qm31Ops.Op)
    (hrow : AcceptedRow boundary in0 in1 out op) :
    producedWire (produced boundary) out =
      evaluate op (producedWire (produced boundary) in0)
        (producedWire (produced boundary) in1) := by
  obtain ⟨row, hmem, h0, h1, hout, hflags, hm, hair⟩ := hrow
  have hgate : row.toGate ∈ boundary.jointGateSource.gateRows :=
    List.mem_map.mpr ⟨row, hmem, rfl⟩
  obtain ⟨hv0, hv1, hvout⟩ := row_values_match_wire
    boundary.jointGateSource.gateRows
    boundary.jointGateSource.gateExternalUses
    boundary.jointGateSource.gateExternalYields
    hbalance hunique row.toGate hgate
    (by simpa [CanonicalRow.toGate] using hm)
  have heval : row.output = evaluate op row.in0 row.in1 :=
    (accepts_encoded op row.in0 row.in1 row.output).mp
      (by simpa [CanonicalRow.toGate, hflags] using hair)
  have hv0' : row.in0 = producedWire (produced boundary)
      row.in0Address.val := by
    simpa [CanonicalRow.toGate, produced] using hv0
  have hv1' : row.in1 = producedWire (produced boundary)
      row.in1Address.val := by
    simpa [CanonicalRow.toGate, produced] using hv1
  calc
    producedWire (produced boundary) out = row.output := by
      rw [← hout]
      exact hvout.symm
    _ = evaluate op row.in0 row.in1 := heval
    _ = evaluate op (producedWire (produced boundary) in0)
          (producedWire (produced boundary) in1) := by
      rw [← h0, ← h1]
      exact congrArg₂ (evaluate op) hv0' hv1'

/-- Reserved output slot, 0..3 for sum and 4..7 for product. -/
def outputSlot (product : Bool) (lane : Fin 4) : Fin 8 :=
  ⟨(if product then 4 else 0) + lane.val, by split_ifs <;> omega⟩

def packedOutputAddress (N : Nat) (product : Bool) : Nat :=
  (if product then 24 else 23) + 10 * N

/-- `simd.unpackIdx` selects one packed coordinate through a pointwise mask,
then (except lane zero) an extension-basis inverse multiply. `setOutputs`
adds the final `scalar + zero` copy row at the reserved public address.
The intermediate addresses are existential because they depend on fixed-row
allocation, but all intermediate rows must be present and AIR-accepted. -/
def OutputPath {N : Nat} (boundary : Boundary N) (callCount : Nat)
    (product : Bool) (lane : Fin 4) : Prop :=
  ∃ unitAddress maskedAddress inverseAddress scalarAddress : Nat,
    ValueAt boundary unitAddress (unit lane) ∧
    AcceptedRow boundary (packedOutputAddress callCount product)
      unitAddress maskedAddress .pointwiseMul ∧
    (if lane.val = 0 then scalarAddress = maskedAddress else
      ValueAt boundary inverseAddress (unitInverse lane) ∧
      AcceptedRow boundary maskedAddress inverseAddress scalarAddress .mul) ∧
    AcceptedRow boundary scalarAddress 0
      (3 + (outputSlot product lane).val) .add

private theorem public_is_produced {N : Nat} (boundary : Boundary N)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (slot : Fin 8) :
    ValueAt boundary (3 + slot.val) (base (boundary.publicOutputs slot)) := by
  unfold ValueAt produced
  apply hbalance.mem_iff.mp
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨((⟨3 + slot.val, by omega⟩ : CanonicalAddress),
    base (boundary.publicOutputs slot)), ?_, rfl⟩
  unfold Boundary.jointGateSource
  apply List.mem_append_left
  apply List.mem_append_right
  unfold Boundary.publicFeeder
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot, rfl⟩)

private theorem output_path_value {N : Nat} (boundary : Boundary N)
    (hbalance : balanced boundary.jointGateSource.gateRows
      boundary.jointGateSource.gateExternalUses
      boundary.jointGateSource.gateExternalYields)
    (hunique : uniqueProduced (produced boundary))
    (hzero : ValueAt boundary 0 (base 0))
    (callCount : Nat) (product : Bool) (lane : Fin 4)
    (hpath : OutputPath boundary callCount product lane) :
    boundary.publicOutputs (outputSlot product lane) =
      coord (producedWire (produced boundary)
        (packedOutputAddress callCount product)) lane := by
  let wire := producedWire (produced boundary)
  obtain ⟨unitAddress, maskedAddress, inverseAddress, scalarAddress,
    hunit, hmask, hinverse, hcopy⟩ := hpath
  have hunitWire : wire unitAddress = unit lane := value_wire boundary hunique hunit
  have hzeroWire : wire 0 = base 0 := value_wire boundary hunique hzero
  have hmaskEq := accepted_row_equation boundary hbalance hunique
    (packedOutputAddress callCount product) unitAddress maskedAddress
    .pointwiseMul hmask
  change wire maskedAddress =
    evaluate .pointwiseMul (wire (packedOutputAddress callCount product))
      (wire unitAddress) at hmaskEq
  rw [hunitWire] at hmaskEq
  have hscalar : wire scalarAddress =
      base (coord (wire (packedOutputAddress callCount product)) lane) := by
    have hacceptMask : accepts (encode .pointwiseMul)
        (wire (packedOutputAddress callCount product)) (unit lane)
        (wire maskedAddress) :=
      (accepts_encoded .pointwiseMul _ _ _).mpr
        hmaskEq
    have hunpack : acceptsUnpack lane
        (wire (packedOutputAddress callCount product))
        (wire scalarAddress) := by
      refine ⟨wire maskedAddress, hacceptMask, ?_⟩
      by_cases hlane : lane.val = 0
      · simp only [hlane, ↓reduceIte] at hinverse ⊢
        simpa [hinverse]
      · simp only [hlane, ↓reduceIte] at hinverse ⊢
        obtain ⟨hinvValue, hinvRow⟩ := hinverse
        have hinvWire : wire inverseAddress = unitInverse lane :=
          value_wire boundary hunique hinvValue
        have hinvEq := accepted_row_equation boundary hbalance hunique
          maskedAddress inverseAddress scalarAddress .mul hinvRow
        change wire scalarAddress = evaluate .mul
          (wire maskedAddress) (wire inverseAddress) at hinvEq
        rw [hinvWire] at hinvEq
        exact (accepts_encoded .mul _ _ _).mpr
          hinvEq
    exact (acceptsUnpack_iff lane _ _).mp hunpack
  have hcopyEq := accepted_row_equation boundary hbalance hunique
    scalarAddress 0 (3 + (outputSlot product lane).val) .add hcopy
  change wire (3 + (outputSlot product lane).val) =
    evaluate .add (wire scalarAddress) (wire 0) at hcopyEq
  have hpublicWire : wire (3 + (outputSlot product lane).val) =
      base (boundary.publicOutputs (outputSlot product lane)) :=
    value_wire boundary hunique (public_is_produced boundary hbalance _)
  rw [hscalar, hzeroWire] at hcopyEq
  have hword := hpublicWire.symm.trans hcopyEq
  have hbase : base (boundary.publicOutputs (outputSlot product lane)) =
      base (coord (wire (packedOutputAddress callCount product)) lane) := by
    simpa [evaluate, Packed.add, base] using hword
  exact congrArg Quad.a hbase

/-- Actual packed-tail/public path conditional theorem. The two packing
memberships bind source states to the packed circuit wires at 22 and
`22+10N`. They remain compiler/packing correspondence obligations. The
remaining premises select exactly the two packed arithmetic rows, eight
unpack paths, and eight `setOutputs` copy rows; no public result is assumed. -/
theorem all_public_outputs_match_source {N : Nat}
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
    (hjoint : ((boundary.jointGateSource).circuitUses ++
      jointUses rows boundary.finish).Perm
      ((boundary.jointGateSource).circuitYields ++
        jointYields rows boundary.start))
    (hstep : ∀ call row,
      (rows call row).output =
        boundary.step call (rows call row).input)
    (hpackedInitial : ValueAt boundary 22 (packState initial))
    (hpackedFinal : ValueAt boundary (22 + 10 * N)
      (packState (boundary.finish ⟨N - 1, by omega⟩)))
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
  let last : Fin N := ⟨N - 1, by omega⟩
  let wire := producedWire (produced boundary)
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
  have hfirstWire : wire 22 = packState initial :=
    value_wire boundary hunique hpackedInitial
  have hfinalWire : wire (22 + 10 * N) = packState (sourcePrefix N initial) := by
    have h := value_wire boundary hunique hpackedFinal
    change wire (22 + 10 * N) = packState (boundary.finish last) at h
    rw [hend] at h
    exact h
  have haddEq := accepted_row_equation boundary hbalance hunique
    22 (22 + 10 * N) (23 + 10 * N) .add hadd
  have hmulEq := accepted_row_equation boundary hbalance hunique
    22 (22 + 10 * N) (24 + 10 * N) .pointwiseMul hmul
  change wire (23 + 10 * N) = evaluate .add
    (wire 22) (wire (22 + 10 * N)) at haddEq
  change wire (24 + 10 * N) = evaluate .pointwiseMul
    (wire 22) (wire (22 + 10 * N)) at hmulEq
  intro lane
  have hsum := output_path_value boundary hbalance hunique hzero
    N false lane (hpaths false lane)
  have hproduct := output_path_value boundary hbalance hunique hzero
    N true lane (hpaths true lane)
  constructor
  · change boundary.publicOutputs (outputSlot false lane) =
      coord (wire (23 + 10 * N)) lane at hsum
    rw [haddEq, hfinalWire, hfirstWire] at hsum
    fin_cases lane <;>
      simpa [evaluate, Packed.add, packState, coord, add_comm] using hsum
  · change boundary.publicOutputs (outputSlot true lane) =
      coord (wire (24 + 10 * N)) lane at hproduct
    rw [hmulEq, hfinalWire, hfirstWire] at hproduct
    fin_cases lane <;>
      simpa [evaluate, Packed.pointwise, packState, coord, mul_comm] using hproduct

end S31.Gadgets.Air.SourceMixedPublicClosure
