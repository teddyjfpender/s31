import S31.Gadgets.Air.GateConstantDAG
import S31.Gadgets.Air.GateProducerRoster

/-!
The exact-Gate boundary for an interned source constant. A source-derived
positive physical row owns each finalization step and each packed source add
row. Global *exact* event balance gives those rows one coherent address map;
their installed arithmetic residuals then supply the assumptions of the
constant-DAG theorem. The reduction from the production compressed LogUp to
exact balance, and authentication of arbitrary proof openings, remain open.
-/

namespace S31.Gadgets.Air.GateConstantLookupJoin

open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateWireMap
open S31.Gadgets.Air.GateProducerRoster
open S31.Gadgets.Air.GateConstantDAG
open S31.Functional.Correspondence.StructuralNativeGateCertificate
open S31.Functional.Correspondence.StructuralNativeFixedConstant

abbrev Quad := S31.Gadgets.Packed.Quad

noncomputable def wire (rows : List Row) (externalYields : List Event)
    (address : Nat) (coordinate : Fin 4) : S31.M31 :=
  S31.Field.fromZMod (S31.Gadgets.Packed.coord
    (producedWire (allYields rows externalYields) address) coordinate)

theorem pack_wire (rows : List Row) (externalYields : List Event)
    (address : Nat) :
    S31.Gadgets.Air.Qm31Ops.packM31 (wire rows externalYields address) =
      producedWire (allYields rows externalYields) address := by
  apply S31.Gadgets.Packed.Quad.ext <;>
    simp [wire, S31.Gadgets.Air.Qm31Ops.packM31,
      S31.Gadgets.Packed.coord, S31.Field.to_from]

/-- A source gate's addresses and operation must match one positive row.
The residual premise concerns that row's actual value columns. -/
structure Owner (rows : List Row) (op : S31.Gadgets.Air.Qm31Ops.Op)
    (in0 in1 out : Nat) where
  row : Row
  member : row ∈ rows
  left : row.in0Address = in0
  right : row.in1Address = in1
  output : row.outAddress = out
  selector : row.flags = S31.Gadgets.Air.Qm31Ops.encode op
  positive : 0 < row.multiplicity
  air : ∀ residual ∈ S31.Gadgets.Air.NativeQm31Air.residuals
    row.flags row.in0 row.in1 row.output, residual = 0

theorem owner_air (rows : List Row) (externalUses externalYields : List Event)
    (externalProducers : List Event)
    (hbalance : balanced rows externalUses externalYields)
    (hroster : ((activeRows rows).map Row.outAddress ++
      externalProducers.map Prod.fst).Nodup)
    (hcoverage : ∀ event ∈ externalYields, event ∈ externalProducers)
    (op : S31.Gadgets.Air.Qm31Ops.Op) (in0 in1 out : Nat)
    (owner : Owner rows op in0 in1 out) :
    ∀ residual ∈ S31.Gadgets.Air.NativeQm31Air.residuals
      (S31.Gadgets.Air.Qm31Ops.encode op)
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire rows externalYields in0))
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire rows externalYields in1))
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire rows externalYields out)),
      residual = 0 := by
  have hunique := unique_yields_of_nodup_roster rows externalYields
    externalProducers hroster hcoverage
  have hvalues := row_values_match_wire rows externalUses externalYields
    hbalance hunique owner.row owner.member owner.positive
  have hrow : S31.Gadgets.Air.Qm31Ops.accepts owner.row.flags
      owner.row.in0 owner.row.in1 owner.row.output := by
    simpa only [S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq,
      S31.Gadgets.Air.Qm31Ops.accepts] using owner.air
  have hmatched : S31.Gadgets.Air.Qm31Ops.accepts
      (S31.Gadgets.Air.Qm31Ops.encode op)
      (producedWire (allYields rows externalYields) in0)
      (producedWire (allYields rows externalYields) in1)
      (producedWire (allYields rows externalYields) out) := by
    simpa [← owner.left, ← owner.right, ← owner.output,
      ← owner.selector, ← hvalues.1, ← hvalues.2.1,
      ← hvalues.2.2] using hrow
  simpa only [pack_wire,
    S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq] using hmatched

theorem finalization_air (rows : List Row)
    (externalUses externalYields externalProducers : List Event)
    (gates : List Gate) (mulGates : List MulGate)
    (hbalance : balanced rows externalUses externalYields)
    (hroster : ((activeRows rows).map Row.outAddress ++
      externalProducers.map Prod.fst).Nodup)
    (hcoverage : ∀ event ∈ externalYields, event ∈ externalProducers)
    (hlinear : ∀ gate ∈ gates,
      Owner rows gate.op.airOp gate.in0 gate.in1 gate.out)
    (hmul : ∀ gate ∈ mulGates,
      Owner rows .mul gate.in0 gate.in1 gate.out) :
    NativeAirRows (wire rows externalYields) gates ∧
      NativeMulAirRows (wire rows externalYields) mulGates := by
  constructor
  · intro gate hgate
    exact owner_air rows externalUses externalYields externalProducers
      hbalance hroster hcoverage gate.op.airOp gate.in0 gate.in1 gate.out
      (hlinear gate hgate)
  · intro gate hgate
    exact owner_air rows externalUses externalYields externalProducers
      hbalance hroster hcoverage .mul gate.in0 gate.in1 gate.out
      (hmul gate hgate)

/-- The public `u` producer event fixes the third reserved wire. Its value
is read through the same coherent map as the finalization and source rows. -/
theorem public_u_wire (rows : List Row) (externalYields externalProducers : List Event)
    (hroster : ((activeRows rows).map Row.outAddress ++
      externalProducers.map Prod.fst).Nodup)
    (hcoverage : ∀ event ∈ externalYields, event ∈ externalProducers)
    (hu : (2, (⟨0, 0, 1, 0⟩ : Quad)) ∈ externalYields) :
    S31.Gadgets.Air.Qm31Ops.packM31 (wire rows externalYields 2) =
      ⟨0, 0, 1, 0⟩ := by
  rw [pack_wire]
  exact producedWire_eq (allYields rows externalYields)
    (unique_yields_of_nodup_roster rows externalYields externalProducers
      hroster hcoverage) 2 _
    (List.mem_append_right _ hu)

def sourcePhysical (source : Nat → Row) (index : Nat) :
    S31.Gadgets.Air.GateSourcePhysicalRows.PhysicalRow :=
  { op := .add, flags := (source index).flags,
    lhs := (source index).in0, rhs := (source index).in1,
    output := (source index).output }

/-- For every active lane, an actual source-owned add row reads the constant
proved by the finalization DAG. Its right operand is derived from exact Gate
balance and the positive producer roster; local AIR comes from the selected
physical row. The only remaining source-port facts are the input and output
lane bindings. -/
theorem add_const_active_lanes_of_exact_gate
    (length constant address : Nat)
    (input output : Fin length → S31.M31)
    (rows : List Row) (source : Nat → Row)
    (externalUses externalYields externalProducers : List Event)
    (gates : List Gate) (mulGates : List MulGate)
    (steps : List GateConstantDAG.Step) (final : Known)
    (hpath : GateConstantDAG.Path gates mulGates anchors steps final)
    (htarget : final address = some
      (S31.Gadgets.Air.GateAddConstComposition.broadcast
        (S31.Field.toZMod (RiscvRefinement.M31.reduce constant))))
    (hzeroGate : (⟨.add, 0, 0, 0⟩ : Gate) ∈ gates)
    (huGate : (⟨2, 1, 2⟩ : MulGate) ∈ mulGates)
    (hbalance : balanced rows externalUses externalYields)
    (hroster : ((activeRows rows).map Row.outAddress ++
      externalProducers.map Prod.fst).Nodup)
    (hcoverage : ∀ event ∈ externalYields, event ∈ externalProducers)
    (hu : (2, (⟨0, 0, 1, 0⟩ : Quad)) ∈ externalYields)
    (hlinear : ∀ gate ∈ gates,
      Owner rows gate.op.airOp gate.in0 gate.in1 gate.out)
    (hmul : ∀ gate ∈ mulGates,
      Owner rows .mul gate.in0 gate.in1 gate.out)
    (hsource : ∀ index : Fin length, source (index.val / 4) ∈ rows)
    (hsourceSelector : ∀ index : Fin length,
      (source (index.val / 4)).flags =
        S31.Gadgets.Air.Qm31Ops.encode .add)
    (hsourcePositive : ∀ index : Fin length,
      0 < (source (index.val / 4)).multiplicity)
    (hsourceConstantAddress : ∀ index : Fin length,
      (source (index.val / 4)).in1Address = address)
    (hsourceAir : ∀ index : Fin length, ∀ residual ∈
      S31.Gadgets.Air.NativeQm31Air.residuals
        (source (index.val / 4)).flags
        (source (index.val / 4)).in0
        (source (index.val / 4)).in1
        (source (index.val / 4)).output,
        residual = 0)
    (hinput : ∀ index : Fin length,
      S31.Gadgets.Packed.coord (source (index.val / 4)).in0
        (S31.Gadgets.Air.GateAddConstComposition.activeLane index.val) =
          S31.Field.toZMod (input index))
    (houtput : ∀ index : Fin length,
      S31.Gadgets.Packed.coord (source (index.val / 4)).output
        (S31.Gadgets.Air.GateAddConstComposition.activeLane index.val) =
          S31.Field.toZMod (output index)) :
    ∀ index : Fin length,
      output index = input index + RiscvRefinement.M31.reduce constant := by
  have hair := (finalization_air rows externalUses externalYields
    externalProducers gates mulGates hbalance hroster hcoverage
    hlinear hmul).1
  have hmulAir := (finalization_air rows externalUses externalYields
    externalProducers gates mulGates hbalance hroster hcoverage
    hlinear hmul).2
  have huWire := public_u_wire rows externalYields externalProducers
    hroster hcoverage hu
  apply GateConstantDAG.add_const_active_lanes_sound length constant address
    input output (sourcePhysical source) (wire rows externalYields)
    gates mulGates steps final hpath htarget hzeroGate huGate huWire hair hmulAir
  · intro index
    rfl
  · intro index
    exact hsourceSelector index
  · intro index residual hresidual
    exact hsourceAir index residual hresidual
  · intro index
    have hunique := unique_yields_of_nodup_roster rows externalYields
      externalProducers hroster hcoverage
    have hvalues := row_values_match_wire rows externalUses externalYields
      hbalance hunique (source (index.val / 4)) (hsource index)
      (hsourcePositive index)
    calc
      (sourcePhysical source (index.val / 4)).rhs =
          (source (index.val / 4)).in1 := rfl
      _ = producedWire (allYields rows externalYields)
          (source (index.val / 4)).in1Address := hvalues.2.1
      _ = producedWire (allYields rows externalYields) address := by
          rw [hsourceConstantAddress index]
      _ = S31.Gadgets.Air.Qm31Ops.packM31
          (wire rows externalYields address) := (pack_wire rows externalYields address).symm
  · exact hinput
  · exact houtput

/-- A one-row hand witness: input addresses 7 and 8 are externally produced,
the add row produces address 9, and the public use consumes address 9. -/
def exampleOwner : Owner [honestExample] .add 7 8 9 :=
  { row := honestExample
    member := by simp
    left := rfl
    right := rfl
    output := rfl
    selector := rfl
    positive := by decide
    air := by
      rw [S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq]
      exact honest_example_local }

theorem example_owner_air :
    ∀ residual ∈ S31.Gadgets.Air.NativeQm31Air.residuals
      (S31.Gadgets.Air.Qm31Ops.encode .add)
      (S31.Gadgets.Air.Qm31Ops.packM31
        (wire [honestExample] exampleExternalYields 7))
      (S31.Gadgets.Air.Qm31Ops.packM31
        (wire [honestExample] exampleExternalYields 8))
      (S31.Gadgets.Air.Qm31Ops.packM31
        (wire [honestExample] exampleExternalYields 9)),
      residual = 0 := by
  exact owner_air [honestExample] exampleExternalUses exampleExternalYields
    exampleExternalYields honest_example_balanced (by decide)
    (by intro event hevent; exact hevent) .add 7 8 9 exampleOwner

/-- The locally valid forged row in `GateLookup` reads 4 at address 7 while
the external producer supplies 5. It cannot meet the exact-balance premise. -/
theorem forged_example_cannot_supply_join :
    ¬ balanced [forgedExample] forgedExternalUses exampleExternalYields :=
  forged_example_rejected

end S31.Gadgets.Air.GateConstantLookupJoin
