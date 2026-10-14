import S31.Gadgets.Air.GateAddConstComposition
import S31.Gadgets.Functional.Correspondence.StructuralNativeFixedConstant

/-!
The value of a native interned constant may be derived from a finite DAG of
actual finalization gates, regardless of which radix the builder selected.
This local theorem assumes the gate roster, AIR residuals and public anchors
are authenticated; it does not derive them from arbitrary PCS/FRI acceptance.
-/

namespace S31.Gadgets.Air.GateConstantDAG

open S31.Functional.Correspondence.StructuralNativeGateCertificate
open S31.Functional.Correspondence.StructuralNativeGateOwnership
open S31.Functional.Correspondence.StructuralNativeFixedConstant

abbrev WireQuad := S31.Functional.Correspondence.StructuralNativeGateCertificate.Quad

inductive Op where
  | add | sub | mul
  deriving DecidableEq, Repr

structure Step where
  op : Op
  in0 : Nat
  in1 : Nat
  out : Nat
  deriving DecidableEq, Repr

def Step.owned (step : Step) (gates : List Gate) (mulGates : List MulGate) : Prop :=
  match step.op with
  | .add => (⟨.add, step.in0, step.in1, step.out⟩ : Gate) ∈ gates
  | .sub => (⟨.sub, step.in0, step.in1, step.out⟩ : Gate) ∈ gates
  | .mul => (⟨step.in0, step.in1, step.out⟩ : MulGate) ∈ mulGates

def Step.eval (step : Step) (left right : S31.Gadgets.Packed.Quad) :
    S31.Gadgets.Packed.Quad :=
  match step.op with
  | .add => Packed.add left right
  | .sub => S31.Gadgets.Air.Qm31Ops.subtract left right
  | .mul => Packed.mul left right

theorem Step.air_sound (step : Step)
    (wire : Nat → WireQuad)
    (gates : List Gate) (mulGates : List MulGate)
    (howned : step.owned gates mulGates)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates) :
    S31.Gadgets.Air.Qm31Ops.packM31 (wire step.out) =
      step.eval (S31.Gadgets.Air.Qm31Ops.packM31 (wire step.in0))
        (S31.Gadgets.Air.Qm31Ops.packM31 (wire step.in1)) := by
  cases step with
  | mk op in0 in1 out =>
    cases op with
    | add =>
      have h := linear_gate_packed_sound wire gates
        ⟨.add, in0, in1, out⟩ howned hair
      simpa [Step.eval, GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate] using h
    | sub =>
      have h := linear_gate_packed_sound wire gates
        ⟨.sub, in0, in1, out⟩ howned hair
      simpa [Step.eval, GateOp.airOp, S31.Gadgets.Air.Qm31Ops.evaluate] using h
    | mul =>
      simpa [Step.eval] using
        mul_gate_packed_sound wire mulGates ⟨in0, in1, out⟩ howned hmul

abbrev Known := Nat → Option S31.Gadgets.Packed.Quad

def put (known : Known) (address : Nat)
    (value : S31.Gadgets.Packed.Quad) : Known :=
  fun probe => if probe = address then some value else known probe

def KnownSound (known : Known)
    (wire : Nat → WireQuad) : Prop :=
  ∀ address value, known address = some value →
    S31.Gadgets.Air.Qm31Ops.packM31 (wire address) = value

/-- One certified DAG edge extends the set of values forced by native AIR.
The `known out = none` premise prevents a later edge from replacing a
previously certified wire. -/
theorem put_sound (known : Known) (step : Step)
    (left right : S31.Gadgets.Packed.Quad)
    (wire : Nat → WireQuad)
    (gates : List Gate) (mulGates : List MulGate)
    (hknown : KnownSound known wire)
    (hleft : known step.in0 = some left)
    (hright : known step.in1 = some right)
    (howned : step.owned gates mulGates)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates) :
    KnownSound (put known step.out (step.eval left right)) wire := by
  intro address value hvalue
  by_cases heq : address = step.out
  · subst address
    have hv : value = step.eval left right := by
      simpa [put] using hvalue.symm
    subst value
    simpa [hknown step.in0 left hleft, hknown step.in1 right hright] using
      step.air_sound wire gates mulGates howned hair hmul
  · exact hknown address value (by simpa [put, heq] using hvalue)

/-- A topologically ordered certificate: each input is already known and
every gate is present in the native finalization roster. -/
inductive Path (gates : List Gate) (mulGates : List MulGate) :
    Known → List Step → Known → Prop where
  | done (known) : Path gates mulGates known [] known
  | next (known final : Known) (step : Step) (rest : List Step)
      (left right : S31.Gadgets.Packed.Quad)
      (hleft : known step.in0 = some left)
      (hright : known step.in1 = some right)
      (hfresh : known step.out = none)
      (howned : step.owned gates mulGates)
      (htail : Path gates mulGates
        (put known step.out (step.eval left right)) rest final) :
      Path gates mulGates known (step :: rest) final

theorem Path.sound (wire : Nat → WireQuad)
    (gates : List Gate) (mulGates : List MulGate)
    (initial final : Known) (steps : List Step)
    (hpath : Path gates mulGates initial steps final)
    (hinitial : KnownSound initial wire)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates) :
    KnownSound final wire := by
  induction hpath with
  | done => exact hinitial
  | next known final step rest left right hleft hright _ howned htail ih =>
      exact ih (put_sound known step left right wire gates mulGates
        hinitial hleft hright howned hair hmul)

def anchors : Known := fun address =>
  if address = 0 then some ⟨0, 0, 0, 0⟩ else
  if address = 1 then some ⟨1, 0, 0, 0⟩ else
  if address = 2 then some ⟨0, 0, 1, 0⟩ else none

theorem anchors_sound
    (wire : Nat → WireQuad)
    (hzero : S31.Gadgets.Air.Qm31Ops.packM31 (wire 0) = ⟨0, 0, 0, 0⟩)
    (hone : S31.Gadgets.Air.Qm31Ops.packM31 (wire 1) = ⟨1, 0, 0, 0⟩)
    (hu : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩) :
    KnownSound anchors wire := by
  intro address value hvalue
  by_cases h0 : address = 0
  · subst address
    simp [anchors] at hvalue
    subst value
    exact hzero
  by_cases h1 : address = 1
  · subst address
    simp [anchors] at hvalue
    subst value
    exact hone
  by_cases h2 : address = 2
  · subst address
    simp [anchors] at hvalue
    subst value
    exact hu
  simp [anchors, h0, h1, h2] at hvalue

/-- Any canonical nonzero M31 literal admitted as a native broadcast target
has the required value when its actual finalization DAG evaluates to that
broadcast. The certificate's expected output is computed from public roots,
not copied from a witness cell. -/
theorem broadcast_value (wire : Nat → WireQuad)
    (gates : List Gate) (mulGates : List MulGate)
    (steps : List Step) (final : Known) (address constant : Nat)
    (hpath : Path gates mulGates anchors steps final)
    (htarget : final address = some
      (GateAddConstComposition.broadcast (S31.Field.toZMod
        (RiscvRefinement.M31.reduce constant))))
    (hzero : S31.Gadgets.Air.Qm31Ops.packM31 (wire 0) = ⟨0, 0, 0, 0⟩)
    (hone : S31.Gadgets.Air.Qm31Ops.packM31 (wire 1) = ⟨1, 0, 0, 0⟩)
    (hu : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates) :
    S31.Gadgets.Air.Qm31Ops.packM31 (wire address) =
      GateAddConstComposition.broadcast (S31.Field.toZMod
        (RiscvRefinement.M31.reduce constant)) :=
  (hpath.sound wire gates mulGates anchors final steps
    (anchors_sound wire hzero hone hu) hair hmul) address _ htarget

/-- The three reserved roots are fixed by the actual native self-add and
`Mul(u, one, u)` anchor rows, with `u` supplied by the public output event.
No expected zero/one witness value is assumed here. -/
theorem broadcast_value_from_native_anchors (wire : Nat → WireQuad)
    (gates : List Gate) (mulGates : List MulGate)
    (steps : List Step) (final : Known) (address constant : Nat)
    (hpath : Path gates mulGates anchors steps final)
    (htarget : final address = some
      (GateAddConstComposition.broadcast (S31.Field.toZMod
        (RiscvRefinement.M31.reduce constant))))
    (hzeroGate : (⟨.add, 0, 0, 0⟩ : Gate) ∈ gates)
    (huGate : (⟨2, 1, 2⟩ : MulGate) ∈ mulGates)
    (hu : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates) :
    S31.Gadgets.Air.Qm31Ops.packM31 (wire address) =
      GateAddConstComposition.broadcast (S31.Field.toZMod
        (RiscvRefinement.M31.reduce constant)) := by
  have hzeroWire : wire 0 = fun _ => 0 := by
    funext i
    have h := congrFun (zero_anchor_air_sound (n := 4) (by decide)
      wire gates hzeroGate hair) i
    simpa [active] using h
  have hzero : S31.Gadgets.Air.Qm31Ops.packM31 (wire 0) = ⟨0, 0, 0, 0⟩ := by
    simp [hzeroWire, S31.Gadgets.Air.Qm31Ops.packM31,
      S31.Field.toZMod_zero]
  have hone := one_anchor_air_sound wire mulGates hu huGate hmul
  exact broadcast_value wire gates mulGates steps final address constant
    hpath htarget hzero hone hu hair hmul

/-- The native finalization DAG discharges the literal-value premise of
`add_const` for any active source length. The compiler/lookup joins are
expressed by `hread`, `hinput`, and `houtput`; arbitrary-proof authentication
of those cells remains outside this local theorem. -/
theorem add_const_active_lanes_sound (length constant address : Nat)
    (input output : Fin length → S31.M31)
    (rows : Nat → S31.Gadgets.Air.GateSourcePhysicalRows.PhysicalRow)
    (wire : Nat → WireQuad)
    (gates : List Gate) (mulGates : List MulGate)
    (steps : List Step) (final : Known)
    (hpath : Path gates mulGates anchors steps final)
    (htarget : final address = some
      (GateAddConstComposition.broadcast (S31.Field.toZMod
        (RiscvRefinement.M31.reduce constant))))
    (hzeroGate : (⟨.add, 0, 0, 0⟩ : Gate) ∈ gates)
    (huGate : (⟨2, 1, 2⟩ : MulGate) ∈ mulGates)
    (hu : S31.Gadgets.Air.Qm31Ops.packM31 (wire 2) = ⟨0, 0, 1, 0⟩)
    (hair : NativeAirRows wire gates)
    (hmul : NativeMulAirRows wire mulGates)
    (hop : ∀ index : Fin length, (rows (index.val / 4)).op = .add)
    (hfixed : ∀ index : Fin length,
      (rows (index.val / 4)).flags =
        S31.Gadgets.Air.Qm31Ops.encode (rows (index.val / 4)).op)
    (hrowAir : ∀ index : Fin length, ∀ residual ∈
      S31.Gadgets.Air.NativeQm31Air.residuals
        (rows (index.val / 4)).flags (rows (index.val / 4)).lhs
        (rows (index.val / 4)).rhs (rows (index.val / 4)).output,
        residual = 0)
    (hread : ∀ index : Fin length,
      (rows (index.val / 4)).rhs =
        S31.Gadgets.Air.Qm31Ops.packM31 (wire address))
    (hinput : ∀ index : Fin length,
      S31.Gadgets.Packed.coord (rows (index.val / 4)).lhs
        (GateAddConstComposition.activeLane index.val) =
          S31.Field.toZMod (input index))
    (houtput : ∀ index : Fin length,
      S31.Gadgets.Packed.coord (rows (index.val / 4)).output
        (GateAddConstComposition.activeLane index.val) =
          S31.Field.toZMod (output index)) :
    ∀ index : Fin length,
      output index = input index + RiscvRefinement.M31.reduce constant := by
  have hconstant := broadcast_value_from_native_anchors wire gates mulGates
    steps final address constant hpath htarget hzeroGate huGate hu hair hmul
  apply GateAddConstComposition.active_lanes_m31_sound length
    (RiscvRefinement.M31.reduce constant) input output rows hop hfixed hrowAir
  · intro index
    rw [hread index, hconstant]
  · exact hinput
  · exact houtput

end S31.Gadgets.Air.GateConstantDAG
