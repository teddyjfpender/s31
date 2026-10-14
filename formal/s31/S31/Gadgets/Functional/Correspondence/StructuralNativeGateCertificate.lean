import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffects
import S31.Gadgets.Air.NativeQm31AirProof

/-!
A reusable semantic bridge for a *supplied* native direct-Gate graph. It is
parameterized by actual variable addresses and four-coordinate wire values,
so its theorems quantify over every admitted lane value and every SSA length.
The physical gate roster and variable values still need to be authenticated
against native preprocessed and committed rows. This module does not claim a
theorem about the Zig compiler's emitted bytes.
-/

namespace S31.Functional.Correspondence.StructuralNativeGateCertificate

open S31
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes ArithmeticOp)
open S31.Functional.Correspondence.GeneralLinearSSAEffects

abbrev SourceOp := S31.Functional.Correspondence.SourceFunctionBytes.Op
abbrev EffectStep := S31.Functional.Correspondence.GeneralLinearSSAEffects.Step

abbrev Quad := Fin 4 → M31

def active {n : Nat} (hn : n ≤ 4) (quad : Quad) : Lanes n :=
  fun i => quad ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩

inductive GateOp where
  | add | sub | pointwiseMul
  deriving DecidableEq, Repr

def GateOp.eval (op : GateOp) (a b : M31) : M31 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .pointwiseMul => a * b

def GateOp.source (op : GateOp) : SourceOp :=
  match op with
  | .add => .add
  | .sub => .sub
  | .pointwiseMul => .mul

theorem source_eval (op : GateOp) (a b : M31) :
    S31.Functional.Correspondence.SourceFunctionBytes.Op.eval
      op.source a b = op.eval a b := by cases op <;> rfl

structure Gate where
  op : GateOp
  in0 : Nat
  in1 : Nat
  out : Nat
  deriving DecidableEq, Repr

/-- The mathematical value relation of one actual add/sub/pointwise-mul gate.
The gate's addresses are retained, including subtraction operand order. -/
def Gate.satisfied (wire : Nat → Quad) (gate : Gate) : Prop :=
  ∀ coordinate : Fin 4,
    wire gate.out coordinate =
      gate.op.eval (wire gate.in0 coordinate) (wire gate.in1 coordinate)

/-- This finite check can be reduced on concrete four-coordinate gate rows. -/
def Gate.check (wire : Nat → Quad) (gate : Gate) : Bool :=
  (List.finRange 4).all fun coordinate =>
    decide (wire gate.out coordinate =
      gate.op.eval (wire gate.in0 coordinate) (wire gate.in1 coordinate))

theorem checked_gate_satisfied (wire : Nat → Quad) (gate : Gate)
    (hcheck : gate.check wire = true) : gate.satisfied wire := by
  intro coordinate
  have hall := List.all_eq_true.mp hcheck coordinate
    (List.mem_finRange coordinate)
  exact of_decide_eq_true hall

def checkGates (wire : Nat → Quad) (gates : List Gate) : Bool :=
  gates.all (Gate.check wire)

theorem checked_gates_satisfied (wire : Nat → Quad) (gates : List Gate)
    (hcheck : checkGates wire gates = true) :
    ∀ gate ∈ gates, gate.satisfied wire := by
  intro gate hmember
  exact checked_gate_satisfied wire gate
    (List.all_eq_true.mp hcheck gate hmember)

/-- The direct-Gate AIR selector corresponding to each structural M31 gate.
Source multiplication is packed pointwise multiplication, not QM31 extension
multiplication. -/
def GateOp.airOp : GateOp → S31.Gadgets.Air.Qm31Ops.Op
  | .add => .add
  | .sub => .sub
  | .pointwiseMul => .pointwiseMul

private theorem air_eval_coord (op : GateOp) (a b : Quad) (i : Fin 4) :
    S31.Gadgets.Packed.coord
      (S31.Gadgets.Air.Qm31Ops.evaluate op.airOp
        (S31.Gadgets.Air.Qm31Ops.packM31 a)
        (S31.Gadgets.Air.Qm31Ops.packM31 b)) i =
      S31.Field.toZMod (op.eval (a i) (b i)) := by
  cases op with
  | add =>
      simpa [GateOp.airOp, GateOp.eval, S31.Gadgets.Air.Qm31Ops.s31Op]
        using S31.Gadgets.Air.Qm31Ops.s31Op_coord false a b i
  | sub =>
      simpa [GateOp.airOp, GateOp.eval, S31.Gadgets.Air.Qm31Ops.evaluate]
        using S31.Gadgets.Air.Qm31Ops.sub_coord a b i
  | pointwiseMul =>
      simpa [GateOp.airOp, GateOp.eval, S31.Gadgets.Air.Qm31Ops.s31Op]
        using S31.Gadgets.Air.Qm31Ops.s31Op_coord true a b i

/-- A source-extracted nine-residual native AIR row implies the direct-Gate
semantic equation at every one of its four physical M31 coordinates. This
local algebra bridge still requires the preprocessed selector/address cells
and committed trace values to be authenticated against the actual proof. -/
theorem native_air_row_satisfied (wire : Nat → Quad) (gate : Gate)
    (hair : ∀ r ∈ S31.Gadgets.Air.NativeQm31Air.residuals
      (S31.Gadgets.Air.Qm31Ops.encode gate.op.airOp)
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in0))
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in1))
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.out)), r = 0) :
    gate.satisfied wire := by
  have hmodel : S31.Gadgets.Air.Qm31Ops.accepts
      (S31.Gadgets.Air.Qm31Ops.encode gate.op.airOp)
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in0))
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in1))
      (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.out)) := by
    simpa [S31.Gadgets.Air.Qm31Ops.accepts,
      S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq] using hair
  have hpacked := (S31.Gadgets.Air.Qm31Ops.accepts_encoded gate.op.airOp _ _ _).mp hmodel
  intro coordinate
  apply S31.Field.toZMod_injective
  have hcoord := congrArg (fun q => S31.Gadgets.Packed.coord q coordinate) hpacked
  simpa only [S31.Gadgets.Air.Qm31Ops.coord_packM31,
    air_eval_coord] using hcoord

/-- The native nine-residual relation for every gate in a supplied roster.
The quantification is over the entire roster, including unused gates. -/
def NativeAirRows (wire : Nat → Quad) (gates : List Gate) : Prop :=
  ∀ gate ∈ gates, ∀ r ∈ S31.Gadgets.Air.NativeQm31Air.residuals
    (S31.Gadgets.Air.Qm31Ops.encode gate.op.airOp)
    (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in0))
    (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.in1))
    (S31.Gadgets.Air.Qm31Ops.packM31 (wire gate.out)), r = 0

/-- Local source-extracted AIR acceptance discharges the finite gate-value
check used by the generic structural certificate. The missing global premise
is authentication of these rows as the actual committed direct-Gate AIR. -/
theorem native_air_rows_check (wire : Nat → Quad) (gates : List Gate)
    (hair : NativeAirRows wire gates) : checkGates wire gates = true := by
  unfold checkGates
  apply List.all_eq_true.mpr
  intro gate hmember
  unfold Gate.check
  apply List.all_eq_true.mpr
  intro coordinate _
  exact decide_eq_true (native_air_row_satisfied wire gate (hair gate hmember) coordinate)

theorem gate_active_sound {n : Nat} (hn : n ≤ 4) (wire : Nat → Quad)
    (gate : Gate) (hgate : gate.satisfied wire) :
    active hn (wire gate.out) = fun i =>
      S31.Functional.Correspondence.SourceFunctionBytes.Op.eval gate.op.source
        (active hn (wire gate.in0) i)
        (active hn (wire gate.in1) i) := by
  funext i
  exact (hgate ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩).trans
    (source_eval gate.op _ _).symm

/-- A step's checked source-address map and semantic equality. Actual gate
membership can construct these witnesses through `binary_gate_evidence` or
`constant_gate_evidence`; optimized steps require their own value evidence. -/
inductive StepEvidence {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat) :
    List (Lanes n) → EffectStep → Lanes n → Prop where
  | binaryValue (values : List (Lanes n)) (id lhs rhs : Nat)
      (op : SourceOp) (left right outAddr : Nat)
      (hleft : addresses[lhs]? = some left)
      (hright : addresses[rhs]? = some right)
      (hout : addresses[id]? = some outAddr)
      (hleftValue : values[lhs]? = some (active hn (wire left)))
      (hrightValue : values[rhs]? = some (active hn (wire right)))
      (houtput : active hn (wire outAddr) =
        fun i => S31.Functional.Correspondence.SourceFunctionBytes.Op.eval
          op (active hn (wire left) i)
          (active hn (wire right) i))
      (hid : id = values.length) :
      StepEvidence hn wire gates addresses values
        (.binary id lhs rhs op) (active hn (wire outAddr))
  | constantValue (values : List (Lanes n)) (id lhs value : Nat)
      (multiply : Bool) (left outAddr : Nat)
      (hcanonical : value < S31.modulus)
      (hleft : addresses[lhs]? = some left)
      (hout : addresses[id]? = some outAddr)
      (hleftValue : values[lhs]? = some (active hn (wire left)))
      (houtput : active hn (wire outAddr) =
        if multiply then
          (fun i => active hn (wire left) i * RiscvRefinement.M31.reduce value)
        else (fun i => active hn (wire left) i + RiscvRefinement.M31.reduce value))
      (hid : id = values.length) :
      StepEvidence hn wire gates addresses values
        (.constant id lhs value multiply) (active hn (wire outAddr))

/-- A gate found in the native roster and satisfying its row polynomial
discharges the semantic equality required by a binary source step. -/
theorem binary_gate_evidence {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (values : List (Lanes n)) (id lhs rhs : Nat) (op : GateOp)
    (left right outAddr : Nat)
    (hleft : addresses[lhs]? = some left)
    (hright : addresses[rhs]? = some right)
    (hout : addresses[id]? = some outAddr)
    (hleftValue : values[lhs]? = some (active hn (wire left)))
    (hrightValue : values[rhs]? = some (active hn (wire right)))
    (hid : id = values.length)
    (hmember : ⟨op, left, right, outAddr⟩ ∈ gates)
    (hvalid : checkGates wire gates = true) :
    StepEvidence hn wire gates addresses values
      (.binary id lhs rhs op.source) (active hn (wire outAddr)) := by
  exact .binaryValue values id lhs rhs op.source left right outAddr
    hleft hright hout hleftValue hrightValue
    (gate_active_sound hn wire _
      (checked_gates_satisfied wire gates hvalid _ hmember)) hid

/-- For add/multiply by a canonical M31 literal, the constant operand must
be present as the same value in all four physical coordinates. -/
theorem constant_gate_evidence {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (values : List (Lanes n)) (id lhs value : Nat) (multiply : Bool)
    (left constantAddr outAddr : Nat)
    (hcanonical : value < S31.modulus)
    (hleft : addresses[lhs]? = some left)
    (hout : addresses[id]? = some outAddr)
    (hleftValue : values[lhs]? = some (active hn (wire left)))
    (hid : id = values.length)
    (hconstant : ∀ coordinate : Fin 4,
      wire constantAddr coordinate = RiscvRefinement.M31.reduce value)
    (hmember : ⟨if multiply then .pointwiseMul else .add,
      left, constantAddr, outAddr⟩ ∈ gates)
    (hvalid : checkGates wire gates = true) :
    StepEvidence hn wire gates addresses values
      (.constant id lhs value multiply) (active hn (wire outAddr)) := by
  have hgate := gate_active_sound hn wire _
    (checked_gates_satisfied wire gates hvalid _ hmember)
  refine .constantValue values id lhs value multiply left outAddr
    hcanonical hleft hout hleftValue ?_ hid
  funext i
  have hc := hconstant ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩
  cases multiply <;>
    simpa [GateOp.source, GateOp.eval,
      S31.Functional.Correspondence.SourceFunctionBytes.Op.eval,
      active, hc] using congrFun hgate i

theorem evidence_accepts_row {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (values : List (Lanes n)) (step : EffectStep) (output : Lanes n)
    (hevidence : StepEvidence hn wire gates addresses values step output) :
    acceptsRow values step output (fun _ _ => 0) (fun _ _ => 0) := by
  cases hevidence with
  | binaryValue id lhs rhs op left right outAddr
      hleft hright hout hleftValue hrightValue houtput hid =>
      exact ⟨active hn (wire left), active hn (wire right), hid,
        hleftValue, hrightValue,
        (S31.Functional.Correspondence.SourceFunctionBytes.packed_iff_eval
          op _ _ _ _ _).mpr (fun i => congrFun houtput i)⟩
  | constantValue id lhs value multiply left outAddr
      hcanonical hleft hout hleftValue houtput hid =>
      refine ⟨hcanonical, active hn (wire left), hid, hleftValue, ?_⟩
      cases multiply with
      | false =>
          exact (S31.Functional.Correspondence.SourceFunctionBytes.packed_iff_eval
            .add _ _ _ _ _).mpr (fun i => congrFun houtput i)
      | true =>
          exact (S31.Functional.Correspondence.SourceFunctionBytes.packed_iff_eval
            .mul _ _ _ _ _).mpr (fun i => congrFun houtput i)

/-- The source-selected address of each input is checked against its packed
four-coordinate port. For a public scalar input, the separate native pack
path must show these coordinates equal its bound scalar ABI words. -/
def InputPorts {n : Nat} (hn : n ≤ 4) (wire : Nat → Quad)
    (addresses : List Nat) (count : Nat) (inputs : Nat → Lanes n) : Prop :=
  ∀ id < count, ∃ addr,
    addresses[id]? = some addr ∧ active hn (wire addr) = inputs id

def checkInputPorts {n : Nat} (hn : n ≤ 4) (wire : Nat → Quad)
    (addresses : List Nat) (count : Nat) (inputs : Nat → Lanes n) : Bool :=
  (List.range count).all fun id =>
    match addresses[id]? with
    | none => false
    | some addr => (List.finRange n).all fun i =>
        decide (active hn (wire addr) i = inputs id i)

theorem checked_input_ports_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (addresses : List Nat) (count : Nat)
    (inputs : Nat → Lanes n)
    (hcheck : checkInputPorts hn wire addresses count inputs = true) :
    InputPorts hn wire addresses count inputs := by
  intro id hid
  have hrow := List.all_eq_true.mp hcheck id (List.mem_range.mpr hid)
  cases haddr : addresses[id]? with
  | none => simp [haddr] at hrow
  | some addr =>
      simp only [haddr] at hrow
      refine ⟨addr, rfl, ?_⟩
      funext i
      have hi := List.all_eq_true.mp hrow i (List.mem_finRange i)
      exact of_decide_eq_true hi

def nativeInitial {n : Nat} (hn : n ≤ 4) (wire : Nat → Quad)
    (addresses : List Nat) (count : Nat) : List (Lanes n) :=
  (List.range count).map fun id =>
    active hn (wire (addresses[id]?.getD 0))

theorem checked_input_ports {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (addresses : List Nat) (count : Nat)
    (inputs : Nat → Lanes n)
    (hports : InputPorts hn wire addresses count inputs) :
    nativeInitial hn wire addresses count = initialValues count inputs := by
  unfold nativeInitial initialValues
  apply List.map_congr_left
  intro id hid
  obtain ⟨addr, haddr, hvalue⟩ := hports id (List.mem_range.mp hid)
  simpa [haddr] using hvalue

/-- The selected source output must be the same packed native wire as the
public claim. This checks all declared coordinates, including short lanes. -/
def checkOutputPort {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (addresses : List Nat)
    (final : List (Lanes n)) (outputId : Nat)
    (claimed : Lanes n) : Bool :=
  match addresses[outputId]?, final[outputId]? with
  | some addr, some actual =>
      (List.finRange n).all fun i =>
        decide (actual i = active hn (wire addr) i) &&
          decide (claimed i = active hn (wire addr) i)
  | _, _ => false

theorem checked_output_port {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (addresses : List Nat)
    (final : List (Lanes n)) (outputId : Nat)
    (claimed : Lanes n)
    (hcheck : checkOutputPort hn wire addresses final outputId claimed = true) :
    final[outputId]? = some claimed := by
  unfold checkOutputPort at hcheck
  cases haddr : addresses[outputId]? with
  | none => simp [haddr] at hcheck
  | some addr =>
      cases hactual : final[outputId]? with
      | none => simp [haddr, hactual] at hcheck
      | some actual =>
          simp only [haddr, hactual] at hcheck
          have heq : actual = claimed := by
            funext i
            have hi := List.all_eq_true.mp hcheck i (List.mem_finRange i)
            simp at hi
            exact hi.1.trans hi.2.symm
          simp [heq]

inductive NativeTrace {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat) :
    List (Lanes n) → List EffectStep → List (Lanes n) → Prop where
  | done (values : List (Lanes n)) : NativeTrace hn wire gates addresses values [] values
  | next {values final : List (Lanes n)} {step : EffectStep} {rest : List EffectStep}
      {output : Lanes n}
      (hrow : StepEvidence hn wire gates addresses values step output)
      (hrest : NativeTrace hn wire gates addresses
        (values ++ [output]) rest final) :
      NativeTrace hn wire gates addresses values (step :: rest) final

theorem native_trace_accepts {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    {initial final : List (Lanes n)} {steps : List EffectStep}
    (htrace : NativeTrace hn wire gates addresses initial steps final) :
    AcceptsTrace initial steps final := by
  induction htrace with
  | done values => exact .done values
  | next hrow hrest ih =>
      exact .next _ (fun _ _ => 0) (fun _ _ => 0)
        (evidence_accepts_row hn wire gates addresses _ _ _ hrow) ih

/-- A masked native equality path constrains all declared lanes. The mask
may leave inactive packed coordinates arbitrary. -/
theorem masked_assertion_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (left right diff mask masked zeroAddr : Nat)
    (hsub : ∀ coordinate : Fin 4,
      wire diff coordinate = wire left coordinate - wire right coordinate)
    (hmul : ∀ coordinate : Fin 4,
      wire masked coordinate = wire diff coordinate * wire mask coordinate)
    (hmask : ∀ i : Fin n,
      wire mask ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ = 1)
    (heq : wire masked = wire zeroAddr)
    (hzero : ∀ i : Fin n,
      wire zeroAddr ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ = 0) :
    active hn (wire left) = active hn (wire right) := by
  funext i
  let coordinate : Fin 4 := ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩
  have h := congrFun heq coordinate
  have hdiff : wire left coordinate - wire right coordinate = 0 := by
    simpa [coordinate, hmul coordinate, hmask i, hsub coordinate,
      hzero i] using h
  exact (RiscvRefinement.M31.sub_eq_zero_iff _ _).mp hdiff

/-- The assertion certificate carries all checked source pairs, including
dead producers. `masked_assertion_sound` supplies the equality when a native
partial-lane mask gadget is used. -/
def NativeAssertions {n : Nat} (final : List (Lanes n))
    (assertions : List (Nat × Nat)) : Prop :=
  ∃ pairs, resolveAssertions final assertions = some pairs ∧
    ∀ pair ∈ pairs, pair.1 = pair.2

def checkAssertions {n : Nat} (final : List (Lanes n))
    (assertions : List (Nat × Nat)) : Bool :=
  match resolveAssertions final assertions with
  | none => false
  | some pairs => pairs.all fun pair =>
      (List.finRange n).all fun i => decide (pair.1 i = pair.2 i)

theorem checked_assertions_sound {n : Nat} (final : List (Lanes n))
    (assertions : List (Nat × Nat))
    (hcheck : checkAssertions final assertions = true) :
    NativeAssertions final assertions := by
  cases hresolve : resolveAssertions final assertions with
  | none => simp [checkAssertions, hresolve] at hcheck
  | some pairs =>
      simp only [checkAssertions, hresolve] at hcheck
      refine ⟨pairs, hresolve, ?_⟩
      intro pair hmember
      funext i
      have hrow := List.all_eq_true.mp hcheck pair hmember
      have hi := List.all_eq_true.mp hrow i (List.mem_finRange i)
      exact of_decide_eq_true hi

theorem native_assertions_air {n : Nat} (final : List (Lanes n))
    (assertions : List (Nat × Nat))
    (hassert : NativeAssertions final assertions) :
    assertionsAir final assertions := by
  obtain ⟨pairs, hresolve, heq⟩ := hassert
  exact ⟨pairs, hresolve, fun pair hmem =>
    (assertion_poly_iff_eq pair.1 pair.2).mpr (heq pair hmem)⟩

/-- Join the native address/gate certificate to the already proved generic
SSA-to-source theorem. Assertions include unused producers. -/
theorem checked_native_trace_sound {n : Nat} (hn : n ≤ 4)
    (ssa : EmittedSSA) (source : Source)
    (certificate : Certificate) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (hcheck : checkEmittedSSA ssa source = some certificate)
    (hlanes : ssa.lane_count = n)
    (hports : checkInputPorts hn wire addresses certificate.inputs inputs = true)
    (htrace : NativeTrace hn wire gates addresses
      (nativeInitial hn wire addresses certificate.inputs)
      certificate.steps final)
    (houtput : checkOutputPort hn wire addresses final
      certificate.output claimed = true)
    (hassert : checkAssertions final certificate.assertions = true) :
    source.accepts inputs claimed := by
  have hinitial := checked_input_ports hn wire addresses
    certificate.inputs inputs
    (checked_input_ports_sound hn wire addresses certificate.inputs inputs hports)
  rw [hinitial] at htrace
  subst n
  exact emitted_ssa_air_sound ssa source certificate inputs claimed final
    hcheck (native_trace_accepts hn wire gates addresses htrace)
    (checked_output_port hn wire addresses final certificate.output claimed houtput)
    (native_assertions_air final certificate.assertions
      (checked_assertions_sound final certificate.assertions hassert))

end S31.Functional.Correspondence.StructuralNativeGateCertificate
