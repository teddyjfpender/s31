import S31.Gadgets.Functional.Correspondence.StructuralNativeTraceDecoder

/-!
An AIR-derived source trace for the direct binary M31 fragment and exact
zero/one identity erasures. Unlike the
value-level graph decoder, this checker does not test each source result
equation. It requires an actual native add/sub/pointwise-mul gate for every
source step; commutative gates may swap operands and CSE may reuse a gate.
The theorem derives each binary source equation from the native AIR residuals
of that gate. An erased add-zero or multiply-one step instead must map to the
exact same physical wire as its input; field identities then prove its result.
Other constant steps remain outside this profile.
-/

namespace S31.Functional.Correspondence.StructuralNativeGateOwnership

open S31
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)
open S31.Functional.Correspondence.GeneralLinearSSAEffects
open S31.Functional.Correspondence.StructuralNativeGateCertificate
open S31.Functional.Correspondence.StructuralNativeTraceDecoder
open S31.Functional.Correspondence.GeneralLinearSSABytes (Parse)

private def gateOp : SourceOp → GateOp
  | .add => .add
  | .sub => .sub
  | .mul => .pointwiseMul

private theorem gateOp_source (op : SourceOp) : (gateOp op).source = op := by
  cases op <;> rfl

private def sourceGate (op : SourceOp) (left right outAddr : Nat) : Gate :=
  ⟨gateOp op, left, right, outAddr⟩

/-- An exact native gate may be shared by several source CSE nodes. Subtraction
keeps operand order; addition and multiplication may use either order. -/
def checkDirectOwner (gates : List Gate) (op : SourceOp)
    (left right outAddr : Nat) : Bool :=
  decide (sourceGate op left right outAddr ∈ gates) ||
    (decide (op ≠ .sub) &&
      decide (sourceGate op right left outAddr ∈ gates))

private theorem source_swap (op : SourceOp) (h : op ≠ .sub) (a b : M31) :
    op.eval b a = op.eval a b := by
  cases op with
  | add => exact congrArg RiscvRefinement.M31.reduce (Nat.add_comm b.val a.val)
  | sub => contradiction
  | mul => exact congrArg RiscvRefinement.M31.reduce (Nat.mul_comm b.val a.val)

/-- The source equation follows from an owning gate's AIR residuals, without
checking the source output value equation as a separate oracle assertion. -/
theorem direct_owner_air_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (op : SourceOp)
    (left right outAddr : Nat)
    (howner : checkDirectOwner gates op left right outAddr = true)
    (hair : NativeAirRows wire gates) :
    active hn (wire outAddr) = fun i =>
      op.eval (active hn (wire left) i) (active hn (wire right) i) := by
  unfold checkDirectOwner at howner
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at howner
  rcases howner with hforward | hreverse
  · have hmember : sourceGate op left right outAddr ∈ gates :=
      hforward
    have hgate := gate_active_sound hn wire (sourceGate op left right outAddr)
      (native_air_row_satisfied wire _ (hair _ hmember))
    simpa [sourceGate, gateOp_source] using hgate
  · rcases hreverse with ⟨hne, hfound⟩
    have hmember : sourceGate op right left outAddr ∈ gates :=
      hfound
    have hgate := gate_active_sound hn wire (sourceGate op right left outAddr)
      (native_air_row_satisfied wire _ (hair _ hmember))
    funext i
    have hi := congrFun hgate i
    simpa [sourceGate, gateOp_source, source_swap op hne] using hi

/-- A binary step needs its exact native gate owner. An add-zero or
multiply-one step instead needs the exact physical source/output wire alias.
The checker never compares a step's sampled output to its arithmetic result. -/
def checkOwnedStep {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (values : List (Lanes n)) (step : EffectStep) : Option (Lanes n) :=
  match step with
  | .binary id lhs rhs op =>
      match addresses[lhs]?, addresses[rhs]?, addresses[id]? with
      | some left, some right, some outAddr =>
          if id = values.length ∧
              values[lhs]? = some (active hn (wire left)) ∧
              values[rhs]? = some (active hn (wire right)) ∧
              checkDirectOwner gates op left right outAddr = true then
            some (active hn (wire outAddr))
          else none
      | _, _, _ => none
  | .constant id lhs value multiply =>
      match addresses[lhs]?, addresses[id]? with
      | some left, some outAddr =>
          if value < S31.modulus ∧ id = values.length ∧
              values[lhs]? = some (active hn (wire left)) ∧
              outAddr = left ∧
              (if multiply then value = 1 else value = 0) then
            some (active hn (wire outAddr))
          else none
      | _, _ => none

theorem checkOwnedStep_air_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (values : List (Lanes n)) (step : EffectStep) (output : Lanes n)
    (hair : NativeAirRows wire gates)
    (hstep : checkOwnedStep hn wire gates addresses values step = some output) :
    StepEvidence hn wire gates addresses values step output := by
  cases step with
  | constant id lhs value multiply =>
      unfold checkOwnedStep at hstep
      cases hleft : addresses[lhs]? with
      | none => simp [hleft] at hstep
      | some left =>
          cases hout : addresses[id]? with
          | none => simp [hleft, hout] at hstep
          | some outAddr =>
              simp only [hleft, hout] at hstep
              by_cases hvalid : value < S31.modulus ∧ id = values.length ∧
                  values[lhs]? = some (active hn (wire left)) ∧
                  outAddr = left ∧ (if multiply then value = 1 else value = 0)
              · simp [hvalid] at hstep
                rcases hvalid with ⟨hcanonical, hid, hleftValue, halias, hidentity⟩
                subst outAddr
                subst output
                refine .constantValue values id lhs value multiply left left
                  hcanonical hleft hout hleftValue ?_ hid
                cases multiply with
                | false =>
                    simp at hidentity
                    subst value
                    simp
                | true =>
                    simp at hidentity
                    subst value
                    simp
              · simp [hvalid] at hstep
  | binary id lhs rhs op =>
      unfold checkOwnedStep at hstep
      cases hleft : addresses[lhs]? with
      | none => simp [hleft] at hstep
      | some left =>
          cases hright : addresses[rhs]? with
          | none => simp [hleft, hright] at hstep
          | some right =>
              cases hout : addresses[id]? with
              | none => simp [hleft, hright, hout] at hstep
              | some outAddr =>
                  simp only [hleft, hright, hout] at hstep
                  split_ifs at hstep with hvalid
                  · have houtput : active hn (wire outAddr) = output :=
                      Option.some.inj hstep
                    rcases hvalid with ⟨hid, hleftValue, hrightValue, howner⟩
                    subst output
                    exact .binaryValue values id lhs rhs op left right outAddr
                      hleft hright hout hleftValue hrightValue
                      (direct_owner_air_sound hn wire gates op left right
                        outAddr howner hair) hid

/-- Binary steps have a direct owning native gate. Identity erasures have the
same source and destination wire address, with no native gate required. -/
def checkOwnedSteps {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat) :
    List (Lanes n) → List EffectStep → Option (List (Lanes n))
  | values, [] => some values
  | values, step :: rest => do
      let output ← checkOwnedStep hn wire gates addresses values step
      checkOwnedSteps hn wire gates addresses (values ++ [output]) rest

theorem checkOwnedSteps_air_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (initial final : List (Lanes n)) (steps : List EffectStep)
    (hair : NativeAirRows wire gates)
    (hsteps : checkOwnedSteps hn wire gates addresses initial steps = some final) :
    NativeTrace hn wire gates addresses initial steps final := by
  induction steps generalizing initial with
  | nil =>
      simp only [checkOwnedSteps, Option.some.injEq] at hsteps
      subst final
      exact .done initial
  | cons step rest ih =>
      simp only [checkOwnedSteps] at hsteps
      cases hstep : checkOwnedStep hn wire gates addresses initial step with
      | none => simp [hstep] at hsteps
      | some output =>
          simp [hstep] at hsteps
          exact .next
            (checkOwnedStep_air_sound hn wire gates addresses initial step
              output hair hstep)
            (ih (initial ++ [output]) hsteps)

/-- Source bytes and canonical SSA certificate are joined to the decoded
native graph. Binary source equations follow from owning native AIR residuals;
zero/one identities follow from exact address aliases and M31 field laws.
The graph bytes and AIR rows remain supplied premises until exporter
provenance and committed-cell authentication are proved. -/
theorem checked_direct_owned_source_air_sound {n : Nat} (hn : n ≤ 4)
    (sourceBytes : List Nat) (certificateBytes graphBytes : String)
    (ssa : EmittedSSA) (meaning : Source) (certificate : Certificate)
    (graph : ExportedGraph) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (hsource : GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate
      sourceBytes certificateBytes = .ok (ssa, meaning, certificate))
    (hgraph : decodeExportedGraph graphBytes = .ok graph)
    (hnames : graph.sourceNames = ssa.names)
    (hlanes : ssa.lane_count = n)
    (hports : checkInputPorts hn graph.wire graph.addresses
      certificate.inputs inputs = true)
    (howned : checkOwnedSteps hn graph.wire graph.gates graph.addresses
      (nativeInitial hn graph.wire graph.addresses certificate.inputs)
      certificate.steps = some final)
    (houtput : checkOutputPort hn graph.wire graph.addresses final
      certificate.output claimed = true)
    (hassert : checkAssertions final certificate.assertions = true)
    (hair : NativeAirRows graph.wire graph.gates) :
    GeneralLinearSSAEffectsSourceBytes.denotation sourceBytes inputs claimed ∧
      decodeExportedGraph graphBytes = .ok graph ∧
      graph.sourceNames = ssa.names := by
  refine ⟨?_, hgraph, hnames⟩
  obtain ⟨hparse, _, hmeaning, hssa⟩ :=
    GeneralLinearSSAEffectsSourceBytes.checked_source_parts sourceBytes
      certificateBytes ssa meaning certificate hsource
  refine ⟨ssa, meaning, hparse, hmeaning, ?_⟩
  exact checked_native_trace_sound hn ssa meaning certificate inputs claimed
    final graph.wire graph.gates graph.addresses hssa hlanes hports
    (checkOwnedSteps_air_sound hn graph.wire graph.gates graph.addresses
      (nativeInitial hn graph.wire graph.addresses certificate.inputs)
      final certificate.steps hair howned) houtput hassert

end S31.Functional.Correspondence.StructuralNativeGateOwnership
