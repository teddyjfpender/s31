import S31.Gadgets.Functional.Correspondence.StructuralNativeGateCertificate
import S31.Gadgets.Functional.Correspondence.GeneralLinearSSABytes
import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes

/-!
An executable, value-level decoder for a supplied structural native Gate
graph. The source certificate supplies the checked `EffectStep` roster;
`addresses` and `wire` are the graph's source-to-wire map and four-coordinate
value table. Every source step checks its addressed operands, fresh output ID,
canonical literal, and exact active-lane result before extending the trace.
The gate roster is checked separately over all four physical coordinates.

The Lean decoder parses the exact graph JSON's direct-Gate projection. It
does not prove that supplied bytes were emitted by the installed Zig compiler,
or that parsed addresses, gates, and values are the committed AIR witness.
Compiler ownership, public packing, and AIR authentication remain separate
premises. This module constructs the `NativeTrace` required by the existing
structural source theorem for any supplied step count.
-/

namespace S31.Functional.Correspondence.StructuralNativeTraceDecoder

open S31
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)
open S31.Functional.Correspondence.GeneralLinearSSAEffects
open S31.Functional.Correspondence.StructuralNativeGateCertificate
open S31.Functional.Correspondence.GeneralLinearSSABytes
  (Parse fields field string nat array exactString)
open Lean

private def constantResult {n : Nat} (multiply : Bool)
    (left : Lanes n) (value : Nat) : Lanes n :=
  if multiply then
    (fun i => left i * RiscvRefinement.M31.reduce value)
  else (fun i => left i + RiscvRefinement.M31.reduce value)

/-- Consume one source step against the concrete source-to-wire addresses.
The test is semantic: a compiler-erased alias or constant fold can pass when
its native output wire has exactly the source result. -/
def checkNativeStep {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (addresses : List Nat)
    (values : List (Lanes n)) (step : EffectStep) : Option (Lanes n) :=
  match step with
  | .binary id lhs rhs op =>
      match addresses[lhs]?, addresses[rhs]?, addresses[id]? with
      | some left, some right, some outAddr =>
          let output := active hn (wire outAddr)
          if id = values.length ∧
              values[lhs]? = some (active hn (wire left)) ∧
              values[rhs]? = some (active hn (wire right)) ∧
              output = (fun i => op.eval
                (active hn (wire left) i) (active hn (wire right) i)) then
            some output
          else none
      | _, _, _ => none
  | .constant id lhs value multiply =>
      match addresses[lhs]?, addresses[id]? with
      | some left, some outAddr =>
          let output := active hn (wire outAddr)
          if value < S31.modulus ∧ id = values.length ∧
              values[lhs]? = some (active hn (wire left)) ∧
              output = constantResult multiply (active hn (wire left)) value then
            some output
          else none
      | _, _ => none

theorem checkNativeStep_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (values : List (Lanes n)) (step : EffectStep) (output : Lanes n)
    (accepted : checkNativeStep hn wire addresses values step = some output) :
    StepEvidence hn wire gates addresses values step output := by
  cases step with
  | binary id lhs rhs op =>
      unfold checkNativeStep at accepted
      cases hleft : addresses[lhs]? with
      | none => simp [hleft] at accepted
      | some left =>
          cases hright : addresses[rhs]? with
          | none => simp [hleft, hright] at accepted
          | some right =>
              cases hout : addresses[id]? with
              | none => simp [hleft, hright, hout] at accepted
              | some outAddr =>
                  simp only [hleft, hright, hout] at accepted
                  split_ifs at accepted with hvalid
                  · have houtput : active hn (wire outAddr) = output :=
                      Option.some.inj accepted
                    rcases hvalid with ⟨hid, hleftValue, hrightValue, heq⟩
                    subst output
                    exact .binaryValue values id lhs rhs op left right outAddr
                      hleft hright hout hleftValue hrightValue heq hid
  | constant id lhs value multiply =>
      unfold checkNativeStep at accepted
      cases hleft : addresses[lhs]? with
      | none => simp [hleft] at accepted
      | some left =>
          cases hout : addresses[id]? with
          | none => simp [hleft, hout] at accepted
          | some outAddr =>
              simp only [hleft, hout] at accepted
              split_ifs at accepted with hvalid
              · have houtput : active hn (wire outAddr) = output :=
                  Option.some.inj accepted
                rcases hvalid with ⟨hcanonical, hid, hleftValue, heq⟩
                subst output
                exact .constantValue values id lhs value multiply left outAddr
                  hcanonical hleft hout hleftValue heq hid

/-- Decode the complete source step list. Every accepted step appends one
source value, including steps whose native graph output aliases an older
wire. -/
def checkNativeSteps {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (addresses : List Nat) :
    List (Lanes n) → List EffectStep → Option (List (Lanes n))
  | values, [] => some values
  | values, step :: rest => do
      let output ← checkNativeStep hn wire addresses values step
      checkNativeSteps hn wire addresses (values ++ [output]) rest

theorem checkNativeSteps_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (initial final : List (Lanes n)) (steps : List EffectStep)
    (accepted : checkNativeSteps hn wire addresses initial steps = some final) :
    NativeTrace hn wire gates addresses initial steps final := by
  induction steps generalizing initial with
  | nil =>
      simp only [checkNativeSteps, Option.some.injEq] at accepted
      subst final
      exact .done initial
  | cons step rest ih =>
      simp only [checkNativeSteps] at accepted
      cases hstep : checkNativeStep hn wire addresses initial step with
      | none => simp [hstep] at accepted
      | some output =>
          simp [hstep] at accepted
          exact .next
            (checkNativeStep_sound hn wire gates addresses initial step output hstep)
            (ih (initial ++ [output]) accepted)

/-- A checked structural trace includes all four-coordinate gate equations
and produces the exact `NativeTrace` premise of `checked_native_trace_sound`.
The `checkNativeSteps` proof itself uses source value equations, so it also
accepts justified compiler erasures. -/
def checkStructuralTrace {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (initial : List (Lanes n)) (steps : List EffectStep) :
    Option (List (Lanes n)) := do
  if checkGates wire gates then
    checkNativeSteps hn wire addresses initial steps
  else none

theorem checkStructuralTrace_sound {n : Nat} (hn : n ≤ 4)
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (initial final : List (Lanes n)) (steps : List EffectStep)
    (accepted : checkStructuralTrace hn wire gates addresses initial steps =
      some final) :
    checkGates wire gates = true ∧
      NativeTrace hn wire gates addresses initial steps final := by
  unfold checkStructuralTrace at accepted
  by_cases hgate : checkGates wire gates = true
  · have hsteps : checkNativeSteps hn wire addresses initial steps = some final := by
      simpa [hgate] using accepted
    exact ⟨hgate,
      checkNativeSteps_sound hn wire gates addresses initial final steps hsteps⟩
  · simp [hgate] at accepted

/-- Replace the manually supplied `NativeTrace` premise with a computable
check of the supplied graph values and source step list. This still assumes
the source certificate was accepted, the graph ports and public result match,
and the graph itself is the native committed witness. -/
theorem checked_structural_trace_sound {n : Nat} (hn : n ≤ 4)
    (ssa : EmittedSSA) (source : Source)
    (certificate : Certificate) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (wire : Nat → Quad) (gates : List Gate) (addresses : List Nat)
    (hcheck : checkEmittedSSA ssa source = some certificate)
    (hlanes : ssa.lane_count = n)
    (hports : checkInputPorts hn wire addresses certificate.inputs inputs = true)
    (hdecoded : checkStructuralTrace hn wire gates addresses
      (nativeInitial hn wire addresses certificate.inputs)
      certificate.steps = some final)
    (houtput : checkOutputPort hn wire addresses final
      certificate.output claimed = true)
    (hassert : checkAssertions final certificate.assertions = true) :
    source.accepts inputs claimed := by
  have htrace := (checkStructuralTrace_sound hn wire gates addresses
    (nativeInitial hn wire addresses certificate.inputs) final certificate.steps
    hdecoded).2
  exact checked_native_trace_sound hn ssa source certificate inputs claimed
    final wire gates addresses hcheck hlanes hports htrace houtput hassert

/-- The value/address/Gate projection decoded from the native graph JSON.
The parser validates the full top-level field roster and the source-to-canonical
address chain. Full QM31 multiplication, Eq, input conversion, finalization,
and padded rows remain the independent graph audit's responsibility. -/
structure ExportedGraph where
  values : List Quad
  sourceNames : List String
  addresses : List Nat
  gates : List Gate

def ExportedGraph.wire (graph : ExportedGraph) (addr : Nat) : Quad :=
  (graph.values[addr]?).getD (fun _ => 0)

private def graphFields : List String :=
  ["schema", "n_vars", "values", "add", "sub", "mul", "pointwise_mul",
   "eq", "triple_xor", "m31_to_u32", "blake_g_gate", "permutation_ends",
   "permutation_inputs", "permutation_outputs", "output", "constant_keys",
   "constant_vars", "source_map", "canonical_nodes", "node_wires",
   "node_spans", "assertion_spans", "bindings", "finalization", "padded"]

private def parseQuad (json : Json) : Parse Quad := do
  let words ← array nat json
  if words.length != 4 || words.any (· ≥ S31.modulus) then
    throw "native graph value is not four canonical M31 coordinates"
  return fun i => RiscvRefinement.M31.reduce (words[i.val]?.getD 0)

private def parseGate (op : GateOp) (count : Nat) (json : Json) : Parse Gate := do
  fields json ["in0", "in1", "out"]
  let in0 ← nat (← field json "in0")
  let in1 ← nat (← field json "in1")
  let out ← nat (← field json "out")
  if in0 ≥ count || in1 ≥ count || out ≥ count then
    throw "native source gate address is out of range"
  return { op, in0, in1, out }

private def parseSourceMap (json : Json) : Parse (String × Nat) := do
  fields json ["name", "id"]
  let name ← string (← field json "name")
  let id ← nat (← field json "id")
  return (name, id)

private def parseCanonicalWire (index count : Nat) (json : Json) : Parse Nat := do
  fields json ["id", "wires"]
  let id ← nat (← field json "id")
  let wires ← array nat (← field json "wires")
  match wires with
  | [addr] =>
      if id != index || addr ≥ count then
        throw "native canonical wire address differs or is out of range"
      return addr
  | _ => throw "native canonical node must have one packed wire"

/-- Bounded Lean decoding of the exact exported graph schema's source Gate
projection. Missing or extra top-level keys, noncanonical M31 words, malformed
source/canonical mappings, and out-of-range gate addresses fail closed. The
8 MiB limit matches the local exporter's size cap. -/
def decodeExportedGraph (bytes : String) : Parse ExportedGraph := do
  if bytes.utf8ByteSize > 8 * 1024 * 1024 then
    throw "native structural graph exceeds 8 MiB"
  let json ← Json.parse bytes
  fields json graphFields
  for name in graphFields do
    let _ ← field json name
  exactString (← field json "schema") "s31-structural-m31-exact-native-graph-v2"
  let count ← nat (← field json "n_vars")
  if count == 0 || count > 262144 then
    throw "native variable count exceeds bounded profile"
  let values ← array parseQuad (← field json "values")
  if values.length != count then throw "native value count differs"
  let sourceMap ← array parseSourceMap (← field json "source_map")
  let sourceNames := sourceMap.map Prod.fst
  let rawWires ← array (fun item => pure item) (← field json "node_wires")
  let canonicalWires ← rawWires.zipIdx.mapM fun (item, index) =>
    parseCanonicalWire index count item
  let addresses ← sourceMap.mapM fun (_, id) =>
    match canonicalWires[id]? with
    | some addr => .ok addr
    | none => .error "source node lacks canonical packed wire"
  let add ← array (parseGate .add count) (← field json "add")
  let sub ← array (parseGate .sub count) (← field json "sub")
  let pointwise ← array (parseGate .pointwiseMul count)
    (← field json "pointwise_mul")
  if add.length + sub.length + pointwise.length > 262144 then
    throw "native source gate roster exceeds bounded profile"
  return { values, sourceNames, addresses, gates := add ++ sub ++ pointwise }

/-- One computable admission gate from the exported JSON bytes to the checked
source trace, input ports, public result, and assertions. It returns the parsed
graph and reconstructed source values for independent inspection. -/
def checkExportedGraph {n : Nat} (hn : n ≤ 4)
    (bytes : String) (certificate : Certificate)
    (inputs : Nat → Lanes n) (claimed : Lanes n) :
    Parse (ExportedGraph × List (Lanes n)) :=
  match decodeExportedGraph bytes with
  | .error error => .error error
  | .ok graph =>
      if graph.addresses.length != certificate.inputs + certificate.steps.length then
        .error "source map length differs from checked SSA"
      else if checkInputPorts hn graph.wire graph.addresses certificate.inputs inputs then
        match checkStructuralTrace hn graph.wire graph.gates graph.addresses
            (nativeInitial hn graph.wire graph.addresses certificate.inputs)
            certificate.steps with
        | none => .error "native structural trace fails"
        | some final =>
            if checkOutputPort hn graph.wire graph.addresses final
                certificate.output claimed then
              if checkAssertions final certificate.assertions then
                .ok (graph, final)
              else .error "native source assertion differs"
            else .error "native public output differs"
      else .error "native input ports differ from source inputs"

/-- Decompose successful decoding into the exact four checks used by the
structural source theorem. -/
theorem checked_exported_graph_components {n : Nat} (hn : n ≤ 4)
    (bytes : String) (graph : ExportedGraph)
    (certificate : Certificate) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (hgraph : checkExportedGraph hn bytes certificate inputs claimed =
      .ok (graph, final)) :
    checkInputPorts hn graph.wire graph.addresses certificate.inputs inputs = true ∧
    checkStructuralTrace hn graph.wire graph.gates graph.addresses
      (nativeInitial hn graph.wire graph.addresses certificate.inputs)
      certificate.steps = some final ∧
    checkOutputPort hn graph.wire graph.addresses final
      certificate.output claimed = true ∧
    checkAssertions final certificate.assertions = true := by
  cases hdecode : decodeExportedGraph bytes with
  | error message => simp [checkExportedGraph, hdecode] at hgraph
  | ok decoded =>
      by_cases hlen : decoded.addresses.length !=
          certificate.inputs + certificate.steps.length
      · simp [checkExportedGraph, hdecode, hlen] at hgraph
      · by_cases hports : checkInputPorts hn decoded.wire decoded.addresses
            certificate.inputs inputs = true
        · cases htrace : checkStructuralTrace hn decoded.wire decoded.gates
              decoded.addresses
              (nativeInitial hn decoded.wire decoded.addresses certificate.inputs)
              certificate.steps with
          | none => simp [checkExportedGraph, hdecode, hlen, hports, htrace] at hgraph
          | some values =>
              by_cases houtput : checkOutputPort hn decoded.wire
                  decoded.addresses values certificate.output claimed = true
              · by_cases hassert : checkAssertions values
                    certificate.assertions = true
                · have heq : (decoded, values) = (graph, final) := by
                    simpa [checkExportedGraph, hdecode, hlen, hports, htrace,
                      houtput, hassert]
                      using hgraph
                  cases Prod.mk.inj heq with
                  | intro hdecoded hvalues =>
                      subst graph
                      subst final
                      exact ⟨hports, htrace, houtput, hassert⟩
                · simp [checkExportedGraph, hdecode, hlen, hports, htrace,
                    houtput, hassert] at hgraph
              · simp [checkExportedGraph, hdecode, hlen, hports, htrace,
                  houtput] at hgraph
        · simp [checkExportedGraph, hdecode, hlen, hports] at hgraph

/-- Successful Lean decoding supplies the actual `NativeTrace` premise for
every admitted source step. This theorem checks concrete values; it does not
authenticate those values or gates to a native proof. -/
theorem checked_exported_graph_trace {n : Nat} (hn : n ≤ 4)
    (bytes : String) (graph : ExportedGraph)
    (certificate : Certificate) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (hgraph : checkExportedGraph hn bytes certificate inputs claimed =
      .ok (graph, final)) :
    NativeTrace hn graph.wire graph.gates graph.addresses
      (nativeInitial hn graph.wire graph.addresses certificate.inputs)
      certificate.steps final := by
  have hchecks := checked_exported_graph_components hn bytes graph
    certificate inputs claimed final hgraph
  exact (checkStructuralTrace_sound hn graph.wire graph.gates graph.addresses
    (nativeInitial hn graph.wire graph.addresses certificate.inputs)
    final certificate.steps hchecks.2.1).2

/-- Successful byte-level projection checking and an accepted source
certificate establish the source result for these concrete input values.
The actual Zig exporter and committed AIR still require an ownership and
verifier refinement proof. -/
theorem checked_exported_graph_sound {n : Nat} (hn : n ≤ 4)
    (bytes : String) (graph : ExportedGraph)
    (ssa : EmittedSSA) (source : Source)
    (certificate : Certificate) (inputs : Nat → Lanes n)
    (claimed : Lanes n) (final : List (Lanes n))
    (hcheck : checkEmittedSSA ssa source = some certificate)
    (hlanes : ssa.lane_count = n)
    (hgraph : checkExportedGraph hn bytes certificate inputs claimed =
      .ok (graph, final)) :
    source.accepts inputs claimed := by
  rcases checked_exported_graph_components hn bytes graph certificate
    inputs claimed final hgraph with ⟨hports, htrace, houtput, hassert⟩
  exact checked_structural_trace_sound hn ssa source certificate inputs
    claimed final graph.wire graph.gates graph.addresses hcheck hlanes
    hports htrace houtput hassert

/-- The complete checked result retains the independently parsed source SSA,
its semantic meaning, and the graph whose source-map names are owned by that
SSA. The bytes themselves remain supplied data, not authenticated proof cells. -/
structure CheckedSourceGraph (n : Nat) where
  ssa : EmittedSSA
  meaning : Source
  certificate : Certificate
  graph : ExportedGraph
  final : List (Lanes n)

/-- One executable join for source text, canonical SSA certificate bytes, and
the supplied native graph projection. The source-map names must occur in the
same order as the independently parsed source's input and node names. -/
def checkSourceNativeGraph {n : Nat} (hn : n ≤ 4)
    (sourceBytes : List Nat) (certificateBytes graphBytes : String)
    (inputs : Nat → Lanes n) (claimed : Lanes n) :
    Parse (CheckedSourceGraph n) :=
  match GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate
      sourceBytes certificateBytes with
  | .error error => .error error
  | .ok (ssa, meaning, certificate) =>
      if n = 0 then .error "native source graph requires at least one lane"
      else if ssa.lane_count = n then
        match checkExportedGraph hn graphBytes certificate inputs claimed with
        | .error error => .error error
        | .ok (graph, final) =>
            if graph.sourceNames = ssa.names then
              .ok { ssa, meaning, certificate, graph, final }
            else .error "native source-map names differ from parsed source SSA"
      else .error "native graph lane count differs from parsed source SSA"

/-- Decomposition is universal in the admitted source step list and 1–4 lane
count. In particular, source-map name ownership is an executable checker
premise rather than an informal assumption. -/
theorem checked_source_native_graph_components {n : Nat} (hn : n ≤ 4)
    (sourceBytes : List Nat) (certificateBytes graphBytes : String)
    (inputs : Nat → Lanes n) (claimed : Lanes n)
    (checked : CheckedSourceGraph n)
    (h : checkSourceNativeGraph hn sourceBytes certificateBytes graphBytes
      inputs claimed = .ok checked) :
    GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate
      sourceBytes certificateBytes =
        .ok (checked.ssa, checked.meaning, checked.certificate) ∧
    0 < n ∧ checked.ssa.lane_count = n ∧
    checkExportedGraph hn graphBytes checked.certificate inputs claimed =
      .ok (checked.graph, checked.final) ∧
    checked.graph.sourceNames = checked.ssa.names := by
  unfold checkSourceNativeGraph at h
  cases hsource : GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate
      sourceBytes certificateBytes with
  | error error => simp [hsource] at h
  | ok parts =>
      obtain ⟨ssa, meaning, certificate⟩ := parts
      by_cases hpositive : n = 0
      · simp [hsource, hpositive] at h
      · by_cases hlanes : ssa.lane_count = n
        · cases hgraph : checkExportedGraph hn graphBytes certificate inputs
              claimed with
          | error error => simp [hsource, hpositive, hlanes, hgraph] at h
          | ok result =>
              obtain ⟨graph, final⟩ := result
              by_cases hnames : graph.sourceNames = ssa.names
              · have heq :
                    ({ ssa, meaning, certificate, graph, final } :
                      CheckedSourceGraph n) = checked := by
                    simpa [hsource, hpositive, hlanes, hgraph, hnames] using h
                subst checked
                exact ⟨rfl, Nat.pos_of_ne_zero hpositive, hlanes,
                  hgraph, hnames⟩
              · simp [hsource, hpositive, hlanes, hgraph, hnames] at h
        · simp [hsource, hpositive, hlanes] at h

/-- Successful checking of all three supplied byte strings proves the
denotation of the parsed S31 source for every admitted step list and 1–4
lanes. This theorem does not assert that Zig emitted `graphBytes`, or that
its wire cells are bound to a proof commitment. -/
theorem checked_source_native_graph_sound {n : Nat} (hn : n ≤ 4)
    (sourceBytes : List Nat) (certificateBytes graphBytes : String)
    (inputs : Nat → Lanes n) (claimed : Lanes n)
    (checked : CheckedSourceGraph n)
    (h : checkSourceNativeGraph hn sourceBytes certificateBytes graphBytes
      inputs claimed = .ok checked) :
    GeneralLinearSSAEffectsSourceBytes.denotation sourceBytes inputs claimed := by
  obtain ⟨hsource, _, hlanes, hgraph, _⟩ :=
    checked_source_native_graph_components hn sourceBytes certificateBytes
      graphBytes inputs claimed checked h
  obtain ⟨hparse, _, hmeaning, hssa⟩ :=
    GeneralLinearSSAEffectsSourceBytes.checked_source_parts sourceBytes
      certificateBytes checked.ssa checked.meaning checked.certificate hsource
  refine ⟨checked.ssa, checked.meaning, hparse, hmeaning, ?_⟩
  exact checked_exported_graph_sound hn graphBytes checked.graph checked.ssa
    checked.meaning checked.certificate inputs claimed checked.final hssa
    hlanes hgraph

private def toyGraph : ExportedGraph :=
  { values := [fun _ => 1, fun _ => 0, fun _ => 1]
    sourceNames := ["x", "y", "z"]
    addresses := [0, 1, 2]
    gates := [{ op := .sub, in0 := 0, in1 := 1, out := 2 }] }

private def toyCertificate : Certificate :=
  { inputs := 2
    steps := [.binary 2 0 1 .sub]
    assertions := []
    output := 2 }

private def toyInputs : Nat → Lanes 1
  | 0 => fun _ => 1
  | _ => fun _ => 0

private def toyClaim : Lanes 1 := fun _ => 1

/-- Ordered subtraction of packed (1,1,1,1) and (0,0,0,0) succeeds. -/
example : checkStructuralTrace (by decide : 1 ≤ 4) toyGraph.wire
    toyGraph.gates toyGraph.addresses
    (nativeInitial (by decide : 1 ≤ 4) toyGraph.wire toyGraph.addresses 2)
    toyCertificate.steps = some [toyInputs 0, toyInputs 1, toyClaim] := by
  decide

/-- Readdressing the source's first input to the zero wire is rejected. -/
example : checkStructuralTrace (by decide : 1 ≤ 4) toyGraph.wire
    toyGraph.gates [1, 1, 2]
    (nativeInitial (by decide : 1 ≤ 4) toyGraph.wire [1, 1, 2] 2)
    toyCertificate.steps = none := by
  decide

/-- Changing the output wire to 2 violates the actual ordered-sub gate. -/
private def changedValueGraph : ExportedGraph :=
  { toyGraph with values := [fun _ => 1, fun _ => 0,
      fun _ => RiscvRefinement.M31.reduce 2] }

example : checkStructuralTrace (by decide : 1 ≤ 4) changedValueGraph.wire
    changedValueGraph.gates changedValueGraph.addresses
    (nativeInitial (by decide : 1 ≤ 4) changedValueGraph.wire
      changedValueGraph.addresses 2) toyCertificate.steps = none := by
  decide

/-- A hand-written JSON fixture for the direct-Gate projection. All required
top-level fields are present, but ignored fields have toy placeholders; this
is not claimed to be a full Zig-emitted graph. -/
private def toyBytes : String := r#"{
  "schema":"s31-structural-m31-exact-native-graph-v2",
  "n_vars":3,
  "values":[[1,1,1,1],[0,0,0,0],[1,1,1,1]],
  "add":[],"sub":[{"in0":0,"in1":1,"out":2}],"mul":[],
  "pointwise_mul":[],"eq":[],"triple_xor":[],"m31_to_u32":[],
  "blake_g_gate":[],"permutation_ends":[],"permutation_inputs":[],
  "permutation_outputs":[],"output":[],"constant_keys":[],
  "constant_vars":[],
  "source_map":[{"name":"x","id":0},{"name":"y","id":1},
    {"name":"z","id":2}],
  "canonical_nodes":[],
  "node_wires":[{"id":0,"wires":[0]},{"id":1,"wires":[1]},
    {"id":2,"wires":[2]}],
  "node_spans":[],"assertion_spans":[],"bindings":[],
  "finalization":[],"padded":[]
}"#

#guard match decodeExportedGraph toyBytes with
  | .ok graph => graph.addresses == [0, 1, 2]
  | .error _ => false

#guard match checkExportedGraph (by decide : 1 ≤ 4) toyBytes toyCertificate
    toyInputs toyClaim with
  | .ok (_, final) => final.length == 3
  | .error _ => false

/-- A malformed source-to-canonical ID cannot be projected to a wire. -/
private def badSourceBytes : String :=
  toyBytes.replace "\"name\":\"z\",\"id\":2" "\"name\":\"z\",\"id\":9"

#guard match decodeExportedGraph badSourceBytes with
  | .error _ => true
  | .ok _ => false

/-- A noncanonical M31 coordinate cannot enter the graph value table. -/
private def badFieldBytes : String :=
  toyBytes.replace "[1,1,1,1]" "[2147483647,1,1,1]"

#guard match decodeExportedGraph badFieldBytes with
  | .error _ => true
  | .ok _ => false

/-- This mutation remains valid JSON and in-range, but readdresses x to y. -/
private def readdressedBytes : String :=
  toyBytes.replace "\"name\":\"x\",\"id\":0" "\"name\":\"x\",\"id\":1"

#guard match decodeExportedGraph readdressedBytes with
  | .ok graph => graph.addresses == [1, 1, 2]
  | .error _ => false

#guard match checkExportedGraph (by decide : 1 ≤ 4)
    readdressedBytes toyCertificate toyInputs toyClaim with
  | .error _ => true
  | .ok _ => false

/-- The changed final value is canonical M31 and parses, but violates the
subtraction gate equation. -/
private def changedOutputBytes : String :=
  toyBytes.replace "[1,1,1,1]]," "[2,2,2,2]],"

#guard match decodeExportedGraph changedOutputBytes with
  | .ok graph => graph.values.length == 3
  | .error _ => false

#guard match checkExportedGraph (by decide : 1 ≤ 4)
    changedOutputBytes toyCertificate toyInputs toyClaim with
  | .error _ => true
  | .ok _ => false

end S31.Functional.Correspondence.StructuralNativeTraceDecoder
