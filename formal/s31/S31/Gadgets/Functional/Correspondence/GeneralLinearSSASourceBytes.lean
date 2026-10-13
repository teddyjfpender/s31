import S31.Gadgets.Functional.Correspondence.GeneralLinearSSABytes
import S31.Gadgets.Functional.Correspondence.SourceFunctionBytes

/-!
An independent Lean parser for the plain, pure M31 array fragment of S31.
It consumes the actual ASCII source bytes and derives the same positional
SSA fields that `GeneralLinearSSABytes` decodes from a compiler certificate.
The accepted syntax is one circuit with 1–4 public/private inputs, equal
1–8 lane shapes, 1–16 binary `let` statements, and one named output. ASCII
whitespace and comments are allowed. Standard-library imports, function calls,
aliases, literals, assertions, and parenthesized expressions are outside this
parser's grammar. All source tokens, names, references, and trailing bytes
are checked; this is a conservative subset of the Python source checker. The
circuit identifier's spelling is validated but cannot be compared to this
certificate because its SSA field set does not include the circuit name.

The combined checker compares independently parsed source SSA with all of
the certificate's decoded SSA fields. Its theorem binds packed-row soundness
to the denotation of those supplied source bytes. It does not prove that the
production Python parser or Zig emitter implements this parser, or that a
native proof implies the modeled `AcceptsTrace` premise.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSASourceBytes

open S31.Functional.SSATextBytes
open S31.Functional.Correspondence.SourceFunctionBytes
open S31.Functional.Correspondence.GeneralLinearSSA
open S31.Functional.Correspondence.GeneralLinearSSABytes

private def nameString (name : Token) : String :=
  String.ofList (name.map Char.ofNat)

private def takeVisibility : List Token → Option (String × List Token)
  | head :: rest =>
      if head == token "public" then some ("public", rest)
      else if head == token "private" then some ("private", rest)
      else none
  | [] => none

private def parseOneInput (expectedLength : Option Nat)
    (inputs : List EmittedInput) (names : List Token)
    (remaining : List Token) :
    Option (Nat × List EmittedInput × List Token × List Token) := do
  let (visibility, rest) ← takeVisibility remaining
  let (name, rest) ← takeIdent rest
  if names.contains name then none else
  let rest ← expect (token ":") rest
  let (length, rest) ← takeLength rest
  if let some expected := expectedLength then
    if length != expected then none else pure ()
  let input : EmittedInput :=
    { id := inputs.length, name := nameString name, visibility }
  return (length, inputs ++ [input], names ++ [name], rest)

private def parseMoreInputs : Nat → Nat → List EmittedInput →
    List Token → List Token →
    Option (Nat × List EmittedInput × List Token × List Token)
  | 0, _, _, _, _ => none
  | fuel + 1, length, inputs, names, remaining => do
      if remaining.head? == some (token ",") then
        let rest ← expect (token ",") remaining
        let (length, inputs, names, rest) ←
          parseOneInput (some length) inputs names rest
        parseMoreInputs fuel length inputs names rest
      else
        let rest ← expect (token ")") remaining
        return (length, inputs, names, rest)

private structure State where
  remaining : List Token
  names : List Token
  nodes : List EmittedNode

private def parseLet (state : State) : Option State := do
  let rest ← expect (token "let") state.remaining
  let (name, rest) ← takeIdent rest
  if state.names.contains name then none else
  let rest ← expect (token "=") rest
  let (left, rest) ← takeIdent rest
  let (op, rest) ← takeOp rest
  let (right, rest) ← takeIdent rest
  let rest ← expect (token ";") rest
  let lhs ← findName left state.names
  let rhs ← findName right state.names
  let opName := match op with
    | .add => "add" | .sub => "sub" | .mul => "mul"
  let node : EmittedNode :=
    { id := state.names.length, name := nameString name,
      op := opName, lhs, rhs }
  let next : State :=
    { remaining := rest, names := state.names ++ [name],
      nodes := state.nodes ++ [node] }
  return next

private def parseLets : Nat → State → Option State
  | 0, state =>
      if state.remaining.head? == some (token "let") then none else some state
  | fuel + 1, state =>
      if state.remaining.head? == some (token "let") then do
        parseLets fuel (← parseLet state)
      else some state

/-- The source parser enforces every positional ID by construction and checks
the public ABI word count before returning its complete pure SSA projection. -/
def parseSource (bytes : List Nat) : Option EmittedSSA := do
  if bytes.length > 16384 || !bytes.all (· < 128) then none else
  let tokens ← lex bytes
  if tokens.length > 512 then none else
  let rest ← expect (token "circuit") tokens
  let (_, rest) ← takeIdent rest
  let rest ← expect (token "(") rest
  let (length, inputs, names, rest) ← parseOneInput none [] [] rest
  let (length, inputs, names, rest) ←
    parseMoreInputs 4 length inputs names rest
  let rest ← expectMany [token "->", token "public"] rest
  let rest ← takeSameLength length rest
  if length * (1 + (inputs.filter (·.visibility == "public")).length) > 8 then none else
  let rest ← expect (token "{") rest
  let state ← parseLets 16 { remaining := rest, names, nodes := [] }
  if state.nodes.isEmpty then none else
  let (outputName, rest) ← takeIdent state.remaining
  let rest ← if rest.head? == some (token ";") then
    expect (token ";") rest else some rest
  let rest ← expect (token "}") rest
  if !rest.isEmpty then none else
  let output ← findName outputName state.names
  let ssa : EmittedSSA :=
    { lane_count := length, inputs := inputs, nodes := state.nodes,
      assertions := [], output := output }
  return ssa

/-- Return the circuit identifier from the same complete bounded source
grammar used for the SSA projection. The certificate itself omits this name. -/
def parseSourceName (bytes : List Nat) : Option String := do
  let _ ← parseSource bytes
  let tokens ← lex bytes
  let rest ← expect (token "circuit") tokens
  let (name, _) ← takeIdent rest
  return nameString name

/-- The meaning of source bytes is the term obtained by independently
parsing every pure statement and resolving its positional references. -/
def sourceTerm (ssa : EmittedSSA) : Option Term := do
  let certificate ← ssa.decode
  let terms ← certificate.instructions.foldlM checkStep
    (initialTerms certificate.inputs)
  terms[certificate.output]?

def denotation (source : List Nat) (inputs : Nat → Lanes n) :
    Option (Lanes n) := do
  let ssa ← parseSource source
  let meaning ← sourceTerm ssa
  return meaning.eval inputs

/-- Check actual source bytes against *every* SSA field in canonical emitted
certificate bytes; no caller-supplied source term is trusted. -/
def checkSourceCertificate (source : List Nat) (certificateBytes : String) :
    Except String (EmittedSSA × Term × Certificate) :=
  if certificateBytes.utf8ByteSize > 65536 then
    .error "certificate exceeds byte bound"
  else match parseSource source with
  | none => .error "source outside pure text grammar"
  | some sourceSSA =>
      match decodeCertificate certificateBytes with
      | .error error => .error error
      | .ok emittedSSA =>
          if emittedSSA = sourceSSA then
            match sourceTerm sourceSSA with
            | none => .error "source SSA has no term"
            | some meaning =>
                match checkEmittedSSA emittedSSA meaning with
                | none => .error "certificate SSA does not check against source term"
                | some certificate => .ok (emittedSSA, meaning, certificate)
          else .error "certificate SSA differs from independently parsed source bytes"

theorem checked_source_parts (source : List Nat) (certificateBytes : String)
    (ssa : EmittedSSA) (meaning : Term) (certificate : Certificate)
    (h : checkSourceCertificate source certificateBytes =
      .ok (ssa, meaning, certificate)) :
    parseSource source = some ssa ∧
    decodeCertificate certificateBytes = .ok ssa ∧
    sourceTerm ssa = some meaning ∧
    checkEmittedSSA ssa meaning = some certificate := by
  unfold checkSourceCertificate at h
  by_cases hbound : 65536 < certificateBytes.utf8ByteSize
  · simp [hbound] at h
  · simp only [if_neg hbound] at h
    cases hsource : parseSource source with
    | none => simp [hsource] at h
    | some parsed =>
        cases hdecode : decodeCertificate certificateBytes with
        | error error => simp [hsource, hdecode] at h
        | ok emitted =>
            by_cases heq : emitted = parsed
            · subst emitted
              cases hterm : sourceTerm parsed with
              | none => simp [hsource, hdecode, hterm] at h
              | some term =>
                  cases hcheck : checkEmittedSSA parsed term with
                  | none => simp [hsource, hdecode, hterm, hcheck] at h
                  | some checked =>
                      have hp : (parsed, term, checked) =
                          (ssa, meaning, certificate) := by
                        simpa [hsource, hdecode, hterm, hcheck] using h
                      have hssa : parsed = ssa := congrArg Prod.fst hp
                      have hmeaning : term = meaning := by
                        exact congrArg (fun triple => triple.2.1) hp
                      have hcertificate : checked = certificate := by
                        exact congrArg (fun triple => triple.2.2) hp
                      subst ssa
                      subst meaning
                      subst certificate
                      exact ⟨rfl, rfl, hterm, hcheck⟩
            · simp [hsource, hdecode, heq] at h

/-- Source bytes and emitted certificate bytes determine the same public
result for any complete modeled packed-row witness and any input assignment. -/
theorem checked_source_air_sound (source : List Nat)
    (certificateBytes : String) (ssa : EmittedSSA) (meaning : Term)
    (certificate : Certificate) (inputs : Nat → Lanes ssa.lane_count)
    (claimed : Lanes ssa.lane_count) (final : List (Lanes ssa.lane_count))
    (hcheck : checkSourceCertificate source certificateBytes =
      .ok (ssa, meaning, certificate))
    (hrows : AcceptsTrace (initialValues certificate.inputs inputs)
      certificate.instructions final)
    (houtput : final[certificate.output]? = some claimed) :
    denotation source inputs = some claimed := by
  obtain ⟨hsource, _, hterm, hssa⟩ :=
    checked_source_parts source certificateBytes ssa meaning certificate hcheck
  have hvalue := emitted_ssa_air_sound ssa meaning certificate inputs
    claimed final hssa hrows houtput
  simp [denotation, hsource, hterm, hvalue]

end S31.Functional.Correspondence.GeneralLinearSSASourceBytes
