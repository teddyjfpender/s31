import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsBytes
import S31.Gadgets.Functional.Correspondence.SourceFunctionBytes

/-!
An independent byte parser for a bounded effectful S31 circuit. It accepts
binary M31 array arithmetic, canonical `splat<N>(k_m31)` constants, and
interleaved `assert_eq` statements. Every assertion operand must be in scope
at its original textual position. The parsed source determines the exact
indexed effects SSA compared with canonical compiler certificate bytes.

Static helpers, aliases, grouped expressions, and scalar types are outside
this deliberately bounded grammar. The circuit name is syntax-checked but
is absent from the certificate's SSA projection, so this semantic check does
not authenticate its spelling or the source SHA-256 field.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes

open S31.Functional.SSATextBytes
open S31.Functional.Correspondence.SourceFunctionBytes
open S31.Functional.Correspondence.GeneralLinearSSA (Lanes)
open S31.Functional.Correspondence.GeneralLinearSSAEffects

private def nameString (name : Token) : String :=
  String.ofList (name.map Char.ofNat)

/-- Separate lexer so the preexisting pure source grammar is unchanged. It
recognizes `@`, `<`, `>` and suffixed M31 literals in addition to the ordinary
ASCII expression tokens. -/
private def lexFuel : Nat → List Nat → Option (List Token)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, head :: tail =>
      if isSpace head then lexFuel fuel tail
      else if head == 47 then
        match tail with
        | 47 :: afterSlashes =>
            let (_, afterComment) := span (fun b => b != 10) afterSlashes
            lexFuel fuel afterComment
        | _ => none
      else if isNameStart head then do
        let (suffix, rest) := span isNameTail tail
        return (head :: suffix) :: (← lexFuel fuel rest)
      else if isDigit head then do
        let (suffix, rest) := span isNameTail tail
        return (head :: suffix) :: (← lexFuel fuel rest)
      else if head == 45 then
        match tail with
        | 62 :: rest => do return [45, 62] :: (← lexFuel fuel rest)
        | _ => do return [45] :: (← lexFuel fuel tail)
      else if head == 46 then
        match tail with
        | 42 :: rest => do return [46, 42] :: (← lexFuel fuel rest)
        | _ => none
      else if List.contains
          [40, 41, 44, 91, 93, 59, 58, 123, 125, 61, 43, 64, 60, 62] head then
        do return [head] :: (← lexFuel fuel tail)
      else none

private def takeVisibility : List Token → Option (String × List Token)
  | head :: rest =>
      if head == token "public" then some ("public", rest)
      else if head == token "private" then some ("private", rest)
      else none
  | [] => none

private def parseOneInput (expectedLength : Option Nat)
    (inputs : List GeneralLinearSSA.EmittedInput) (names : List Token)
    (remaining : List Token) :
    Option (Nat × List GeneralLinearSSA.EmittedInput × List Token × List Token) := do
  let (visibility, rest) ← takeVisibility remaining
  let (name, rest) ← takeIdent rest
  if names.contains name then none else
  let rest ← expect (token ":") rest
  let (length, rest) ← takeLength rest
  if let some expected := expectedLength then
    if length != expected then none else pure ()
  let input : GeneralLinearSSA.EmittedInput :=
    { id := inputs.length, name := nameString name, visibility }
  return (length, inputs ++ [input], names ++ [name], rest)

private def parseMoreInputs : Nat → Nat →
    List GeneralLinearSSA.EmittedInput → List Token → List Token →
    Option (Nat × List GeneralLinearSSA.EmittedInput × List Token × List Token)
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

private def literal (digits : Token) : Option Nat := do
  let text := nameString digits
  let parts := text.splitOn "_m31"
  match parts with
  | [number, ""] =>
      let value ← number.toNat?
      if toString value != number || value ≥ S31.modulus then none else
      some value
  | _ => none

private inductive Atom where
  | wire (id : Nat)
  | constant (value : Nat)

private def takeAtom (length : Nat) (names : List Token) :
    List Token → Option (Atom × List Token)
  | head :: rest =>
      if head == token "splat" then do
        let rest ← expectMany
          [token "<", token (toString length), token ">", token "("] rest
        match rest with
        | literalToken :: afterLiteral =>
            let value ← literal literalToken
            let rest ← expect (token ")") afterLiteral
            return (.constant value, rest)
        | [] => none
      else do
        let (name, rest) ← takeIdent (head :: rest)
        let id ← findName name names
        return (.wire id, rest)
  | [] => none

private def takeWire (names : List Token) (remaining : List Token) :
    Option (Nat × List Token) := do
  let (name, rest) ← takeIdent remaining
  let id ← findName name names
  return (id, rest)

private structure State where
  remaining : List Token
  names : List Token
  nodes : List EmittedNode
  assertions : List (Nat × Nat)
  seenAssertions : List (Nat × Nat)

private def parseLet (length : Nat) (state : State) : Option State := do
  let rest ← expect (token "let") state.remaining
  let (name, rest) ← takeIdent rest
  if state.names.contains name || state.nodes.length ≥ 16 then none else
  let rest ← expect (token "=") rest
  let (left, rest) ← takeAtom length state.names rest
  let (op, rest) ← takeOp rest
  let (right, rest) ← takeAtom length state.names rest
  let rest ← expect (token ";") rest
  let id := state.names.length
  let node ← match left, right with
    | .wire lhs, .wire rhs =>
        let operation := match op with
          | .add => "add" | .sub => "sub" | .mul => "mul"
        some ({ id := id, name := nameString name, op := operation, lhs := lhs, rhs := some rhs, constant := none } : EmittedNode)
    | .wire lhs, .constant value =>
        let operation := if op == .mul then "mul_const" else "add_const"
        let adjusted := if op == .sub then (S31.modulus - value) % S31.modulus
          else value
        some ({ id := id, name := nameString name, op := operation, lhs := lhs, rhs := none, constant := some adjusted } : EmittedNode)
    | .constant value, .wire lhs =>
        if op == .sub then none else
        let operation := if op == .mul then "mul_const" else "add_const"
        some ({ id := id, name := nameString name, op := operation, lhs := lhs, rhs := none, constant := some value } : EmittedNode)
    | .constant _, .constant _ => none
  let next : State := { state with remaining := rest, names := state.names ++ [name], nodes := state.nodes ++ [node] }
  return next

private def parseAssertion (state : State) : Option State := do
  if state.assertions.length ≥ 16 then none else
  let rest ← expectMany [token "assert_eq", token "("] state.remaining
  let (lhs, rest) ← takeWire state.names rest
  let rest ← expect (token ",") rest
  let (rhs, rest) ← takeWire state.names rest
  let rest ← expectMany [token ")", token ";"] rest
  let ordered := (min lhs rhs, max lhs rhs)
  if state.seenAssertions.contains ordered then none else
  let next : State := { state with remaining := rest, assertions := state.assertions ++ [(lhs, rhs)], seenAssertions := state.seenAssertions ++ [ordered] }
  return next

private def parseStatements : Nat → Nat → State → Option State
  | 0, _, state =>
      if state.remaining.head? == some (token "let") ||
          state.remaining.head? == some (token "assert_eq") then none else some state
  | fuel + 1, length, state =>
      if state.remaining.head? == some (token "let") then do
        let next ← parseLet length state
        parseStatements fuel length next
      else if state.remaining.head? == some (token "assert_eq") then do
        let next ← parseAssertion state
        parseStatements fuel length next
      else some state

/-- The source-side indexed effects graph, including assertions in textual
order. Pure arithmetic references and assertion reads must be in scope. -/
def parseSource (bytes : List Nat) : Option EmittedSSA := do
  if bytes.length > 16384 || !bytes.all (· < 128) then none else
  let tokens ← lexFuel (bytes.length + 1) bytes
  if tokens.length > 512 then none else
  let tokens ← if tokens.head? == some (token "use") then
    expectMany [token "use", token "std", token "@", token "1", token ";"] tokens
    else some tokens
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
  let state ← parseStatements 32 length
    { remaining := rest, names, nodes := [], assertions := [], seenAssertions := [] }
  if state.nodes.isEmpty then none else
  let (outputName, rest) ← takeIdent state.remaining
  let rest ← if rest.head? == some (token ";") then
    expect (token ";") rest else some rest
  let rest ← expect (token "}") rest
  if !rest.isEmpty then none else
  let output ← findName outputName state.names
  let result : EmittedSSA :=
    { lane_count := length, inputs, nodes := state.nodes,
      assertions := state.assertions, output }
  return result

def sourceMeaning (ssa : EmittedSSA) : Option Source := do
  let certificate ← ssa.decode
  let terms ← certificate.steps.foldlM checkStep
    (initialTerms certificate.inputs)
  let output ← terms[certificate.output]?
  let assertions ← resolveAssertions terms certificate.assertions
  return { output, assertions }

/-- The source relation is partial: inputs violating any assertion do not
have an accepted claim. -/
def denotation (source : List Nat) (inputs : Nat → Lanes n)
    (claimed : Lanes n) : Prop :=
  ∃ ssa meaning, parseSource source = some ssa ∧
    sourceMeaning ssa = some meaning ∧ meaning.accepts inputs claimed

def checkSourceCertificate (source : List Nat) (certificateBytes : String) :
    Except String (EmittedSSA × Source × Certificate) :=
  match parseSource source with
  | none => .error "source outside effects text grammar"
  | some sourceSSA =>
      match GeneralLinearSSAEffectsBytes.decodeCertificate certificateBytes with
      | .error error => .error error
      | .ok emittedSSA =>
          if emittedSSA = sourceSSA then
            match sourceMeaning sourceSSA with
            | none => .error "source effects SSA has no meaning"
            | some meaning =>
                match checkEmittedSSA emittedSSA meaning with
                | none => .error "effects SSA does not check against source"
                | some certificate => .ok (emittedSSA, meaning, certificate)
          else .error "effects SSA differs from independently parsed source bytes"

theorem checked_source_parts (source : List Nat) (certificateBytes : String)
    (ssa : EmittedSSA) (meaning : Source) (certificate : Certificate)
    (h : checkSourceCertificate source certificateBytes =
      .ok (ssa, meaning, certificate)) :
    parseSource source = some ssa ∧
    GeneralLinearSSAEffectsBytes.decodeCertificate certificateBytes = .ok ssa ∧
    sourceMeaning ssa = some meaning ∧
    checkEmittedSSA ssa meaning = some certificate := by
  unfold checkSourceCertificate at h
  cases hsource : parseSource source with
  | none => simp [hsource] at h
  | some parsed =>
      cases hdecode : GeneralLinearSSAEffectsBytes.decodeCertificate certificateBytes with
      | error error => simp [hsource, hdecode] at h
      | ok emitted =>
          by_cases heq : emitted = parsed
          · subst emitted
            cases hmeaning : sourceMeaning parsed with
            | none => simp [hsource, hdecode, hmeaning] at h
            | some foundMeaning =>
                cases hcheck : checkEmittedSSA parsed foundMeaning with
                | none => simp [hsource, hdecode, hmeaning, hcheck] at h
                | some checked =>
                    have hp : (parsed, foundMeaning, checked) =
                        (ssa, meaning, certificate) := by
                      simpa [hsource, hdecode, hmeaning, hcheck] using h
                    have hssa : parsed = ssa := congrArg Prod.fst hp
                    have hmeaningEq : foundMeaning = meaning :=
                      congrArg (fun triple => triple.2.1) hp
                    have hcertificate : checked = certificate :=
                      congrArg (fun triple => triple.2.2) hp
                    subst ssa
                    subst meaning
                    subst certificate
                    exact ⟨rfl, rfl, hmeaning, hcheck⟩
          · simp [hsource, hdecode, heq] at h

theorem checked_source_air_sound (source : List Nat)
    (certificateBytes : String) (ssa : EmittedSSA) (meaning : Source)
    (certificate : Certificate) (inputs : Nat → Lanes ssa.lane_count)
    (claimed : Lanes ssa.lane_count) (final : List (Lanes ssa.lane_count))
    (hcheck : checkSourceCertificate source certificateBytes =
      .ok (ssa, meaning, certificate))
    (hrows : AcceptsTrace (initialValues certificate.inputs inputs)
      certificate.steps final)
    (houtput : final[certificate.output]? = some claimed)
    (hassert : assertionsAir final certificate.assertions) :
    denotation source inputs claimed := by
  obtain ⟨hsource, _, hmeaning, hssa⟩ :=
    checked_source_parts source certificateBytes ssa meaning certificate hcheck
  refine ⟨ssa, meaning, hsource, hmeaning, ?_⟩
  exact emitted_ssa_air_sound ssa meaning certificate inputs claimed final
    hssa hrows houtput hassert

end S31.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes
