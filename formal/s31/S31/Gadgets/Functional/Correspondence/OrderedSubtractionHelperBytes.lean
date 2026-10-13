import S31.Gadgets.Functional.Correspondence.OrderedSubtractionBytes

/-!
An exact byte parser for one pure, statically called binary array helper.
The helper has zero to fifteen arithmetic `let` bindings and one final
binary expression; the circuit calls it once on its public four-lane input.
Parameter references are resolved through that call before the direct-Gate
instruction list is constructed. This models static inlining with no helper
gate or runtime call frame. General S31 functions and closures are outside
this bounded grammar.
-/

namespace S31.Functional.Correspondence.OrderedSubtractionHelperBytes

open S31.Functional.SSATextBytes
open S31.Functional.Correspondence.OrderedSubtractionBytes

structure State where
  remaining : List Token
  names : List Token
  values : List Nat
  expressions : List (OrderedSubtractionBytes.Op × Nat × Nat)
  instructions : List Instruction

def resolve (name : Token) (state : State) : Option Nat := do
  let index ← findName name state.names
  state.values[index]?

def parseLet (state : State) : Option State := do
  let rest ← expect (token "let") state.remaining
  let (name, rest) ← SourceFunctionBytes.takeIdent rest
  if state.names.contains name then none else
  let rest ← expect (token "=") rest
  let (left, rest) ← SourceFunctionBytes.takeIdent rest
  let (op, rest) ← SourceFunctionBytes.takeOp rest
  let (right, rest) ← SourceFunctionBytes.takeIdent rest
  let rest ← expect (token ";") rest
  let lhs ← resolve left state
  let rhs ← resolve right state
  if op != .sub && lhs > rhs then none else
  let expression := (op, lhs, rhs)
  if state.expressions.contains expression then none else
  let id := state.instructions.length + 1
  let instruction : Instruction := { id, lhs, rhs, op }
  return { remaining := rest,
           names := state.names ++ [name],
           values := state.values ++ [id],
           expressions := state.expressions ++ [expression],
           instructions := state.instructions ++ [instruction] }

def parseLetsFuel : Nat → State → Option State
  | 0, state =>
      if state.remaining.head? == some (token "let") then none else some state
  | fuel + 1, state =>
      if state.remaining.head? == some (token "let") then do
        let next ← parseLet state
        parseLetsFuel fuel next
      else some state

/-- The generated `_s31_i1_N` names are the reviewed v1 static-inlining
convention for intermediate helper operations. The final expression receives
the public circuit result name, so it needs no temporary wire. -/
def intermediateName (id : Nat) : Token :=
  token ("_s31_i1_" ++ toString id)

def parseBytes (bytes : List Nat) : Option OrderedSubtractionBytes.Parsed := do
  if bytes.length > 16384 || !(bytes.all (fun byte => byte < 128)) then none else
  let tokens ← lex bytes
  if tokens.length > 256 then none else
  let rest ← expect (token "fn") tokens
  let (helperName, rest) ← SourceFunctionBytes.takeIdent rest
  let rest ← expect (token "(") rest
  let (paramFirst, rest) ← SourceFunctionBytes.takeIdent rest
  let rest ← expect (token ":") rest
  let rest ← SourceFunctionBytes.takeSameLength 4 rest
  let rest ← expect (token ",") rest
  let (paramSecond, rest) ← SourceFunctionBytes.takeIdent rest
  if paramFirst == paramSecond || helperName == paramFirst ||
      helperName == paramSecond then none else
  let rest ← expect (token ":") rest
  let rest ← SourceFunctionBytes.takeSameLength 4 rest
  let rest ← expectMany [token ")", token "->"] rest
  let rest ← SourceFunctionBytes.takeSameLength 4 rest
  let rest ← expect (token "{") rest
  let state ← parseLetsFuel 15 {
    remaining := rest, names := [paramFirst, paramSecond],
    values := [0, 0], expressions := [], instructions := [] }
  let (lastLeft, rest) ← SourceFunctionBytes.takeIdent state.remaining
  let (lastOp, rest) ← SourceFunctionBytes.takeOp rest
  let (lastRight, rest) ← SourceFunctionBytes.takeIdent rest
  let lhs ← resolve lastLeft state
  let rhs ← resolve lastRight state
  if lastOp != .sub && lhs > rhs then none else
  if state.expressions.contains (lastOp, lhs, rhs) then none else
  let rest ← expect (token "}") rest
  let rest ← expect (token "circuit") rest
  let (circuitName, rest) ← SourceFunctionBytes.takeIdent rest
  if helperName == circuitName then none else
  let rest ← expectMany [token "(", token "public"] rest
  let (inputName, rest) ← SourceFunctionBytes.takeIdent rest
  let rest ← expect (token ":") rest
  let rest ← SourceFunctionBytes.takeSameLength 4 rest
  let rest ← expectMany [token ")", token "->", token "public"] rest
  let rest ← SourceFunctionBytes.takeSameLength 4 rest
  let rest ← expectMany [token "{", token "let"] rest
  let (outputName, rest) ← SourceFunctionBytes.takeIdent rest
  if outputName == inputName then none else
  let rest ← expect (token "=") rest
  let rest ← expect helperName rest
  let rest ← expect (token "(") rest
  let (callFirst, rest) ← SourceFunctionBytes.takeIdent rest
  let rest ← expect (token ",") rest
  let (callSecond, rest) ← SourceFunctionBytes.takeIdent rest
  if callFirst != inputName || callSecond != inputName then none else
  let rest ← expectMany [token ")", token ";", outputName, token "}"] rest
  if !rest.isEmpty then none else
  let finalId := state.instructions.length + 1
  let final : Instruction := { id := finalId, lhs, rhs, op := lastOp }
  let intermediates :=
    (List.range state.instructions.length).map intermediateName
  if intermediates.contains inputName || intermediates.contains outputName then none else
  return { circuitName, inputName, outputName,
           wireNames := [inputName] ++ intermediates ++ [outputName],
           instructions := state.instructions ++ [final], output := finalId }

def denotation (bytes : List Nat) (input : Lanes) : Option Lanes := do
  let parsed ← parseBytes bytes
  OrderedSubtractionBytes.execute parsed input

def checkRelation (sourceBytes normalizedBytes : List Nat) :
    Option OrderedSubtractionBytes.Parsed := do
  let parsed ← parseBytes sourceBytes
  let expected ← OrderedSubtractionBytes.encodeNormalized parsed
  if expected != normalizedBytes then none else some parsed

theorem checked_relation_bytes (sourceBytes normalizedBytes : List Nat)
    (parsed : OrderedSubtractionBytes.Parsed)
    (h : checkRelation sourceBytes normalizedBytes = some parsed) :
    parseBytes sourceBytes = some parsed ∧
      OrderedSubtractionBytes.encodeNormalized parsed = some normalizedBytes := by
  unfold checkRelation at h
  cases hs : parseBytes sourceBytes with
  | none => simp [hs] at h
  | some found =>
      cases he : OrderedSubtractionBytes.encodeNormalized found with
      | none => simp [hs, he] at h
      | some expected =>
          by_cases hsame : expected = normalizedBytes
          · have hp : found = parsed := by simpa [hs, he, hsame] using h
            subst parsed
            exact ⟨rfl, by simpa [hsame] using he⟩
          · simp [hs, he, hsame] at h

/-- Any accepted packed rows for the statically inlined helper force the
meaning of its source bytes. Coherent wire reads are explicit premises of
`Accepts`; native opening authentication is not inferred. -/
theorem checked_air_sound (sourceBytes normalizedBytes : List Nat)
    (parsed : OrderedSubtractionBytes.Parsed) (input claim : Lanes)
    (final : List Lanes) (tailA tailB : Tail)
    (hbytes : checkRelation sourceBytes normalizedBytes = some parsed)
    (hrows : Accepts tailA tailB [input] parsed.instructions final)
    (houtput : final[parsed.output]? = some claim) :
    denotation sourceBytes input = some claim := by
  obtain ⟨hsource, _⟩ := checked_relation_bytes sourceBytes normalizedBytes parsed hbytes
  simp [denotation, hsource, OrderedSubtractionBytes.execute,
        OrderedSubtractionBytes.accepts_execute tailA tailB [input] final
          parsed.instructions hrows, houtput]

end S31.Functional.Correspondence.OrderedSubtractionHelperBytes
