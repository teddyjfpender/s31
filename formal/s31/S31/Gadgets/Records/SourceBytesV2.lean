import S31.Gadgets.Records.SourceValueV2
import S31.Gadgets.Functional.SSATextBytes

/-!
An exact-byte parser for the bounded width-one M31 nominal-record fragment.
It independently resolves field names and local operands to positional SSA
wires. Successful parsing carries a checked value certificate for every
result field, including aliases and constructor reordering. This does not
decode normalized JSON, prove equivalence to the Python parser, or bind a
native proof opening. Those are separate correspondence boundaries.
-/

namespace S31.Gadgets.Records.SourceBytesV2

open S31.Functional.SSATextBytes
open S31.Functional.Correspondence.GeneralLinearSSA
open S31.Gadgets.Records.SourceValueV2

private def ident (name : Token) : Bool :=
  isName name && name.length ≤ 96 &&
    !(List.contains
      (["struct", "private", "public", "result", "m31", "let",
        "circuit", "fn", "enum", "match", "bit", "u8", "u16", "u32"].map token)
      name) && !(name.take 15 == (token "_s31_abi_input_").take 15)

private def takeIdent : List Token → Option (Token × List Token)
  | name :: rest => if ident name then some (name, rest) else none
  | [] => none

/-- The common lexer does not admit record field access (`.`). This local
version adds only that token; all other unsupported punctuation fails. -/
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
        let (suffix, rest) := span isDigit tail
        return (head :: suffix) :: (← lexFuel fuel rest)
      else if head == 45 then
        match tail with
        | 62 :: rest => do return [45, 62] :: (← lexFuel fuel rest)
        | _ => none
      else if head == 46 then
        match tail with
        | 42 :: rest => do return [46, 42] :: (← lexFuel fuel rest)
        | _ => do return [46] :: (← lexFuel fuel tail)
      else if List.contains [40, 41, 44, 91, 93, 59, 58, 123, 125, 61, 43] head then
        do return [head] :: (← lexFuel fuel tail)
      else none

private def lex (bytes : List Nat) : Option (List Token) :=
  lexFuel (bytes.length + 1) bytes

private def parseField (remaining : List Token) : Option (Token × List Token) := do
  let (name, rest) ← takeIdent remaining
  let rest ← expectMany [token ":", token "[", token "m31", token ";",
    token "1", token "]"] rest
  return (name, rest)

private def parseFields : Nat → List Token → List Token → Option (List Token × List Token)
  | 0, _, _ => none
  | fuel + 1, fields, remaining => do
      let (name, rest) ← parseField remaining
      if fields.contains name then none else
      let fields := fields ++ [name]
      if rest.head? == some (token ",") then
        parseFields fuel fields (← expect (token ",") rest)
      else return (fields, ← expect (token "}") rest)

private abbrev Root := Token × List (Token × Nat)

private def lookup (name : Token) : List (Token × Nat) → Option Nat
  | [] => none
  | (key, wire) :: rest => if key == name then some wire else lookup name rest

private def rootNamed (name : Token) : List Root → Option (List (Token × Nat))
  | [] => none
  | (key, fields) :: rest => if key == name then some fields else rootNamed name rest

private def parseInput (recordName circuitName : Token) (fields : List Token)
    (roots : List Root) (inputNames : List Token) (publicWords : Nat)
    (remaining : List Token) :
    Option (List Root × List Token × Nat × List Token) := do
  let visibility :: rest := remaining | none
  if visibility != token "public" && visibility != token "private" then none else
  let (name, rest) ← takeIdent rest
  if name == recordName || name == circuitName ||
      (rootNamed name roots).isSome then none else
  let rest ← expectMany [token ":", recordName] rest
  let base := inputNames.length
  let leafNames := (List.range fields.length).map
    (fun i => token ("_s31_abi_input_" ++ toString (base + i)))
  let rootFields := fields.zip ((List.range fields.length).map (base + ·))
  return (roots ++ [(name, rootFields)], inputNames ++ leafNames,
    publicWords + (if visibility == token "public" then fields.length else 0),
    rest)

private def parseInputs : Nat → Token → Token → List Token → List Root →
    List Token → Nat → List Token →
    Option (List Root × List Token × Nat × List Token)
  | 0, _, _, _, _, _, _, _ => none
  | fuel + 1, recordName, circuitName, fields, roots, names, publicWords, remaining => do
      let (roots, names, publicWords, rest) ←
        parseInput recordName circuitName fields roots names publicWords remaining
      if rest.head? == some (token ",") then
        parseInputs fuel recordName circuitName fields roots names publicWords
          (← expect (token ",") rest)
      else return (roots, names, publicWords, ← expect (token ")") rest)

private def parseOperand (roots : List Root) (locals : List (Token × Nat))
    (remaining : List Token) : Option (Nat × List Token) := do
  let (name, rest) ← takeIdent remaining
  if rest.head? == some (token ".") then do
    let rest ← expect (token ".") rest
    let (field, rest) ← takeIdent rest
    let fields ← rootNamed name roots
    return (← lookup field fields, rest)
  else return (← lookup name locals, rest)

private structure State where
  remaining : List Token
  roots : List Root
  locals : List (Token × Nat)
  instructions : List Instruction
  nextWire : Nat
  recordName : Token
  circuitName : Token

private def parseLet (state : State) : Option State := do
  let rest ← expect (token "let") state.remaining
  let (name, rest) ← takeIdent rest
  if name == state.recordName || name == state.circuitName ||
      (rootNamed name state.roots).isSome || (lookup name state.locals).isSome then none else
  let rest ← expect (token "=") rest
  let (lhs, rest) ← parseOperand state.roots state.locals rest
  let op :: rest := rest | none
  let operation ← if op == token "+" then some (.add : ArithmeticOp)
    else if op == token ".*" then some (.mul : ArithmeticOp) else none
  let (rhs, rest) ← parseOperand state.roots state.locals rest
  let rest ← expect (token ";") rest
  let node : Instruction := { id := state.nextWire, lhs, rhs, op := operation }
  let next : State := { state with remaining := rest, locals := state.locals ++ [(name, state.nextWire)], instructions := state.instructions ++ [node], nextWire := state.nextWire + 1 }
  return next

private def parseLets : Nat → State → Option State
  | 0, state =>
      if state.remaining.head? == some (token "let") then none else some state
  | fuel + 1, state =>
      if state.remaining.head? == some (token "let") then do
        parseLets fuel (← parseLet state)
      else some state

private def parseResultFields : Nat → List Root → List (Token × Nat) →
    List Token → List (Token × Nat) → List Token →
    Option (List (Token × Nat) × List Token)
  | 0, _, _, _, _, _ => none
  | fuel + 1, roots, locals, declared, found, remaining => do
      let (field, rest) ← takeIdent remaining
      if !declared.contains field || (lookup field found).isSome then none else
      let rest ← expect (token ":") rest
      let (wire, rest) ← parseOperand roots locals rest
      let found := found ++ [(field, wire)]
      if rest.head? == some (token ",") then
        parseResultFields fuel roots locals declared found
          (← expect (token ",") rest)
      else return (found, ← expect (token "}") rest)

private def checkedFieldsDecidable (program : RecordProgram) :
    (wires : List Nat) → (sources : List Term) →
    Decidable (List.Forall₂ (fun wire source =>
      check (fieldCertificate program wire) source = some ()) wires sources)
  | [], [] => .isTrue .nil
  | [], _ :: _ => .isFalse (by intro h; cases h)
  | _ :: _, [] => .isFalse (by intro h; cases h)
  | wire :: wires, source :: sources =>
      if h : check (fieldCertificate program wire) source = some () then
        match checkedFieldsDecidable program wires sources with
        | .isTrue tail => .isTrue (.cons h tail)
        | .isFalse notTail => .isFalse (by
            intro accepted
            cases accepted with
            | cons _ tail => exact notTail tail)
      else .isFalse (by
        intro accepted
        cases accepted with
        | cons head _ => exact h head)

structure Parsed where
  circuitName : Token
  recordName : Token
  fieldNames : List Token
  inputNames : List Token
  roots : List Root
  program : RecordProgram
  sourceFields : List Term
  checked : Checked program sourceFields

/-- Parse a bounded nominal record directly from bytes and check that every
declaration-ordered output field selects the corresponding SSA term. -/
def parseBytes (bytes : List Nat) : Option Parsed := do
  if bytes.length > 16384 then none else
  let tokens ← lex bytes
  if tokens.length > 512 then none else
  let rest ← expect (token "struct") tokens
  let (recordName, rest) ← takeIdent rest
  if !isLetter recordName.head! || !decide (65 ≤ recordName.head! ∧ recordName.head! ≤ 90) then none else
  let rest ← expect (token "{") rest
  let (fields, rest) ← parseFields 4 [] rest
  let rest ← expect (token "circuit") rest
  let (circuitName, rest) ← takeIdent rest
  if circuitName == recordName then none else
  let rest ← expect (token "(") rest
  let (roots, inputNames, publicWords, rest) ←
    parseInputs 2 recordName circuitName fields [] [] 0 rest
  if publicWords == 0 then none else
  let rest ← expectMany [token "->", token "public", recordName,
    token "{"] rest
  let state ← parseLets 8 ({ remaining := rest, roots := roots, locals := [], instructions := [], nextWire := inputNames.length, recordName := recordName, circuitName := circuitName } : State)
  let rest ← expectMany [recordName, token "{"] state.remaining
  let (result, rest) ← parseResultFields 4 roots state.locals fields [] rest
  if result.length != fields.length then none else
  let fieldWires ← fields.mapM (fun field => lookup field result)
  if publicWords + fieldWires.eraseDups.length > 8 then none else
  let rest := if rest.head? == some (token ";") then rest.drop 1 else rest
  let rest ← expect (token "}") rest
  if !rest.isEmpty then none else
  let program : RecordProgram :=
    { inputs := inputNames.length, instructions := state.instructions,
      fields := fieldWires }
  let terms ← state.instructions.foldlM checkStep
    (initialTerms inputNames.length)
  let sourceFields ← fieldWires.mapM (fun wire => terms[wire]?)
  letI : Decidable (Checked program sourceFields) :=
    checkedFieldsDecidable program program.fields sourceFields
  if h : Checked program sourceFields then
    return { circuitName := circuitName, recordName := recordName, fieldNames := fields, inputNames := inputNames, roots := roots, program := program, sourceFields := sourceFields, checked := h }
  else none

def denotation {n : Nat} (bytes : List Nat) (inputs : Nat → Lanes n) :
    Option (List (Lanes n)) :=
  (parseBytes bytes).map fun parsed =>
    parsed.sourceFields.map (fun term => term.eval inputs)

/-- Every accepted byte program computes its named result fields according
to the independently resolved source operands, for all M31 inputs. -/
theorem parsed_value_correspondence {n : Nat} (bytes : List Nat)
    (parsed : Parsed) (inputs : Nat → Lanes n)
    (hparse : parseBytes bytes = some parsed) :
    some (evaluateFields parsed.program inputs) =
      (denotation bytes inputs).map (List.map some) := by
  rw [checked_fields parsed.program parsed.sourceFields inputs parsed.checked]
  simp [denotation, hparse]

private def pairSource : List Nat := token
  "struct Pair { left: [m31; 1], right: [m31; 1] }\n\
   circuit mix(public x: Pair, private y: Pair) -> public Pair {\n\
     let p = x.left .* y.right;\n\
     let q = p + x.right;\n\
     Pair { right: x.right, left: q }\n\
   }"

set_option maxRecDepth 8192

/-- The concrete source is the independently checked Pair model, including
private `y.right`, declaration-ordered outputs, and the `x.right` alias. -/
theorem pair_source_checked :
    (parseBytes pairSource).map (fun parsed =>
      (parsed.program.inputs, parsed.program.instructions,
       parsed.program.fields, parsed.sourceFields)) =
      some (pairProgram.inputs, pairProgram.instructions,
        pairProgram.fields, pairSourceFields) := by decide

private def wrongFieldSource : List Nat := token
  "struct Pair { left: [m31; 1], right: [m31; 1] }\n\
   circuit mix(public x: Pair, private y: Pair) -> public Pair {\n\
     let p = x.left .* y.missing;\n\
     Pair { left: p, right: x.right }\n\
   }"

theorem wrong_field_rejected : (parseBytes wrongFieldSource).isNone = true := by
  decide

private def swappedProjectionSource : List Nat := token
  "struct Pair { left: [m31; 1], right: [m31; 1] }\n\
   circuit mix(public x: Pair, private y: Pair) -> public Pair {\n\
     let p = x.right .* y.right;\n\
     let q = p + x.right;\n\
     Pair { right: x.right, left: q }\n\
   }"

/-- A changed field projection parses, but receives a different checked SSA
program. It cannot be silently identified with the honest byte source. -/
theorem changed_field_changes_certificate :
    (parseBytes swappedProjectionSource).map (fun parsed =>
      parsed.program.instructions) ≠ some pairProgram.instructions := by decide

end S31.Gadgets.Records.SourceBytesV2
