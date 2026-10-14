import S31.Gadgets.Functional.Correspondence.PureFieldDerivation
import S31.Gadgets.Functional.Correspondence.GeneralLinearSSABytes
import S31.Gadgets.Functional.SSATextBytes

/-!
An independent exact-byte admission checker for the bounded pure-field S31
fragment. Lean lexes the source bytes and constructs both the complete typed
rule list and the normalized relation; it compares them with canonical JSON
artifact bytes. The emitted SHA-256 strings are syntax-checked, not computed
by Lean. Package byte custody remains the Python verifier's responsibility.

This checker deliberately rejects unsupported syntax. It does not prove the
production text parser, optimizer, AIR lowering, or PCS verifier correct.
-/

namespace S31.Functional.Correspondence.PureFieldDerivationBytes

open Lean
open S31.Functional.Correspondence.PureFieldDerivation
open S31.Functional.SSATextBytes (Token token expect expectMany isSpace isNameStart
  isNameTail isDigit span)
open GeneralLinearSSABytes (Parse pythonCanonical fields field string array nat
  digest exactString)

private def obj := Json.mkObj
private def str := Json.str
private def arr (items : List Json) : Json := toJson items
private def num (value : Nat) : Json := toJson value

private def nameText (name : Token) : String :=
  String.ofList (name.map Char.ofNat)

private def reserved : List Token :=
  List.map token ["use", "let", "in", "if", "then", "else", "match", "fun",
    "Fn", "fn", "struct", "enum", "circuit", "blinded", "public", "private",
    "assert_eq", "m31", "accumulate_chainwork", "blake2s_leaf", "blake2s_pair",
    "block_work", "chainwork_from_work", "chainwork_u256", "genesis_hash_mainnet",
    "header_bits", "header_time", "is_zero", "iterate", "lt_u32",
    "m31_from_u16", "merkle_path_blake2s", "merkle_path_poseidon2",
    "poseidon2_leaf", "poseidon2_pair", "pow_valid", "prev_hash", "select",
    "sha256d_header", "splat", "target_mainnet", "target_u256", "work_u256"]

private def takeName : List Token → Option (String × List Token)
  | name :: rest =>
      if name.isEmpty || !isNameStart name.head! || !name.tail.all isNameTail ||
          name.length > 128 || reserved.contains name then none
      else some (nameText name, rest)
  | [] => none

/-- The source lexer consumes one byte per fuel step, accepts only ASCII code
tokens and Python's six ASCII whitespace bytes, and skips `//` comments. -/
private def lexFuel : Nat → List Nat → Option (List Token)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, head :: tail =>
      if isSpace head then lexFuel fuel tail
      else if head == 47 then
        match tail with
        | 47 :: after => lexFuel fuel (span (fun b => b != 10) after).2
        | _ => none
      else if isNameStart head then do
        let (suffix, rest) := span isNameTail tail
        return (head :: suffix) :: (← lexFuel fuel rest)
      else if isDigit head then do
        let (suffix, rest) := span isDigit tail
        return (head :: suffix) :: (← lexFuel fuel rest)
      else if head == 45 then
        match tail with
        | 62 :: rest => return token "->" :: (← lexFuel fuel rest)
        | _ => return token "-" :: (← lexFuel fuel tail)
      else if head == 46 then
        match tail with
        | 42 :: rest => return token ".*" :: (← lexFuel fuel rest)
        | _ => none
      else if List.contains [40, 41, 44, 91, 93, 59, 58, 123, 125, 61, 43,
          64] head then
        return [head] :: (← lexFuel fuel tail)
      else none

private def lex (bytes : List Nat) : Option (List Token) := do
  if bytes.length > 16384 || bytes.any (· > 127) then none else
  let tokens ← lexFuel (bytes.length + 1) bytes
  if tokens.length > 512 then none else some tokens

private def laneType (tokens : List Token) : Option (Nat × List Token) := do
  let rest ← expectMany [token "[", token "m31", token ";"] tokens
  let count ← rest.head?
  let lanes ← (nameText count).toNat?
  if lanes < 1 || lanes > 8 || count != token (toString lanes) then none else
  return (lanes, ← expect (token "]") rest.tail)

private structure Binding where
  name : String
  wire : String
  kind : String
  length : Nat
  deriving Repr, Inhabited

private structure Input where
  name : String
  visibility : String
  length : Nat
  deriving Repr

private def inputJson (input : Input) : Json :=
  obj [("name", str input.name), ("kind", str "m31"),
    ("length", num input.length), ("visibility", str input.visibility)]

private def resultJson (result : Binding) : Json :=
  obj [("wire", str result.wire), ("kind", str result.kind),
    ("length", num result.length)]

private def takeVisibility : List Token → Option (String × List Token)
  | head :: rest =>
      if head == token "public" then some ("public", rest)
      else if head == token "private" then some ("private", rest)
      else none
  | [] => none

private def parseInput (circuit : String) (found : List Input)
    (tokens : List Token) : Option (Input × List Token) := do
  let (visibility, rest) ← takeVisibility tokens
  let (name, rest) ← takeName rest
  if name == circuit || found.any (·.name == name) then none else
  let rest ← expect (token ":") rest
  let (length, rest) ← laneType rest
  return (⟨name, visibility, length⟩, rest)

private def parseInputs : Nat → String → List Input → List Token →
    Option (List Input × List Token)
  | 0, _, _, _ => none
  | fuel + 1, circuit, found, tokens => do
      let (input, rest) ← parseInput circuit found tokens
      let found := found ++ [input]
      if rest.head? == some (token ",") then
        if found.length >= 8 then none else
        parseInputs fuel circuit found rest.tail
      else return (found, ← expect (token ")") rest)

private def unwrap (parts : List Token) : List Token := Id.run do
  let mut current := parts
  for _ in [:16] do
    if current.head? != some (token "(") || current.getLast? != some (token ")") then
      break
    let mut depth := 0
    let mut whole := true
    for (item, index) in current.zipIdx do
      if item == token "(" then depth := depth + 1
      if item == token ")" then depth := depth - 1
      if depth == 0 && index + 1 < current.length then whole := false
    if !whole then break
    current := current.tail.dropLast
  return current

private def parseNamedArgs (arity : Nat) (tokens : List Token) : Option (List String) := do
  let mut rest := tokens
  let mut names := []
  for index in [:arity] do
    let (name, next) ← takeName rest
    names := names ++ [name]
    rest := next
    if index + 1 < arity then rest ← expect (token ",") rest
  if !rest.isEmpty then none else some names

private def parseExpr (parts : List Token) : Option (String × List String) := do
  let parts := unwrap parts
  match parts with
  | [name] =>
      let (name, rest) ← takeName [name]
      if !rest.isEmpty then none else some ("alias", [name])
  | [lhs, op, rhs] =>
      let (lhs, _) ← takeName [lhs]
      let (rhs, _) ← takeName [rhs]
      let operation ← if op == token "+" then some "add"
        else if op == token "-" then some "sub"
        else if op == token ".*" then some "mul" else none
      return (operation, [lhs, rhs])
  | _ =>
      let prefixes : List (List Token × String × Nat) := [
        (List.map token ["std", ":", ":", "math", ":", ":", "inv", "("], "inv", 1),
        (List.map token ["std", ":", ":", "field", ":", ":", "is_zero", "("], "is_zero", 1),
        (List.map token ["std", ":", ":", "field", ":", ":", "select", "("], "select", 3),
        (List.map token ["select", "("], "select", 3)]
      let (headTokens, op, arity) ← prefixes.find? (fun entry =>
        entry.1.isPrefixOf parts)
      let rest := parts.drop headTokens.length
      if rest.getLast? != some (token ")") then none else
      return (op, ← parseNamedArgs arity rest.dropLast)

private def takeExpression (tokens : List Token) : Option (List Token × List Token) :=
  let (parts, rest) := (tokens.takeWhile (· != token ";"),
    tokens.dropWhile (· != token ";"))
  if parts.isEmpty || rest.isEmpty then none else some (parts, rest.tail)

private structure Acc where
  remaining : List Token
  env : List Binding
  steps : List Json
  nodes : List Json
  sourceSteps : List SourceStep
  wireNames : List String
  inverseSources : List String
  controlUsed : Bool

private def lookup (env : List Binding) (name : String) : Option Binding :=
  env.find? (·.name == name)

private def ruleOf : String → Option SourceRule
  | "add" => some .add | "sub" => some .sub | "mul" => some .mul
  | "inv" => some .inv | "is_zero" => some .isZero
  | "select" => some .select | _ => none

private def parseLet (circuit : String) (explicitStd : Bool) (acc : Acc) : Option Acc := do
  let rest ← expect (token "let") acc.remaining
  let (name, rest) ← takeName rest
  if name == circuit || acc.env.any (·.name == name) then none else
  let rest ← expect (token "=") rest
  let (expr, rest) ← takeExpression rest
  let (op, names) ← parseExpr expr
  let args ← names.mapM (lookup acc.env)
  let wires := args.map (·.wire)
  let mut result : Binding := ⟨name, name, "m31", 1⟩
  let mut node : Option Json := none
  let mut controls := acc.controlUsed
  let mut inverses := acc.inverseSources
  if op == "alias" then
    result := { (args.head!) with name }
  else if op == "add" || op == "sub" || op == "mul" then
    if args.length != 2 || args[0]!.kind != "m31" ||
        args[1]!.kind != "m31" || args[0]!.length != args[1]!.length then none else
    result := ⟨name, name, "m31", args[0]!.length⟩
    node := some (obj [("name", str name), ("op", str op),
      ("lhs", str wires[0]!), ("rhs", str wires[1]!)])
  else if op == "inv" then
    if !explicitStd || args.length != 1 || args[0]!.kind != "m31" ||
        inverses.contains wires[0]! then none else
    inverses := inverses ++ [wires[0]!]
    result := ⟨name, name, "m31", args[0]!.length⟩
    node := some (obj [("name", str name), ("op", str op),
      ("lhs", str wires[0]!)])
    controls := true
  else if op == "is_zero" then
    if !explicitStd || args.length != 1 || args[0]!.kind != "m31" ||
        args[0]!.length != 1 then none else
    result := ⟨name, name, "bit", 1⟩
    node := some (obj [("name", str name), ("op", str op),
      ("lhs", str wires[0]!)])
    controls := true
  else if op == "select" then
    if args.length != 3 || args[0]!.kind != "bit" ||
        args[1]!.kind != "m31" || args[2]!.kind != "m31" ||
        args[1]!.length != args[2]!.length ||
        (expr.head? == some (token "std") && !explicitStd) then none else
    result := ⟨name, name, "m31", args[1]!.length⟩
    node := some (obj [("name", str name), ("op", str op),
      ("lhs", str wires[1]!), ("rhs", str wires[2]!),
      ("selector", str wires[0]!)])
    controls := true
  else none
  let nodes := acc.nodes ++ node.toList
  if nodes.length > 64 then none else
  let index := if node.isSome then num (nodes.length - 1) else Json.null
  let step := obj [("name", str name), ("rule", str op),
    ("source_operands", arr (names.map str)),
    ("resolved_operands", arr (wires.map str)),
    ("result", resultJson result), ("node_index", index)]
  let (sourceSteps, wireNames) ← if node.isSome then do
      let refs ← wires.mapM (acc.wireNames.idxOf?)
      let rule ← ruleOf op
      some (acc.sourceSteps ++ [⟨rule, refs⟩], acc.wireNames ++ [name])
    else some (acc.sourceSteps, acc.wireNames)
  return Acc.mk rest (acc.env ++ [result]) (acc.steps ++ [step]) nodes
    sourceSteps wireNames inverses controls

private def parseLets : Nat → String → Bool → Acc → Option Acc
  | 0, _, _, acc =>
      if acc.remaining.head? == some (token "let") then none else some acc
  | fuel + 1, circuit, explicitStd, acc =>
      if acc.remaining.head? == some (token "let") then do
        let next ← parseLet circuit explicitStd acc
        parseLets fuel circuit explicitStd next
      else some acc

structure Parsed where
  relation : Json
  derivation : Json
  sourceSteps : List SourceStep
  outputIndex : Nat

/-- This is the source-byte denotation's syntactic decoder. Successful parse
requires a bounded typed straight-line program and a nonempty control rule. -/
def parseSource (bytes : List Nat) : Option Parsed := do
  let tokens ← lex bytes
  let (explicitStd, rest) ← if tokens.head? == some (token "use") then do
      let rest ← expectMany (List.map token ["use", "std", "@", "1", ";"]) tokens
      some (true, rest)
    else some (false, tokens)
  let rest ← expect (token "circuit") rest
  let (circuit, rest) ← takeName rest
  let rest ← expect (token "(") rest
  let (inputs, rest) ← parseInputs 8 circuit [] rest
  let rest ← expectMany [token "->", token "public"] rest
  let (outputLength, rest) ← laneType rest
  if outputLength + (inputs.filter (·.visibility == "public")).foldl
      (fun total input => total + input.length) 0 > 8 then none else
  let rest ← expect (token "{") rest
  let env := inputs.map (fun input =>
    Binding.mk input.name input.name "m31" input.length)
  let acc ← parseLets 64 circuit explicitStd {
    remaining := rest, env, steps := [], nodes := [], sourceSteps := [],
    wireNames := inputs.map (·.name), inverseSources := [], controlUsed := false }
  let (outputName, rest) ← takeName acc.remaining
  let rest := if rest.head? == some (token ";") then rest.tail else rest
  let rest ← expect (token "}") rest
  if !rest.isEmpty || !acc.controlUsed || acc.nodes.isEmpty then none else
  let output ← lookup acc.env outputName
  if output.kind != "m31" || output.length != outputLength then none else
  let outputIndex ← acc.wireNames.idxOf? output.wire
  let relation := obj [("version", num 1), ("name", str circuit),
    ("inputs", arr (inputs.map inputJson)), ("nodes", arr acc.nodes),
    ("assertions", arr []), ("public_outputs", arr [str output.wire])]
  let derivation := obj [("name", str circuit),
    ("inputs", arr (inputs.map inputJson)), ("steps", arr acc.steps),
    ("output", obj [("source_name", str outputName),
      ("wire", str output.wire), ("kind", str output.kind),
      ("length", num output.length)])]
  return ⟨relation, derivation, acc.sourceSteps, outputIndex⟩

private def certName (json : Json) : Parse String := do
  let value ← string json
  let bytes := value.toUTF8.data.toList.map UInt8.toNat
  match takeName [bytes] with
  | some (name, []) => return name
  | _ => throw "invalid pure-field certificate name"

private def certInput (json : Json) : Parse Input := do
  fields json ["name", "kind", "length", "visibility"]
  let name ← certName (← field json "name")
  exactString (← field json "kind") "m31"
  let length ← nat (← field json "length")
  let visibility ← string (← field json "visibility")
  if length < 1 || length > 8 ||
      (visibility != "public" && visibility != "private") then
    throw "invalid pure-field certificate input type"
  return ⟨name, visibility, length⟩

private structure Replay where
  env : List Binding
  nodes : List Json
  inverseSources : List String
  controls : Nat

/-- Replay one serialized rule without reading source tokens. Both the
resolved operands and the claimed result shape must match this reconstruction. -/
private def replayStep (circuit : String) (state : Replay) (step : Json) :
    Parse Replay := do
  fields step ["name", "rule", "source_operands", "resolved_operands",
    "result", "node_index"]
  let name ← certName (← field step "name")
  if name == circuit || state.env.any (·.name == name) then
    throw "shadowed pure-field certificate let"
  let op ← string (← field step "rule")
  let names ← array certName (← field step "source_operands")
  let arity ← match op with
    | "alias" | "inv" | "is_zero" => pure 1
    | "add" | "sub" | "mul" => pure 2
    | "select" => pure 3
    | _ => throw "unsupported pure-field certificate rule"
  if names.length != arity then throw "wrong pure-field certificate arity"
  let args ← names.mapM (fun operand =>
    match lookup state.env operand with
    | some found => pure found
    | none => throw "future pure-field certificate operand")
  let wires := args.map (·.wire)
  let resolved ← array string (← field step "resolved_operands")
  if resolved != wires then throw "certificate operand resolution differs"
  let mut result : Binding := ⟨name, name, "m31", 1⟩
  let mut node : Option Json := none
  let mut inverseSources := state.inverseSources
  let mut controls := state.controls
  if op == "alias" then
    result := { (args.head!) with name }
  else if op == "add" || op == "sub" || op == "mul" then
    if args[0]!.kind != "m31" || args[1]!.kind != "m31" ||
        args[0]!.length != args[1]!.length then
      throw "binary certificate operand shape differs"
    result := ⟨name, name, "m31", args[0]!.length⟩
    node := some (obj [("name", str name), ("op", str op),
      ("lhs", str wires[0]!), ("rhs", str wires[1]!)])
  else if op == "inv" then
    if args[0]!.kind != "m31" || inverseSources.contains wires[0]! then
      throw "inverse certificate source differs"
    inverseSources := inverseSources ++ [wires[0]!]
    result := ⟨name, name, "m31", args[0]!.length⟩
    node := some (obj [("name", str name), ("op", str op),
      ("lhs", str wires[0]!)])
    controls := controls + 1
  else if op == "is_zero" then
    if args[0]!.kind != "m31" || args[0]!.length != 1 then
      throw "zero-test certificate operand shape differs"
    result := ⟨name, name, "bit", 1⟩
    node := some (obj [("name", str name), ("op", str op),
      ("lhs", str wires[0]!)])
    controls := controls + 1
  else
    if args[0]!.kind != "bit" || args[1]!.kind != "m31" ||
        args[2]!.kind != "m31" || args[1]!.length != args[2]!.length then
      throw "select certificate operand shape differs"
    result := ⟨name, name, "m31", args[1]!.length⟩
    node := some (obj [("name", str name), ("op", str op),
      ("lhs", str wires[1]!), ("rhs", str wires[2]!),
      ("selector", str wires[0]!)])
    controls := controls + 1
  let nodes := state.nodes ++ node.toList
  if nodes.length > 64 then throw "certificate exceeds node bound"
  let index := if node.isSome then num (nodes.length - 1) else Json.null
  if (← field step "node_index") != index ||
      (← field step "result") != resultJson result then
    throw "certificate node index or typed result differs"
  return Replay.mk (state.env ++ [result]) nodes inverseSources controls

/-- Reconstruct the complete normalized relation solely from the certificate
rule JSON. This pass is intentionally independent of `parseSource`. -/
def replayDerivation (derivation : Json) : Parse Json := do
  fields derivation ["name", "inputs", "steps", "output"]
  let circuit ← certName (← field derivation "name")
  let inputs ← array certInput (← field derivation "inputs")
  if inputs.isEmpty || inputs.length > 8 then
    throw "certificate exceeds input bound"
  let mut env : List Binding := []
  for input in inputs do
    if input.name == circuit || env.any (·.name == input.name) then
      throw "duplicate certificate input"
    env := env ++ [⟨input.name, input.name, "m31", input.length⟩]
  let steps ← array pure (← field derivation "steps")
  if steps.isEmpty || steps.length > 64 then
    throw "certificate exceeds step bound"
  let state ← steps.foldlM (replayStep circuit)
    (Replay.mk env [] [] 0)
  fields (← field derivation "output")
    ["source_name", "wire", "kind", "length"]
  let output := (← field derivation "output")
  let outputName ← certName (← field output "source_name")
  let selected ← match lookup state.env outputName with
    | some selected => pure selected
    | none => throw "unknown certificate output"
  if selected.kind != "m31" || state.controls == 0 || state.nodes.isEmpty ||
      selected.length + (inputs.filter (·.visibility == "public")).foldl
        (fun total input => total + input.length) 0 > 8 then
    throw "certificate result or public ABI differs"
  if output != obj [("source_name", str outputName),
      ("wire", str selected.wire), ("kind", str selected.kind),
      ("length", num selected.length)] then
    throw "certificate output type differs"
  return obj [("version", num 1), ("name", str circuit),
    ("inputs", arr (inputs.map inputJson)), ("nodes", arr state.nodes),
    ("assertions", arr []), ("public_outputs", arr [str selected.wire])]

private def canonical (bytes : String) (bound : Nat) : Parse Json := do
  if bytes.utf8ByteSize > bound then throw "JSON exceeds byte bound"
  let json ← Json.parse bytes
  if pythonCanonical 0 json ++ "\n" != bytes then
    throw "noncanonical JSON bytes"
  return json

/-- Compare complete exact certificate and relation bytes against Lean's
source-derived typed rules and normalized nodes. Digest *contents* are not
authenticated by this checker; this is a semantic byte bridge. -/
private def checkParsed (parsed : Parsed) (certificateBytes relationBytes : String) :
    Parse Unit := do
  let certificate ← canonical certificateBytes 131072
  fields certificate ["schema", "capability", "source_sha256",
    "relation_sha256", "derivation"]
  exactString (← field certificate "schema") "s31-pure-field-derivation-v1"
  exactString (← field certificate "capability")
    "exact-source-to-normalized-relation-only"
  digest (← field certificate "source_sha256")
  digest (← field certificate "relation_sha256")
  let derivation ← field certificate "derivation"
  let replayed ← replayDerivation derivation
  if replayed != parsed.relation then
    throw "certificate rule replay differs from source-derived relation"
  if derivation != parsed.derivation then
    throw "typed pure-field derivation differs from exact source"
  let relation ← canonical relationBytes 65536
  if relation != parsed.relation then
    throw "normalized relation differs from exact source"
  return ()

def checkBytes (sourceBytes : List Nat) (certificateBytes relationBytes : String) :
    Parse Parsed :=
  match parseSource sourceBytes with
  | none => .error "source outside bounded pure-field grammar"
  | some parsed => do
      checkParsed parsed certificateBytes relationBytes
      return parsed

/-- The denotation of the exact source bytes is the typed source rule sequence
obtained by Lean's bounded parser. The initial state is in declared input
order; an alias is represented by its previously resolved wire index. -/
def sourceDenotation (sourceBytes : List Nat)
    (initial : PureFieldDerivation.State) : Option PureFieldDerivation.Value := do
  let parsed ← parseSource sourceBytes
  let final ← parsed.sourceSteps.foldlM sourceStep initial
  final[parsed.outputIndex]?

/-- Once the three supplied byte strings pass the Lean checker, the complete
normalized rule sequence has the same partial field value as the exact source
bytes for every initial state, including zero-inverse and invalid-selector
failure. This theorem is independent of Python's certificate generator. -/
theorem checked_bytes_lower_output (sourceBytes : List Nat)
    (certificateBytes relationBytes : String) (parsed : Parsed)
    (initial : PureFieldDerivation.State)
    (hcheck : checkBytes sourceBytes certificateBytes relationBytes = .ok parsed) :
    ((parsed.sourceSteps.map lowerStep).foldlM normalizedStep initial).bind
      (·[parsed.outputIndex]?) = sourceDenotation sourceBytes initial := by
  have hparse : parseSource sourceBytes = some parsed := by
    unfold checkBytes at hcheck
    cases h : parseSource sourceBytes with
    | none => simp [h] at hcheck
    | some actual =>
        cases hchecked : checkParsed actual certificateBytes relationBytes with
        | error message => simp [h, hchecked] at hcheck
        | ok found =>
            have hsame : actual = parsed := by
              simpa [h, hchecked] using hcheck
            simp [hsame] at h ⊢
  simp [sourceDenotation, hparse]
  exact lower_output parsed.sourceSteps initial parsed.outputIndex

end S31.Functional.Correspondence.PureFieldDerivationBytes
