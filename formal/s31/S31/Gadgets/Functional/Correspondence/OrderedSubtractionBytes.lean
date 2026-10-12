import S31.Gadgets.Functional.Correspondence.OrderedSubtractionRelease
import S31.Gadgets.Functional.SSANormalizedBytes

/-!
An exact byte-to-normalized-relation checker for the strict, straight-line
four-lane direct-Gate grammar with ordered subtraction. This is a deliberately
smaller subset of the Python certificate: one public input, 1–16 named binary
`let` operations, and one returned earlier wire. Helpers, lambdas, aliases,
and general S31 source are not admitted here.

The parser consumes source bytes, resolves every operand to an earlier name,
keeps subtraction order, and rejects repeated operations and reversed
commutative operands. The normalized encoder compares exact JSON bytes.
Its semantic theorem below concerns arbitrary satisfying packed arithmetic
rows. Native row emission, Gate lookup, and PCS openings are still external
joins.
-/

namespace S31.Functional.Correspondence.OrderedSubtractionBytes

open S31.Functional.SSATextBytes

abbrev Op := SourceFunctionBytes.Op
abbrev Lanes := Fin 4 → S31.M31
abbrev Tail := Nat → Fin 4 → S31.M31

structure Instruction where
  id : Nat
  lhs : Nat
  rhs : Nat
  op : Op
deriving DecidableEq, Repr

structure Parsed where
  circuitName : Token
  inputName : Token
  outputName : Token
  wireNames : List Token
  instructions : List Instruction
  output : Nat
deriving DecidableEq, Repr

structure State where
  remaining : List Token
  names : List Token
  expressions : List (Op × Nat × Nat)
  instructions : List Instruction

def parseLet (state : State) : Option State := do
  let rest ← expect (token "let") state.remaining
  let (name, rest) ← SourceFunctionBytes.takeIdent rest
  if state.names.contains name then none else
  let rest ← expect (token "=") rest
  let (left, rest) ← SourceFunctionBytes.takeIdent rest
  let (op, rest) ← SourceFunctionBytes.takeOp rest
  let (right, rest) ← SourceFunctionBytes.takeIdent rest
  let rest ← expect (token ";") rest
  let lhs ← findName left state.names
  let rhs ← findName right state.names
  if op != .sub && lhs > rhs then none else
  let expression := (op, lhs, rhs)
  if state.expressions.contains expression then none else
  let instruction : Instruction := { id := state.names.length, lhs, rhs, op }
  return { remaining := rest,
           names := state.names ++ [name],
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

def parseBytes (bytes : List Nat) : Option Parsed := do
  if bytes.length > 16384 then none else
  let tokens ← lex bytes
  if tokens.length > 256 then none else
  let rest ← expect (token "circuit") tokens
  let (circuitName, rest) ← SourceFunctionBytes.takeIdent rest
  let rest ← expectMany [token "(", token "public"] rest
  let (inputName, rest) ← SourceFunctionBytes.takeIdent rest
  let rest ← expectMany [token ":", token "[", token "m31", token ";",
                         token "4", token "]", token ")", token "->",
                         token "public", token "[", token "m31", token ";",
                         token "4", token "]", token "{"] rest
  let state ← parseLetsFuel 16 {
    remaining := rest, names := [inputName], expressions := [], instructions := [] }
  if state.instructions.isEmpty then none else
  let (outputName, rest) ← SourceFunctionBytes.takeIdent state.remaining
  let rest ← expect (token "}") rest
  if !rest.isEmpty then none else
  let output ← findName outputName state.names
  if output == 0 then none else
  return { circuitName, inputName, outputName,
           wireNames := state.names, instructions := state.instructions, output }

def executeStep (values : List Lanes) (instruction : Instruction) :
    Option (List Lanes) := do
  if instruction.id != values.length then none else
  let lhs ← values[instruction.lhs]?
  let rhs ← values[instruction.rhs]?
  return values ++ [fun i => SourceFunctionBytes.Op.eval instruction.op (lhs i) (rhs i)]

def execute (parsed : Parsed) (input : Lanes) : Option Lanes := do
  let values ← parsed.instructions.foldlM executeStep [input]
  values[parsed.output]?

def denotation (bytes : List Nat) (input : Lanes) : Option Lanes := do
  let parsed ← parseBytes bytes
  execute parsed input

/-- Every listed operation is constrained at arbitrary row values. Operand
indices are resolved against the previously accepted wire values. This
explicit address-to-value premise is the local model of the Gate lookup join;
the cryptographic authentication of native proof openings remains open. -/
inductive Accepts (tailA tailB : Tail) :
    List Lanes → List Instruction → List Lanes → Prop where
  | nil (values : List Lanes) : Accepts tailA tailB values [] values
  | cons (values : List Lanes) (step : Instruction) (steps : List Instruction)
      (lhs rhs out : Lanes) (final : List Lanes)
      (hid : step.id = values.length)
      (hlhs : values[step.lhs]? = some lhs)
      (hrhs : values[step.rhs]? = some rhs)
      (hrow : SourceFunctionBytes.Op.packed step.op lhs rhs out tailA tailB)
      (hrest : Accepts tailA tailB (values ++ [out]) steps final) :
      Accepts tailA tailB values (step :: steps) final

theorem accepts_execute (tailA tailB : Tail) (values final : List Lanes)
    (instructions : List Instruction)
    (h : Accepts tailA tailB values instructions final) :
    instructions.foldlM executeStep values = some final := by
  induction h with
  | nil => rfl
  | cons values step steps lhs rhs out final hid hlhs hrhs hrow hrest ih =>
      have hout : out = fun i => SourceFunctionBytes.Op.eval step.op (lhs i) (rhs i) := by
        funext i
        exact (SourceFunctionBytes.packed_iff_eval step.op lhs rhs out
          tailA tailB).mp hrow i
      simp [List.foldlM_cons, executeStep, hid, hlhs, hrhs, ← hout, ih]

def encodeNode (names : List Token) (instruction : Instruction) : Option Token := do
  let lhs ← names[instruction.lhs]?
  let name ← names[instruction.id]?
  let rhs ← names[instruction.rhs]?
  let operation := match instruction.op with
    | .add => token "add" | .sub => token "sub" | .mul => token "mul"
  return token "    {\n      \"lhs\": \"" ++ lhs ++
    token "\",\n      \"name\": \"" ++ name ++
    token "\",\n      \"op\": \"" ++ operation ++
    token "\",\n      \"rhs\": \"" ++ rhs ++ token "\"\n    }"

def encodeNormalized (parsed : Parsed) : Option Token := do
  let nodes ← parsed.instructions.mapM (encodeNode parsed.wireNames)
  return token "{\n  \"assertions\": [],\n  \"inputs\": [\n    {\n      \"kind\": \"m31\",\n      \"length\": 4,\n      \"name\": \"" ++
    parsed.inputName ++
    token "\",\n      \"visibility\": \"public\"\n    }\n  ],\n  \"name\": \"" ++
    parsed.circuitName ++
    token "\",\n  \"nodes\": [\n" ++ SSANormalizedBytes.joinNodes nodes ++
    token "\n  ],\n  \"public_outputs\": [\n    \"" ++
    parsed.outputName ++ token "\"\n  ],\n  \"version\": 1\n}\n"

def checkRelation (sourceBytes normalizedBytes : List Nat) : Option Parsed := do
  let parsed ← parseBytes sourceBytes
  let expected ← encodeNormalized parsed
  if expected != normalizedBytes then none else some parsed

theorem checked_relation_bytes (sourceBytes normalizedBytes : List Nat)
    (parsed : Parsed)
    (h : checkRelation sourceBytes normalizedBytes = some parsed) :
    parseBytes sourceBytes = some parsed ∧
      encodeNormalized parsed = some normalizedBytes := by
  unfold checkRelation at h
  cases hs : parseBytes sourceBytes with
  | none => simp [hs] at h
  | some found =>
      cases he : encodeNormalized found with
      | none => simp [hs, he] at h
      | some expected =>
          by_cases hsame : expected = normalizedBytes
          · have hp : found = parsed := by simpa [hs, he, hsame] using h
            subst parsed
            exact ⟨rfl, by simpa [hsame] using he⟩
          · simp [hs, he, hsame] at h

/-- Exact source and normalized bytes, plus arbitrary accepted packed rows,
force the public claim to equal the meaning of the parsed source bytes. The
row relation carries the explicit coherent-wire premise above. -/
theorem checked_air_sound (sourceBytes normalizedBytes : List Nat)
    (parsed : Parsed) (input claim : Lanes) (final : List Lanes)
    (tailA tailB : Tail)
    (hbytes : checkRelation sourceBytes normalizedBytes = some parsed)
    (hrows : Accepts tailA tailB [input] parsed.instructions final)
    (houtput : final[parsed.output]? = some claim) :
    denotation sourceBytes input = some claim := by
  obtain ⟨hsource, _⟩ := checked_relation_bytes sourceBytes normalizedBytes parsed hbytes
  simp [denotation, execute, hsource,
        accepts_execute tailA tailB [input] final parsed.instructions hrows,
        houtput]

end S31.Functional.Correspondence.OrderedSubtractionBytes
