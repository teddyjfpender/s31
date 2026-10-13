import S31.Gadgets.Functional.SSATextBytes
import S31.Gadgets.Air.SimdChunks

/-!
A bounded, executable ASCII byte-level model of one pure named M31 array helper
called by one circuit. The parser consumes actual source bytes and rejects
unbound names, mismatched array lengths, and trailing syntax. Operand names
are resolved at the helper body and at the call, so subtraction order is
preserved across both boundaries.

This proves the semantics of this Lean parser and the mathematical packed-row
relation. It does not prove equivalence with the production Python parser,
Zig row emission, or the proof system's polynomial commitment verifier.
-/

namespace S31.Functional.Correspondence.SourceFunctionBytes

open S31.Functional.SSATextBytes
open S31.Gadgets.Air.SimdChunks

inductive Op where
  | add | sub | mul
  deriving DecidableEq, Repr

def Op.eval (op : Op) (a b : S31.M31) : S31.M31 :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

def Op.node (op : Op) : S31.Node :=
  match op with
  | .add => S31.Functional.arithmeticNode false
  | .sub => S31.Functional.subtractionNode
  | .mul => S31.Functional.arithmeticNode true

def Op.packed {n : Nat} (op : Op) (a b claimed : Fin n → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) : Prop :=
  match op with
  | .add => packedRows false a b claimed tailA tailB
  | .sub => subPackedRows a b claimed tailA tailB
  | .mul => packedRows true a b claimed tailA tailB

/-- The packed relation constrains every active lane, including a short
final chunk, independently of arbitrary inactive input limbs. -/
theorem packed_iff_eval {n : Nat} (op : Op) (a b claimed : Fin n → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) :
    op.packed a b claimed tailA tailB ↔
      ∀ i : Fin n, claimed i = op.eval (a i) (b i) := by
  cases op with
  | add => exact packedRows_iff false a b claimed tailA tailB
  | sub => exact subPackedRows_iff a b claimed tailA tailB
  | mul => exact packedRows_iff true a b claimed tailA tailB

/-- The same row relation agrees with the executable normalized node. -/
theorem packed_iff_node {n : Nat} (op : Op) (a b claimed : Fin n → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) :
    op.packed a b claimed tailA tailB ↔
      S31.evaluateNode (S31.Functional.arithmeticEnv a b) op.node =
        .ok ⟨.m31, List.ofFn claimed⟩ := by
  cases op with
  | add => exact packedRows_iff_normalized_node false a b claimed tailA tailB
  | sub => exact subPackedRows_iff_normalized_node a b claimed tailA tailB
  | mul => exact packedRows_iff_normalized_node true a b claimed tailA tailB

/-- A resolved name is one of the two function parameters or circuit inputs.
`false` chooses the first and `true` the second; preserving this bit is
essential for noncommutative subtraction. -/
def choose (second : Bool) (first other : α) : α :=
  if second then other else first

structure Parsed where
  length : Nat
  helperName : Token
  circuitName : Token
  firstInput : Token
  secondInput : Token
  outputName : Token
  op : Op
  bodyLeftSecond : Bool
  bodyRightSecond : Bool
  callFirstSecond : Bool
  callSecondSecond : Bool
  inputNamesDistinct : firstInput ≠ secondInput
  deriving DecidableEq, Repr

def Parsed.left {p : Parsed} (a b : Fin p.length → S31.M31) :
    Fin p.length → S31.M31 :=
  choose p.bodyLeftSecond
    (choose p.callFirstSecond a b) (choose p.callSecondSecond a b)

def Parsed.right {p : Parsed} (a b : Fin p.length → S31.M31) :
    Fin p.length → S31.M31 :=
  choose p.bodyRightSecond
    (choose p.callFirstSecond a b) (choose p.callSecondSecond a b)

def Parsed.value (p : Parsed) (a b : Fin p.length → S31.M31) :
    Fin p.length → S31.M31 :=
  fun i => p.op.eval (p.left a b i) (p.right a b i)

def Parsed.air (p : Parsed) (a b claimed : Fin p.length → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) : Prop :=
  p.op.packed (p.left a b) (p.right a b) claimed tailA tailB

/-- For any inputs and public claim, the parsed program's packed AIR rows
accept exactly its source denotation. -/
theorem air_iff_value (p : Parsed) (a b claimed : Fin p.length → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) :
    p.air a b claimed tailA tailB ↔ claimed = p.value a b := by
  rw [Parsed.air, packed_iff_eval]
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    exact congrFun h i

/-- The same accepted claim is the result of the normalized relation node
with operands chosen according to the parsed helper and call sites. -/
theorem air_iff_normalized_node (p : Parsed)
    (a b claimed : Fin p.length → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) :
    p.air a b claimed tailA tailB ↔
      S31.evaluateNode
        (S31.Functional.arithmeticEnv (p.left a b) (p.right a b))
        p.op.node = .ok ⟨.m31, List.ofFn claimed⟩ := by
  exact packed_iff_node p.op (p.left a b) (p.right a b) claimed tailA tailB

/-- Reserved syntax and plain builtins in the independently checked source
fragment. The audit test compares this set with the Python checker by trying
every reserved name as a circuit identifier. -/
def forbiddenIdent : List Token :=
  (List.map token ["use", "let", "in", "if", "then", "else", "match",
    "fun", "Fn", "fn", "struct", "enum", "circuit", "blinded", "public",
    "private", "assert_eq", "m31", "accumulate_chainwork", "blake2s_leaf",
    "blake2s_pair", "block_work", "chainwork_from_work", "chainwork_u256",
    "genesis_hash_mainnet", "header_bits", "header_time", "is_zero",
    "iterate", "lt_u32", "m31_from_u16", "merkle_path_blake2s",
    "merkle_path_poseidon2", "poseidon2_leaf", "poseidon2_pair", "pow_valid",
    "prev_hash", "select", "sha256d_header", "splat", "target_mainnet",
    "target_u256", "work_u256"])

def takeIdent (remaining : List Token) : Option (Token × List Token) := do
  let (name, rest) ← takeName remaining
  if name.length > 128 || forbiddenIdent.contains name then none else
  return (name, rest)

def takeLength (remaining : List Token) : Option (Nat × List Token) := do
  let rest ← expectMany [token "[", token "m31", token ";"] remaining
  match rest with
  | count :: rest =>
      let n ← match count with
        | [49] => some 1 | [50] => some 2 | [51] => some 3
        | [52] => some 4 | [53] => some 5 | [54] => some 6
        | [55] => some 7 | [56] => some 8 | _ => none
      let rest ← expect (token "]") rest
      return (n, rest)
  | [] => none

def takeSameLength (n : Nat) (remaining : List Token) : Option (List Token) := do
  let (found, rest) ← takeLength remaining
  if found == n then some rest else none

def resolve (name first second : Token) : Option Bool :=
  if name == first then some false
  else if name == second then some true
  else none

def takeOp : List Token → Option (Op × List Token)
  | head :: rest =>
      if head == token "+" then some (.add, rest)
      else if head == token "-" then some (.sub, rest)
      else if head == token ".*" then some (.mul, rest)
      else none
  | [] => none

/-- Exact bounded grammar: one named binary function, then one circuit with
two private M31 arrays and one public M31 array of the same length. The body
has one binary operation; the circuit has one call and returns that result.
The caller and callee may reorder or reuse their two inputs. -/
def parseBytes (bytes : List Nat) : Option Parsed := do
  if bytes.length > 16384 then none else
  if !(bytes.all (fun byte => byte < 128)) then none else
  let tokens ← lex bytes
  if tokens.length > 256 then none else
  let rest ← expect (token "fn") tokens
  let (helperName, rest) ← takeIdent rest
  let rest ← expect (token "(") rest
  let (paramFirst, rest) ← takeIdent rest
  let rest ← expect (token ":") rest
  let (n, rest) ← takeLength rest
  let rest ← expect (token ",") rest
  let (paramSecond, rest) ← takeIdent rest
  if paramFirst == paramSecond || helperName == paramFirst ||
      helperName == paramSecond then none else
  let rest ← expect (token ":") rest
  let rest ← takeSameLength n rest
  let rest ← expectMany [token ")", token "->"] rest
  let rest ← takeSameLength n rest
  let rest ← expect (token "{") rest
  let (bodyLeft, rest) ← takeIdent rest
  let bodyLeftSecond ← resolve bodyLeft paramFirst paramSecond
  let (op, rest) ← takeOp rest
  let (bodyRight, rest) ← takeIdent rest
  let bodyRightSecond ← resolve bodyRight paramFirst paramSecond
  let rest ← expect (token "}") rest
  let rest ← expectMany [token "circuit"] rest
  let (circuitName, rest) ← takeIdent rest
  if helperName == circuitName then none else
  let rest ← expectMany [token "(", token "private"] rest
  let (firstInput, rest) ← takeIdent rest
  let rest ← expect (token ":") rest
  let rest ← takeSameLength n rest
  let rest ← expectMany [token ",", token "private"] rest
  let (secondInput, rest) ← takeIdent rest
  if hSame : firstInput = secondInput then none else
  let rest ← expect (token ":") rest
  let rest ← takeSameLength n rest
  let rest ← expectMany [token ")", token "->", token "public"] rest
  let rest ← takeSameLength n rest
  let rest ← expectMany [token "{", token "let"] rest
  let (outputName, rest) ← takeIdent rest
  if outputName == firstInput || outputName == secondInput then none else
  let rest ← expect (token "=") rest
  let rest ← expect helperName rest
  let rest ← expect (token "(") rest
  let (callFirst, rest) ← takeIdent rest
  let callFirstSecond ← resolve callFirst firstInput secondInput
  let rest ← expect (token ",") rest
  let (callSecond, rest) ← takeIdent rest
  let callSecondSecond ← resolve callSecond firstInput secondInput
  let rest ← expectMany [token ")", token ";", outputName, token "}"] rest
  if !rest.isEmpty then none else
  return Parsed.mk n helperName circuitName firstInput secondInput outputName
    op bodyLeftSecond bodyRightSecond callFirstSecond callSecondSecond hSame

/-- Resolve both levels of static function application to the names in the
normalized circuit relation. Only source identifiers enter JSON strings. -/
def Parsed.leftName (p : Parsed) : Token :=
  choose p.bodyLeftSecond
    (choose p.callFirstSecond p.firstInput p.secondInput)
    (choose p.callSecondSecond p.firstInput p.secondInput)

def Parsed.rightName (p : Parsed) : Token :=
  choose p.bodyRightSecond
    (choose p.callFirstSecond p.firstInput p.secondInput)
    (choose p.callSecondSecond p.firstInput p.secondInput)

/-- Interpret one resolved normalized-relation input name in the circuit's
private input environment. Distinct source input names make this unambiguous. -/
def Parsed.readName (p : Parsed) (a b : Fin p.length → S31.M31)
    (name : Token) : Fin p.length → S31.M31 :=
  if name = p.firstInput then a else b

theorem Parsed.readName_choose (p : Parsed)
    (a b : Fin p.length → S31.M31) (second : Bool) :
    p.readName a b (choose second p.firstInput p.secondInput) =
      choose second a b := by
  cases second <;>
    simp [Parsed.readName, choose, p.inputNamesDistinct.symm]

theorem Parsed.leftName_denotes (p : Parsed)
    (a b : Fin p.length → S31.M31) :
    p.readName a b p.leftName = p.left a b := by
  cases h : p.bodyLeftSecond with
  | false =>
      simpa [Parsed.leftName, Parsed.left, choose, h] using
        (p.readName_choose a b p.callFirstSecond)
  | true =>
      simpa [Parsed.leftName, Parsed.left, choose, h] using
        (p.readName_choose a b p.callSecondSecond)

theorem Parsed.rightName_denotes (p : Parsed)
    (a b : Fin p.length → S31.M31) :
    p.readName a b p.rightName = p.right a b := by
  cases h : p.bodyRightSecond with
  | false =>
      simpa [Parsed.rightName, Parsed.right, choose, h] using
        (p.readName_choose a b p.callFirstSecond)
  | true =>
      simpa [Parsed.rightName, Parsed.right, choose, h] using
        (p.readName_choose a b p.callSecondSecond)

/-- The denotation of the names emitted in canonical normalized JSON. -/
def Parsed.relationValue (p : Parsed) (a b : Fin p.length → S31.M31) :
    Fin p.length → S31.M31 :=
  fun i => p.op.eval (p.readName a b p.leftName i)
    (p.readName a b p.rightName i)

theorem Parsed.relationValue_eq_value (p : Parsed)
    (a b : Fin p.length → S31.M31) :
    p.relationValue a b = p.value a b := by
  funext i
  simp [Parsed.relationValue, Parsed.value,
    p.leftName_denotes a b, p.rightName_denotes a b]

def Op.name : Op → Token
  | .add => token "add"
  | .sub => token "sub"
  | .mul => token "mul"

/-- Exact canonical JSON bytes of one private M31 array input. The source
grammar accepts only ASCII identifiers, so no JSON escapes are needed. -/
def encodeInput (name : Token) (length : Nat) : Token :=
  token "    {\n      \"kind\": \"m31\",\n      \"length\": " ++
  token (toString length) ++
  token ",\n      \"name\": \"" ++ name ++
  token "\",\n      \"visibility\": \"private\"\n    }"

/-- Exact canonical JSON bytes of the single resolved arithmetic node. -/
def encodeNode (p : Parsed) : Token :=
  token "    {\n      \"lhs\": \"" ++ p.leftName ++
  token "\",\n      \"name\": \"" ++ p.outputName ++
  token "\",\n      \"op\": \"" ++ p.op.name ++
  token "\",\n      \"rhs\": \"" ++ p.rightName ++
  token "\"\n    }"

/-- Byte-for-byte canonical v1 relation produced by this source fragment.
Its public ABI is one M31 array output and no public inputs. -/
def encodeNormalized (p : Parsed) : Token :=
  token "{\n  \"assertions\": [],\n  \"inputs\": [\n" ++
  encodeInput p.firstInput p.length ++ token ",\n" ++
  encodeInput p.secondInput p.length ++
  token "\n  ],\n  \"name\": \"" ++ p.circuitName ++
  token "\",\n  \"nodes\": [\n" ++ encodeNode p ++
  token "\n  ],\n  \"public_outputs\": [\n    \"" ++ p.outputName ++
  token "\"\n  ],\n  \"version\": 1\n}\n"

/-- Admit actual source and normalized bytes only when the Lean parser
reconstructs their exact relation. This is a source/relation audit, not a
native proof verifier or a certificate for compiler optimizations. -/
def checkRelation (source normalized : List Nat) : Option Parsed := do
  let p ← parseBytes source
  if encodeNormalized p = normalized then some p else none

theorem checked_relation_bytes (source normalized : List Nat) (p : Parsed)
    (h : checkRelation source normalized = some p) :
    parseBytes source = some p ∧ encodeNormalized p = normalized := by
  unfold checkRelation at h
  cases hs : parseBytes source with
  | none => simp [hs] at h
  | some q =>
      by_cases he : encodeNormalized q = normalized
      · simp [hs, he] at h
        subst p
        exact ⟨rfl, he⟩
      · simp [hs, he] at h

def denotation (bytes : List Nat) : Option Parsed := parseBytes bytes

/-- Successful parsing binds actual source bytes to the row relation. -/
theorem parsed_bytes_air_iff (bytes : List Nat) (p : Parsed)
    (hparse : parseBytes bytes = some p)
    (a b claimed : Fin p.length → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) :
    p.air a b claimed tailA tailB ↔
      denotation bytes = some p ∧ claimed = p.value a b := by
  simp [denotation, hparse, air_iff_value]

/-- An accepted source/relation byte pair and every satisfying packed AIR
row agree on the public M31 result for any concrete private inputs. -/
theorem checked_relation_air_iff (source normalized : List Nat) (p : Parsed)
    (h : checkRelation source normalized = some p)
    (a b claimed : Fin p.length → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) :
    p.air a b claimed tailA tailB ↔
      denotation source = some p ∧ encodeNormalized p = normalized ∧
        claimed = p.relationValue a b := by
  obtain ⟨hs, he⟩ := checked_relation_bytes source normalized p h
  simp [denotation, hs, he, air_iff_value, p.relationValue_eq_value a b]

/-- The exact functional source used by the native five-lane subtraction
acceptance gate. This literal is checked here independently of Python. -/
def subtract5Source : String :=
  "fn difference(x: [m31; 5], y: [m31; 5]) -> [m31; 5] { x - y }\n" ++
  "circuit subtract5(private a: [m31; 5], private b: [m31; 5]) -> public [m31; 5] {\n" ++
  "    let out = difference(a, b);\n    out\n}\n"

def subtract5Parsed : Parsed :=
  { length := 5, helperName := token "difference",
    circuitName := token "subtract5", firstInput := token "a",
    secondInput := token "b", outputName := token "out", op := .sub,
    bodyLeftSecond := false, bodyRightSecond := true,
    callFirstSecond := false, callSecondSecond := true,
    inputNamesDistinct := by decide }

set_option maxRecDepth 8192
theorem subtract5_actual_bytes :
    parseBytes (token subtract5Source) = some subtract5Parsed := by decide

/-- Reversing the helper operands changes the resolved parser certificate. -/
def subtract5ReversedSource : String :=
  "fn difference(x: [m31; 5], y: [m31; 5]) -> [m31; 5] { y - x }\n" ++
  "circuit subtract5(private a: [m31; 5], private b: [m31; 5]) -> public [m31; 5] {\n" ++
  "    let out = difference(a, b);\n    out\n}\n"

theorem subtract5_reverse_changes_certificate :
    (parseBytes (token subtract5ReversedSource)).map
      Parsed.bodyLeftSecond = some true := by decide

/-- A mismatched input length is rejected before AIR interpretation. -/
def subtract5MismatchedSource : String :=
  "fn difference(x: [m31; 5], y: [m31; 5]) -> [m31; 5] { x - y }\n" ++
  "circuit subtract5(private a: [m31; 5], private b: [m31; 4]) -> public [m31; 5] {\n" ++
  "    let out = difference(a, b);\n    out\n}\n"

theorem subtract5_mismatched_length_rejected :
    parseBytes (token subtract5MismatchedSource) = none := by decide

theorem subtract5_air_iff (a b claimed : Fin 5 → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) :
    subtract5Parsed.air a b claimed tailA tailB ↔
      ∀ i : Fin 5, claimed i = a i - b i := by
  simpa [subtract5Parsed, Parsed.air, Parsed.left, Parsed.right, choose,
    Op.packed, Op.eval] using
      (packed_iff_eval Op.sub a b claimed tailA tailB)

end S31.Functional.Correspondence.SourceFunctionBytes
