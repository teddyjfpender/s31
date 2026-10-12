import S31.Gadgets.Functional.SSANormalizedBytes

/-!
An independently executable byte checker for the zero-cost alias fragment of
the direct-gate source language. A source `let a = x;` adds a lexical binding
to an existing producer; it emits no normalized node, gate, or AIR row.
Redundant parentheses around a reference or a whole binary expression are
also erased. This module deliberately leaves the original `SSATextBytes`
parser intact because several existing row-count theorems assume each of its
lets emits exactly one arithmetic instruction.

The denotation here is determined by these parsed source bytes. The theorem
does not prove that the production Python parser implements this grammar, or
that the native verifier checks this Lean result. The package checker tests
those implementation boundaries separately for the admitted fragment.
-/

namespace S31.Functional.SSAAliasTextBytes

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes

/-- Match the source-level reserved words used by the independent package
checker. The older direct-only byte parser has a smaller reserved set. -/
def isAliasName (name : Token) : Bool :=
  isName name &&
    !(List.contains
      ([token "use", token "in", token "if", token "then", token "else",
        token "fun", token "Fn", token "fn", token "struct", token "blinded",
        token "private", token "assert_eq"]) name)

/-- Names reserved as built-in circuit entry points by the independent
package checker. This list deliberately mirrors its reviewed plain-name
inventory; a differential test checks that inventory against production. -/
def isPlainBuiltinCircuitName (name : Token) : Bool :=
  List.contains
    ([token "accumulate_chainwork", token "blake2s_leaf", token "blake2s_pair",
      token "block_work", token "chainwork_from_work", token "chainwork_u256",
      token "genesis_hash_mainnet", token "header_bits", token "header_time",
      token "is_zero", token "iterate", token "lt_u32", token "m31_from_u16",
      token "merkle_path_blake2s", token "merkle_path_poseidon2",
      token "poseidon2_leaf", token "poseidon2_pair", token "pow_valid",
      token "prev_hash", token "select", token "sha256d_header", token "splat",
      token "target_mainnet", token "target_u256", token "work_u256"]) name

def takeAliasName : List Token → Option (Token × List Token)
  | name :: rest => if isAliasName name then some (name, rest) else none
  | [] => none

def findBinding (wanted : Token) : List (Token × Nat) → Option Nat
  | [] => none
  | (name, id) :: rest => if name == wanted then some id else findBinding wanted rest

def takeUntil (delimiter : Token) : List Token → Option (List Token × List Token)
  | [] => none
  | head :: tail =>
      if head == delimiter then some ([], tail)
      else do
        let (front, rest) ← takeUntil delimiter tail
        pure (head :: front, rest)

/-- Accept only an identifier wrapped in any number of balanced, redundant
parentheses. Fuel is bounded by the token count. -/
def referenceFuel : Nat → List Token → Option Token
  | 0, _ => none
  | _ + 1, [name] => if isAliasName name then some name else none
  | fuel + 1, openToken :: rest =>
      if openToken != token "(" then none
      else match rest.reverse with
        | closeToken :: insideRev =>
            if closeToken == token ")" then
              referenceFuel fuel insideRev.reverse
            else none
        | [] => none
  | _ + 1, [] => none

def reference (tokens : List Token) : Option Token :=
  referenceFuel (tokens.length + 1) tokens

/-- The first opening parenthesis closes only at the end of the token list. -/
def wholeParentheses : List Token → Bool
  | [] => false
  | first :: rest =>
      if first != token "(" then false else go 1 rest
where
  go (depth : Nat) : List Token → Bool
    | [] => false
    | head :: tail =>
        let nextDepth := if head == token "(" then depth + 1
          else if head == token ")" then depth - 1 else depth
        if nextDepth == 0 then tail.isEmpty else go nextDepth tail

def stripOuterFuel : Nat → List Token → List Token
  | 0, tokens => tokens
  | fuel + 1, tokens =>
      if wholeParentheses tokens then
        stripOuterFuel fuel (tokens.drop 1).dropLast
      else tokens

def stripOuter (tokens : List Token) : List Token :=
  stripOuterFuel (tokens.length + 1) tokens

/-- Find a single top-level arithmetic operation. Extra operations are
rejected because each side must subsequently parse as one reference. -/
def splitTop : List Token → Nat → List Token →
    Option (List Token × Bool × List Token)
  | [], _, _ => none
  | head :: rest, depth, leftRev =>
      if head == token "(" then splitTop rest (depth + 1) (head :: leftRev)
      else if head == token ")" then
        if depth == 0 then none else splitTop rest (depth - 1) (head :: leftRev)
      else if depth == 0 && (head == token "+" || head == token ".*") then
        some (leftRev.reverse, head == token ".*", rest)
      else splitTop rest depth (head :: leftRev)

inductive Rhs where
  | alias (name : Token)
  | arithmetic (multiply : Bool) (left right : Token)

def parseRhs (tokens : List Token) : Option Rhs := do
  let plain := stripOuter tokens
  if let some name := reference plain then
    return .alias name
  let (left, multiply, right) ← splitTop plain 0 []
  let lhs ← reference left
  let rhs ← reference right
  return .arithmetic multiply lhs rhs

structure State where
  remaining : List Token
  producerNames : List Token
  bindings : List (Token × Nat)
  expressions : List (Bool × Nat × Nat)
  instructions : List Instruction

def parseLet (state : State) : Option State := do
  let rest ← expect (token "let") state.remaining
  let (name, rest) ← takeAliasName rest
  if (findBinding name state.bindings).isSome then none else
  let rest ← expect (token "=") rest
  let (rhsTokens, rest) ← takeUntil (token ";") rest
  let rhs ← parseRhs rhsTokens
  match rhs with
  | .alias referenced =>
      let id ← findBinding referenced state.bindings
      return { state with
        remaining := rest,
        bindings := state.bindings ++ [(name, id)] }
  | .arithmetic multiply left right =>
      let lhs ← findBinding left state.bindings
      let rhs ← findBinding right state.bindings
      if lhs > rhs || state.instructions.length >= 16 || name.length > 128 then none else
      let expression := (multiply, lhs, rhs)
      if state.expressions.contains expression then none else
      let id := state.producerNames.length
      let instruction : Instruction := { id, lhs, rhs, multiply }
      return {
        remaining := rest,
        producerNames := state.producerNames ++ [name],
        bindings := state.bindings ++ [(name, id)],
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

def outputReference (tokens : List Token) : Option Token :=
  let stripped := match tokens.reverse with
    | last :: rest => if last == token ";" then rest.reverse else tokens
    | [] => tokens
  reference stripped

def parseAliasBytes (bytes : List Nat) : Option Parsed := do
  if bytes.length > 16384 then none else
  let tokens ← lex bytes
  if tokens.length > 256 then none else
  let rest ← expect (token "circuit") tokens
  let (circuitName, rest) ← takeAliasName rest
  if isPlainBuiltinCircuitName circuitName then none else
  let rest ← expectMany [token "(", token "public"] rest
  let (inputName, rest) ← takeAliasName rest
  if inputName.length > 128 then none else
  let rest ← expectMany [token ":", token "[", token "m31", token ";",
                          token "4", token "]", token ")", token "->",
                          token "public", token "[", token "m31", token ";",
                          token "4", token "]", token "{"] rest
  let state ← parseLetsFuel 256 {
    remaining := rest,
    producerNames := [inputName],
    bindings := [(inputName, 0)],
    expressions := [],
    instructions := [] }
  if state.instructions.isEmpty then none else
  let (outputTokens, rest) ← takeUntil (token "}") state.remaining
  if !rest.isEmpty then none else
  let sourceOutput ← outputReference outputTokens
  let output ← findBinding sourceOutput state.bindings
  if output == 0 then none else
  let outputName ← state.producerNames[output]?
  let certificate : Certificate := { instructions := state.instructions, output }
  match h : termFor certificate with
  | none => none
  | some meaning => some {
      circuitName, inputName, outputName,
      wireNames := state.producerNames,
      certificate, meaning, checked := h }

def denotation (bytes : List Nat) (input : Lanes) : Option Lanes :=
  (parseAliasBytes bytes).map (fun parsed => parsed.meaning.eval input)

theorem parsed_alias_bytes_normalized_sound (bytes : List Nat) (input : Lanes)
    (parsed : Parsed) (hparse : parseAliasBytes bytes = some parsed) :
    executeNormalized parsed.certificate input = denotation bytes input := by
  rw [termFor_sound parsed.certificate parsed.meaning input parsed.checked]
  simp [denotation, hparse]

/-- Check source and normalized JSON bytes against one producer-only SSA.
Aliases and parentheses are absent from the encoded relation. -/
def checkAliasRelation (sourceBytes normalizedBytes : List Nat) : Option Certificate := do
  let parsed ← parseAliasBytes sourceBytes
  let expected ← SSANormalizedBytes.encodeNormalized parsed
  if expected != normalizedBytes then none else some parsed.certificate

theorem checked_alias_relation_sound (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkAliasRelation sourceBytes normalizedBytes = some certificate) :
    executeNormalized certificate input = denotation sourceBytes input := by
  unfold checkAliasRelation at hcheck
  cases hsource : parseAliasBytes sourceBytes with
  | none => simp [hsource] at hcheck
  | some parsed =>
      cases hencoded : SSANormalizedBytes.encodeNormalized parsed with
      | none => simp [hsource, hencoded] at hcheck
      | some expected =>
          by_cases hmatch : expected = normalizedBytes
          · have hcertificate : parsed.certificate = certificate := by
              simpa [hsource, hencoded, hmatch] using hcheck
            subst certificate
            exact parsed_alias_bytes_normalized_sound sourceBytes input parsed hsource
          · simp [hsource, hencoded, hmatch] at hcheck

/-! These concrete byte strings exercise both erasures. The first has three
alias bindings and redundant parentheses; the second spells the same two
arithmetic producers directly. Exact normalized JSON equality includes the
producer names and the public output name, not just evaluated values. -/

def aliasSquareSource : Token := token
  "circuit square4(public x: [m31; 4]) -> public [m31; 4] { let base = (x); let once = ((base) .* (base)); let saved = (once); let result = ((saved) .* (saved)); let returned = (result); (returned); }"

def directSquareSource : Token := token
  "circuit square4(public x: [m31; 4]) -> public [m31; 4] { let once = x .* x; let result = once .* once; result }"

set_option maxRecDepth 2048 in
theorem alias_square_certificate_matches_direct :
    (parseAliasBytes aliasSquareSource).map
      (fun parsed => (parsed.certificate, parsed.wireNames, parsed.outputName)) =
    (parseBytes directSquareSource).map
      (fun parsed => (parsed.certificate, parsed.wireNames, parsed.outputName)) := by
  decide

set_option maxRecDepth 2048 in
theorem alias_square_normalized_bytes_match_direct :
    (parseAliasBytes aliasSquareSource).bind SSANormalizedBytes.encodeNormalized =
    (parseBytes directSquareSource).bind SSANormalizedBytes.encodeNormalized := by
  decide

theorem forward_alias_rejected :
    (parseAliasBytes (token
      "circuit square4(public x: [m31; 4]) -> public [m31; 4] { let alias = later; let later = x .* x; later }")).map
      Parsed.certificate = none := by
  decide

end S31.Functional.SSAAliasTextBytes
